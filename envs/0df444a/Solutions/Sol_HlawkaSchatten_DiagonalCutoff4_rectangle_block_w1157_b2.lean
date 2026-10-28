-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1157_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:38:38.193284+00:00
-- url     : https://prove2.me/submissions/4a465052-6c01-4197-a7ee-4180589e0562

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1157_s6_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159705309/10000000000 : ℝ)*x 0 + (2696540573/5000000000 : ℝ)*x 1 + (2632839171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159705309/10000000000 : ℝ)^4175 ≤ (820292171941/6250000000000 : ℝ)^3151 := by
    have hnat : (2159705309 : ℕ)^4175*6250000000000^3151 ≤ 820292171941^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159705309 10000000000 820292171941 6250000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696540573/5000000000 : ℝ)^4175 ≤ (4412557198129/10000000000000 : ℝ)^3151 := by
    have hnat : (2696540573 : ℕ)^4175*10000000000000^3151 ≤ 4412557198129^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696540573 5000000000 4412557198129 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632839171/5000000000 : ℝ)^4175 ≤ (21374876626677/50000000000000 : ℝ)^3151 := by
    have hnat : (2632839171 : ℕ)^4175*50000000000000^3151 ≤ 21374876626677^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632839171 5000000000 21374876626677 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159705309/10000000000 : ℝ), (2696540573/5000000000 : ℝ), (2632839171/5000000000 : ℝ)] ![(820292171941/6250000000000 : ℝ), (4412557198129/10000000000000 : ℝ), (21374876626677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159705309/10000000000 : ℝ)|^4175 ≤ (820292171941/6250000000000 : ℝ)^3151
        have hw : |(-2159705309/10000000000 : ℝ)|=(2159705309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696540573/5000000000 : ℝ)|^4175 ≤ (4412557198129/10000000000000 : ℝ)^3151
        have hw : |(2696540573/5000000000 : ℝ)|=(2696540573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632839171/5000000000 : ℝ)|^4175 ≤ (21374876626677/50000000000000 : ℝ)^3151
        have hw : |(2632839171/5000000000 : ℝ)|=(2632839171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s6_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672390553/5000000000 : ℝ)*x 0 + (-2224327267/10000000000 : ℝ)*x 1 + (2632839203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672390553/5000000000 : ℝ)^4175 ≤ (4360272425873/10000000000000 : ℝ)^3151 := by
    have hnat : (2672390553 : ℕ)^4175*10000000000000^3151 ≤ 4360272425873^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672390553 5000000000 4360272425873 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224327267/10000000000 : ℝ)^4175 ≤ (1364752179371/10000000000000 : ℝ)^3151 := by
    have hnat : (2224327267 : ℕ)^4175*10000000000000^3151 ≤ 1364752179371^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224327267 10000000000 1364752179371 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632839203/5000000000 : ℝ)^4175 ≤ (10687438485449/25000000000000 : ℝ)^3151 := by
    have hnat : (2632839203 : ℕ)^4175*25000000000000^3151 ≤ 10687438485449^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632839203 5000000000 10687438485449 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672390553/5000000000 : ℝ), (-2224327267/10000000000 : ℝ), (2632839203/5000000000 : ℝ)] ![(4360272425873/10000000000000 : ℝ), (1364752179371/10000000000000 : ℝ), (10687438485449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672390553/5000000000 : ℝ)|^4175 ≤ (4360272425873/10000000000000 : ℝ)^3151
        have hw : |(2672390553/5000000000 : ℝ)|=(2672390553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224327267/10000000000 : ℝ)|^4175 ≤ (1364752179371/10000000000000 : ℝ)^3151
        have hw : |(-2224327267/10000000000 : ℝ)|=(2224327267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632839203/5000000000 : ℝ)|^4175 ≤ (10687438485449/25000000000000 : ℝ)^3151
        have hw : |(2632839203/5000000000 : ℝ)|=(2632839203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s6_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267239073/500000000 : ℝ)*x 0 + (5265678151/10000000000 : ℝ)*x 1 + (-556081783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267239073/500000000 : ℝ)^4175 ≤ (43602728085171/100000000000000 : ℝ)^3151 := by
    have hnat : (267239073 : ℕ)^4175*100000000000000^3151 ≤ 43602728085171^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267239073 500000000 43602728085171 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265678151/10000000000 : ℝ)^4175 ≤ (8549950239757/20000000000000 : ℝ)^3151 := by
    have hnat : (5265678151 : ℕ)^4175*20000000000000^3151 ≤ 8549950239757^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265678151 10000000000 8549950239757 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556081783/2500000000 : ℝ)^4175 ≤ (13647520696229/100000000000000 : ℝ)^3151 := by
    have hnat : (556081783 : ℕ)^4175*100000000000000^3151 ≤ 13647520696229^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556081783 2500000000 13647520696229 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267239073/500000000 : ℝ), (5265678151/10000000000 : ℝ), (-556081783/2500000000 : ℝ)] ![(43602728085171/100000000000000 : ℝ), (8549950239757/20000000000000 : ℝ), (13647520696229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267239073/500000000 : ℝ)|^4175 ≤ (43602728085171/100000000000000 : ℝ)^3151
        have hw : |(267239073/500000000 : ℝ)|=(267239073/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265678151/10000000000 : ℝ)|^4175 ≤ (8549950239757/20000000000000 : ℝ)^3151
        have hw : |(5265678151/10000000000 : ℝ)|=(5265678151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556081783/2500000000 : ℝ)|^4175 ≤ (13647520696229/100000000000000 : ℝ)^3151
        have hw : |(-556081783/2500000000 : ℝ)|=(556081783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s6_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272659309/625000000 : ℝ)*x 0 + (66207481/156250000 : ℝ)*x 1 + (449148989/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272659309/625000000 : ℝ)^4175 ≤ (104115289369/312500000000 : ℝ)^3151 := by
    have hnat : (272659309 : ℕ)^4175*312500000000^3151 ≤ 104115289369^3151*625000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272659309 625000000 104115289369 312500000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66207481/156250000 : ℝ)^4175 ≤ (641105049943/2000000000000 : ℝ)^3151 := by
    have hnat : (66207481 : ℕ)^4175*2000000000000^3151 ≤ 641105049943^3151*156250000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66207481 156250000 641105049943 2000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449148989/1000000000 : ℝ)^4175 ≤ (54106023257/156250000000 : ℝ)^3151 := by
    have hnat : (449148989 : ℕ)^4175*156250000000^3151 ≤ 54106023257^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449148989 1000000000 54106023257 156250000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272659309/625000000 : ℝ), (66207481/156250000 : ℝ), (449148989/1000000000 : ℝ)] ![(104115289369/312500000000 : ℝ), (641105049943/2000000000000 : ℝ), (54106023257/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272659309/625000000 : ℝ)|^4175 ≤ (104115289369/312500000000 : ℝ)^3151
        have hw : |(272659309/625000000 : ℝ)|=(272659309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66207481/156250000 : ℝ)|^4175 ≤ (641105049943/2000000000000 : ℝ)^3151
        have hw : |(66207481/156250000 : ℝ)|=(66207481/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449148989/1000000000 : ℝ)|^4175 ≤ (54106023257/156250000000 : ℝ)^3151
        have hw : |(449148989/1000000000 : ℝ)|=(449148989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s6_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159710373/10000000000 : ℝ)*x 0 + (2633000001/5000000000 : ℝ)*x 1 + (5392758207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159710373/10000000000 : ℝ)^4175 ≤ (6562357763123/50000000000000 : ℝ)^3151 := by
    have hnat : (2159710373 : ℕ)^4175*50000000000000^3151 ≤ 6562357763123^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159710373 10000000000 6562357763123 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633000001/5000000000 : ℝ)^4175 ≤ (8550642670799/20000000000000 : ℝ)^3151 := by
    have hnat : (2633000001 : ℕ)^4175*20000000000000^3151 ≤ 8550642670799^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633000001 5000000000 8550642670799 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392758207/10000000000 : ℝ)^4175 ≤ (22061035548567/50000000000000 : ℝ)^3151 := by
    have hnat : (5392758207 : ℕ)^4175*50000000000000^3151 ≤ 22061035548567^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392758207 10000000000 22061035548567 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159710373/10000000000 : ℝ), (2633000001/5000000000 : ℝ), (5392758207/10000000000 : ℝ)] ![(6562357763123/50000000000000 : ℝ), (8550642670799/20000000000000 : ℝ), (22061035548567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159710373/10000000000 : ℝ)|^4175 ≤ (6562357763123/50000000000000 : ℝ)^3151
        have hw : |(-2159710373/10000000000 : ℝ)|=(2159710373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633000001/5000000000 : ℝ)|^4175 ≤ (8550642670799/20000000000000 : ℝ)^3151
        have hw : |(2633000001/5000000000 : ℝ)|=(2633000001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392758207/10000000000 : ℝ)|^4175 ≤ (22061035548567/50000000000000 : ℝ)^3151
        have hw : |(5392758207/10000000000 : ℝ)|=(5392758207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s6_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312467661/10000000000 : ℝ)*x 0 + (-1048623561/5000000000 : ℝ)*x 1 + (1078551641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312467661/10000000000 : ℝ)^4175 ≤ (43253786787597/100000000000000 : ℝ)^3151 := by
    have hnat : (5312467661 : ℕ)^4175*100000000000000^3151 ≤ 43253786787597^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312467661 10000000000 43253786787597 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048623561/5000000000 : ℝ)^4175 ≤ (12624142131259/100000000000000 : ℝ)^3151 := by
    have hnat : (1048623561 : ℕ)^4175*100000000000000^3151 ≤ 12624142131259^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048623561 5000000000 12624142131259 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078551641/2000000000 : ℝ)^4175 ≤ (44122071075453/100000000000000 : ℝ)^3151 := by
    have hnat : (1078551641 : ℕ)^4175*100000000000000^3151 ≤ 44122071075453^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078551641 2000000000 44122071075453 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312467661/10000000000 : ℝ), (-1048623561/5000000000 : ℝ), (1078551641/2000000000 : ℝ)] ![(43253786787597/100000000000000 : ℝ), (12624142131259/100000000000000 : ℝ), (44122071075453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312467661/10000000000 : ℝ)|^4175 ≤ (43253786787597/100000000000000 : ℝ)^3151
        have hw : |(5312467661/10000000000 : ℝ)|=(5312467661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048623561/5000000000 : ℝ)|^4175 ≤ (12624142131259/100000000000000 : ℝ)^3151
        have hw : |(-1048623561/5000000000 : ℝ)|=(1048623561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078551641/2000000000 : ℝ)|^4175 ≤ (44122071075453/100000000000000 : ℝ)^3151
        have hw : |(1078551641/2000000000 : ℝ)|=(1078551641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s6_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312467659/10000000000 : ℝ)*x 0 + (2696379099/5000000000 : ℝ)*x 1 + (-2097247133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312467659/10000000000 : ℝ)^4175 ≤ (21626893383011/50000000000000 : ℝ)^3151 := by
    have hnat : (5312467659 : ℕ)^4175*50000000000000^3151 ≤ 21626893383011^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312467659 10000000000 21626893383011 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696379099/5000000000 : ℝ)^4175 ≤ (44122070999569/100000000000000 : ℝ)^3151 := by
    have hnat : (2696379099 : ℕ)^4175*100000000000000^3151 ≤ 44122070999569^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696379099 5000000000 44122070999569 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097247133/10000000000 : ℝ)^4175 ≤ (1262414221899/10000000000000 : ℝ)^3151 := by
    have hnat : (2097247133 : ℕ)^4175*10000000000000^3151 ≤ 1262414221899^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097247133 10000000000 1262414221899 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312467659/10000000000 : ℝ), (2696379099/5000000000 : ℝ), (-2097247133/10000000000 : ℝ)] ![(21626893383011/50000000000000 : ℝ), (44122070999569/100000000000000 : ℝ), (1262414221899/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312467659/10000000000 : ℝ)|^4175 ≤ (21626893383011/50000000000000 : ℝ)^3151
        have hw : |(5312467659/10000000000 : ℝ)|=(5312467659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696379099/5000000000 : ℝ)|^4175 ≤ (44122070999569/100000000000000 : ℝ)^3151
        have hw : |(2696379099/5000000000 : ℝ)|=(2696379099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097247133/10000000000 : ℝ)|^4175 ≤ (1262414221899/10000000000000 : ℝ)^3151
        have hw : |(-2097247133/10000000000 : ℝ)|=(2097247133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s6_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2181279149/5000000000 : ℝ)*x 0 + (4490847899/10000000000 : ℝ)*x 1 + (4237923573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181279149/5000000000 : ℝ)^4175 ≤ (1332679490003/4000000000000 : ℝ)^3151 := by
    have hnat : (2181279149 : ℕ)^4175*4000000000000^3151 ≤ 1332679490003^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181279149 5000000000 1332679490003 4000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490847899/10000000000 : ℝ)^4175 ≤ (17310648512611/50000000000000 : ℝ)^3151 := by
    have hnat : (4490847899 : ℕ)^4175*50000000000000^3151 ≤ 17310648512611^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490847899 10000000000 17310648512611 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237923573/10000000000 : ℝ)^4175 ≤ (16030857856037/50000000000000 : ℝ)^3151 := by
    have hnat : (4237923573 : ℕ)^4175*50000000000000^3151 ≤ 16030857856037^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237923573 10000000000 16030857856037 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181279149/5000000000 : ℝ), (4490847899/10000000000 : ℝ), (4237923573/10000000000 : ℝ)] ![(1332679490003/4000000000000 : ℝ), (17310648512611/50000000000000 : ℝ), (16030857856037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181279149/5000000000 : ℝ)|^4175 ≤ (1332679490003/4000000000000 : ℝ)^3151
        have hw : |(2181279149/5000000000 : ℝ)|=(2181279149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490847899/10000000000 : ℝ)|^4175 ≤ (17310648512611/50000000000000 : ℝ)^3151
        have hw : |(4490847899/10000000000 : ℝ)|=(4490847899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237923573/10000000000 : ℝ)|^4175 ≤ (16030857856037/50000000000000 : ℝ)^3151
        have hw : |(4237923573/10000000000 : ℝ)|=(4237923573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5683/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11337/100000 : ℝ) ^ (8349/2048 : ℝ) ≤ (6990049819626101/50000000000000000000 : ℝ) := by
    have hpowers : (11337/100000 : ℝ)^8349 ≤ (6990049819626101/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11337 : ℕ)^8349*50000000000000000000^2048 ≤ 6990049819626101^2048*100000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11337 100000 6990049819626101 50000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11337/100000 : ℝ)) (X := (6990049819626101/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (8349/2048 : ℝ) ≤ (33964679194680317/100000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^8349 ≤ (33964679194680317/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2819 : ℕ)^8349*100000000000000000000^2048 ≤ 33964679194680317^2048*20000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 33964679194680317 100000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (33964679194680317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006990049819626101/25000000000000000000 : ℝ) ≤ (1250085723510991/1250000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (25006990049819626101/25000000000000000000 : ℝ)^2048 ≤ (1250085723510991/1250000000000000 : ℝ)^8349 := by
      have hnat : (25006990049819626101 : ℕ)^2048*1250000000000000^8349 ≤ 1250085723510991^8349*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006990049819626101 25000000000000000000 1250085723510991 1250000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250085723510991/1250000000000000 : ℝ)) (X := (25006990049819626101/25000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047944778833932519/100000000000000000000 : ℝ) ≤ (5000587933568947/5000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (100047944778833932519/100000000000000000000 : ℝ)^2048 ≤ (5000587933568947/5000000000000000 : ℝ)^8349 := by
      have hnat : (100047944778833932519 : ℕ)^2048*5000000000000000^8349 ≤ 5000587933568947^8349*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047944778833932519 100000000000000000000 5000587933568947 5000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000587933568947/5000000000000000 : ℝ)) (X := (100047944778833932519/100000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033964679194680317/50000000000000000000 : ℝ) ≤ (500083297309393/500000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50033964679194680317/50000000000000000000 : ℝ)^2048 ≤ (500083297309393/500000000000000 : ℝ)^8349 := by
      have hnat : (50033964679194680317 : ℕ)^2048*500000000000000^8349 ≤ 500083297309393^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033964679194680317 50000000000000000000 500083297309393 500000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500083297309393/500000000000000 : ℝ)) (X := (50033964679194680317/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6990049819626101/50000000000000000000 : ℝ) ≤ ((1378538967558378817/1379000000000000000 : ℝ)+2*(245039524983/137900000000000 : ℝ)*(11337/100000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (1378538967558378817/1379000000000000000 : ℝ)+2*(245039524983/137900000000000 : ℝ)*(11337/100000 : ℝ)=(1250085723510991/1250000000000000 : ℝ) by norm_num, show 1+2*(6990049819626101/50000000000000000000 : ℝ)=(25006990049819626101/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33964679194680317/100000000000000000000 : ℝ)+(6990049819626101/50000000000000000000 : ℝ) ≤ ((1378538967558378817/1379000000000000000 : ℝ)+(245039524983/137900000000000 : ℝ)*((2819/20000 : ℝ)+(11337/100000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (1378538967558378817/1379000000000000000 : ℝ)+(245039524983/137900000000000 : ℝ)*((2819/20000 : ℝ)+(11337/100000 : ℝ))=(5000587933568947/5000000000000000 : ℝ) by norm_num, show 1+(33964679194680317/100000000000000000000 : ℝ)+(6990049819626101/50000000000000000000 : ℝ)=(100047944778833932519/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33964679194680317/100000000000000000000 : ℝ) ≤ ((1378538967558378817/1379000000000000000 : ℝ)+2*(245039524983/137900000000000 : ℝ)*(2819/20000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (1378538967558378817/1379000000000000000 : ℝ)+2*(245039524983/137900000000000 : ℝ)*(2819/20000 : ℝ)=(500083297309393/500000000000000 : ℝ) by norm_num, show 1+2*(33964679194680317/100000000000000000000 : ℝ)=(50033964679194680317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1378538967558378817/1379000000000000000 : ℝ)*(X 1 0+X 2 0)+(245039524983/137900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1378538967558378817/1379000000000000000 : ℝ)) (alpha := (245039524983/137900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1378538967558378817/1379000000000000000 : ℝ)*(X 0 1+X 2 1)+(245039524983/137900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1378538967558378817/1379000000000000000 : ℝ)) (alpha := (245039524983/137900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1378538967558378817/1379000000000000000 : ℝ)*(X 0 2+X 1 2)+(245039524983/137900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1378538967558378817/1379000000000000000 : ℝ)) (alpha := (245039524983/137900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2159705309/10000000000 : ℝ)*X 0 0+(2696540573/5000000000 : ℝ)*X 0 1+(2632839171/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672390553/5000000000 : ℝ)*X 1 0+(-2224327267/10000000000 : ℝ)*X 1 1+(2632839203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267239073/500000000 : ℝ)*X 2 0+(5265678151/10000000000 : ℝ)*X 2 1+(-556081783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272659309/625000000 : ℝ)*X 0 0+(66207481/156250000 : ℝ)*X 0 1+(449148989/1000000000 : ℝ)*X 0 2+(272659309/625000000 : ℝ)*X 1 0+(66207481/156250000 : ℝ)*X 1 1+(449148989/1000000000 : ℝ)*X 1 2+(272659309/625000000 : ℝ)*X 2 0+(66207481/156250000 : ℝ)*X 2 1+(449148989/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2159710373/10000000000 : ℝ)*X 0 0+(2633000001/5000000000 : ℝ)*X 0 1+(5392758207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312467661/10000000000 : ℝ)*X 1 0+(-1048623561/5000000000 : ℝ)*X 1 1+(1078551641/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312467659/10000000000 : ℝ)*X 2 0+(2696379099/5000000000 : ℝ)*X 2 1+(-2097247133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181279149/5000000000 : ℝ)*X 0 0+(4490847899/10000000000 : ℝ)*X 0 1+(4237923573/10000000000 : ℝ)*X 0 2+(2181279149/5000000000 : ℝ)*X 1 0+(4490847899/10000000000 : ℝ)*X 1 1+(4237923573/10000000000 : ℝ)*X 1 2+(2181279149/5000000000 : ℝ)*X 2 0+(4490847899/10000000000 : ℝ)*X 2 1+(4237923573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (487174348263893841509541/67333984375000000000000000000 : ℝ) := by norm_num
    linear_combination (557435837/50000000000000 : ℝ)*(base19) + (992530349/100000000000000 : ℝ)*(base23) + (6864981/2000000000000 : ℝ)*(lower2) + (421991/156250000000 : ℝ)*(upper3) + (106627623/100000000000000 : ℝ)*(upper5) + (1178292983697363/20000000000000 : ℝ)*(major0) + (1178292983697363/20000000000000 : ℝ)*(major1) + (184108278702713/3125000000000 : ℝ)*(major2) + (7849137493838857/100000000000000 : ℝ)*(sp0) + (7849160613844911/100000000000000 : ℝ)*(sp1) + (1962290184046559/25000000000000 : ℝ)*(sp2) + (1966874170652453/50000000000000 : ℝ)*(sp3) + (24234877727/100000000000000 : ℝ)*(sp4) + (4881444761/25000000000000 : ℝ)*(sp7) + (78675357341679/2000000000000 : ℝ)*(f.failure) + (1569832345743317/20000000000000 : ℝ)*(f.sum) + (13441970223201/1970000000000000000000000000 : ℝ)*base66 + (312145934021335571/27580000000000000000000000000000 : ℝ)*base67 + (132283309913945417/8618750000000000000000000000000 : ℝ)*base69 + (55657898554144429/27580000000000000000000000000000 : ℝ)*base72 + (8265494781729/1970000000000000000000000000 : ℝ)*base73 + (73486186356089167/8618750000000000000000000000000 : ℝ)*base75 + (137589869578630429/27580000000000000000000000000000 : ℝ)*base78 + (83528324596569571/27580000000000000000000000000000 : ℝ)*base79 + (1982562802771/1379000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1628019/200000000000000000000 : ℝ)*base89 + (1628019/200000000000000000000 : ℝ)*base91 + (371981/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8941348773587923483569/985000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26655489/1562500000000 : ℝ)*(base19) + (45778377/2500000000000 : ℝ)*(base23) + (36636677/20000000000000 : ℝ)*(upper3) + (15329139/25000000000000 : ℝ)*(lower4) + (97169511/50000000000000 : ℝ)*(upper5) + (5921392898506379/100000000000000 : ℝ)*(major0) + (5921392898506379/100000000000000 : ℝ)*(major1) + (5921392898506379/100000000000000 : ℝ)*(major2) + (47309786683/100000000000000 : ℝ)*(sp1) + (49402715177/100000000000000 : ℝ)*(sp2) + (7889034528445819/100000000000000 : ℝ)*(sp4) + (7888985512707841/100000000000000 : ℝ)*(sp5) + (7888983294595563/100000000000000 : ℝ)*(sp6) + (1976875482991609/50000000000000 : ℝ)*(sp7) + (1976875482991609/50000000000000 : ℝ)*(f.failure) + (7889034528445819/100000000000000 : ℝ)*(f.sum) + (181766886597/492500000000000000000000000 : ℝ)*base66 + (102122121305791949/19700000000000000000000000000000 : ℝ)*base67 + (135574024913891949/19700000000000000000000000000000 : ℝ)*base69 + (108443188538691949/19700000000000000000000000000000 : ℝ)*base71 + (118649243879/61562500000000000000000000 : ℝ)*base74 + (161757408635108051/19700000000000000000000000000000 : ℝ)*base76 + (40689241979908051/19700000000000000000000000000000 : ℝ)*base78 + (38866475485308051/19700000000000000000000000000000 : ℝ)*base80 + (1215552058571/246250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (22625749/5000000000000000000000 : ℝ)*base89 + (22625749/5000000000000000000000 : ℝ)*base91 + (22625749/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1157_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1157_s7_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107986499/500000000 : ℝ)*x 0 + (539278443/1000000000 : ℝ)*x 1 + (52659589/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107986499/500000000 : ℝ)^4175 ≤ (410152293799/3125000000000 : ℝ)^3151 := by
    have hnat : (107986499 : ℕ)^4175*3125000000000^3151 ≤ 410152293799^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107986499 500000000 410152293799 3125000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539278443/1000000000 : ℝ)^4175 ≤ (8824471074043/20000000000000 : ℝ)^3151 := by
    have hnat : (539278443 : ℕ)^4175*20000000000000^3151 ≤ 8824471074043^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539278443 1000000000 8824471074043 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52659589/100000000 : ℝ)^4175 ≤ (42752771215439/100000000000000 : ℝ)^3151 := by
    have hnat : (52659589 : ℕ)^4175*100000000000000^3151 ≤ 42752771215439^3151*100000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52659589 100000000 42752771215439 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107986499/500000000 : ℝ), (539278443/1000000000 : ℝ), (52659589/100000000 : ℝ)] ![(410152293799/3125000000000 : ℝ), (8824471074043/20000000000000 : ℝ), (42752771215439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107986499/500000000 : ℝ)|^4175 ≤ (410152293799/3125000000000 : ℝ)^3151
        have hw : |(-107986499/500000000 : ℝ)|=(107986499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539278443/1000000000 : ℝ)|^4175 ≤ (8824471074043/20000000000000 : ℝ)^3151
        have hw : |(539278443/1000000000 : ℝ)|=(539278443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52659589/100000000 : ℝ)|^4175 ≤ (42752771215439/100000000000000 : ℝ)^3151
        have hw : |(52659589/100000000 : ℝ)|=(52659589/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s7_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344706989/10000000000 : ℝ)*x 0 + (-2224054633/10000000000 : ℝ)*x 1 + (5265958917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344706989/10000000000 : ℝ)^4175 ≤ (43601923118333/100000000000000 : ℝ)^3151 := by
    have hnat : (5344706989 : ℕ)^4175*100000000000000^3151 ≤ 43601923118333^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344706989 10000000000 43601923118333 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224054633/10000000000 : ℝ)^4175 ≤ (852831591441/6250000000000 : ℝ)^3151 := by
    have hnat : (2224054633 : ℕ)^4175*6250000000000^3151 ≤ 852831591441^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224054633 10000000000 852831591441 6250000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265958917/10000000000 : ℝ)^4175 ≤ (4275277139831/10000000000000 : ℝ)^3151 := by
    have hnat : (5265958917 : ℕ)^4175*10000000000000^3151 ≤ 4275277139831^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265958917 10000000000 4275277139831 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344706989/10000000000 : ℝ), (-2224054633/10000000000 : ℝ), (5265958917/10000000000 : ℝ)] ![(43601923118333/100000000000000 : ℝ), (852831591441/6250000000000 : ℝ), (4275277139831/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344706989/10000000000 : ℝ)|^4175 ≤ (43601923118333/100000000000000 : ℝ)^3151
        have hw : |(5344706989/10000000000 : ℝ)|=(5344706989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224054633/10000000000 : ℝ)|^4175 ≤ (852831591441/6250000000000 : ℝ)^3151
        have hw : |(-2224054633/10000000000 : ℝ)|=(2224054633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265958917/10000000000 : ℝ)|^4175 ≤ (4275277139831/10000000000000 : ℝ)^3151
        have hw : |(5265958917/10000000000 : ℝ)|=(5265958917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s7_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10438881/19531250 : ℝ)*x 0 + (5142538/9765625 : ℝ)*x 1 + (-222405453/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10438881/19531250 : ℝ)^4175 ≤ (43601924015489/100000000000000 : ℝ)^3151 := by
    have hnat : (10438881 : ℕ)^4175*100000000000000^3151 ≤ 43601924015489^3151*19531250^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10438881 19531250 43601924015489 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142538/9765625 : ℝ)^4175 ≤ (10688192836131/25000000000000 : ℝ)^3151 := by
    have hnat : (5142538 : ℕ)^4175*25000000000000^3151 ≤ 10688192836131^3151*9765625^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142538 9765625 10688192836131 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222405453/1000000000 : ℝ)^4175 ≤ (1705663078219/12500000000000 : ℝ)^3151 := by
    have hnat : (222405453 : ℕ)^4175*12500000000000^3151 ≤ 1705663078219^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222405453 1000000000 1705663078219 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10438881/19531250 : ℝ), (5142538/9765625 : ℝ), (-222405453/1000000000 : ℝ)] ![(43601924015489/100000000000000 : ℝ), (10688192836131/25000000000000 : ℝ), (1705663078219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10438881/19531250 : ℝ)|^4175 ≤ (43601924015489/100000000000000 : ℝ)^3151
        have hw : |(10438881/19531250 : ℝ)|=(10438881/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142538/9765625 : ℝ)|^4175 ≤ (10688192836131/25000000000000 : ℝ)^3151
        have hw : |(5142538/9765625 : ℝ)|=(5142538/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222405453/1000000000 : ℝ)|^4175 ≤ (1705663078219/12500000000000 : ℝ)^3151
        have hw : |(-222405453/1000000000 : ℝ)|=(222405453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s7_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362563123/10000000000 : ℝ)*x 0 + (4237853431/10000000000 : ℝ)*x 1 + (4490911951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362563123/10000000000 : ℝ)^4175 ≤ (8329259018423/25000000000000 : ℝ)^3151 := by
    have hnat : (4362563123 : ℕ)^4175*25000000000000^3151 ≤ 8329259018423^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362563123 10000000000 8329259018423 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237853431/10000000000 : ℝ)^4175 ≤ (32061012609493/100000000000000 : ℝ)^3151 := by
    have hnat : (4237853431 : ℕ)^4175*100000000000000^3151 ≤ 32061012609493^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237853431 10000000000 32061012609493 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490911951/10000000000 : ℝ)^4175 ≤ (34621951294859/100000000000000 : ℝ)^3151 := by
    have hnat : (4490911951 : ℕ)^4175*100000000000000^3151 ≤ 34621951294859^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490911951 10000000000 34621951294859 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362563123/10000000000 : ℝ), (4237853431/10000000000 : ℝ), (4490911951/10000000000 : ℝ)] ![(8329259018423/25000000000000 : ℝ), (32061012609493/100000000000000 : ℝ), (34621951294859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362563123/10000000000 : ℝ)|^4175 ≤ (8329259018423/25000000000000 : ℝ)^3151
        have hw : |(4362563123/10000000000 : ℝ)|=(4362563123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237853431/10000000000 : ℝ)|^4175 ≤ (32061012609493/100000000000000 : ℝ)^3151
        have hw : |(4237853431/10000000000 : ℝ)|=(4237853431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490911951/10000000000 : ℝ)|^4175 ≤ (34621951294859/100000000000000 : ℝ)^3151
        have hw : |(4490911951/10000000000 : ℝ)|=(4490911951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s7_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67491713/312500000 : ℝ)*x 0 + (42130223/80000000 : ℝ)*x 1 + (1078492863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67491713/312500000 : ℝ)^4175 ≤ (3281228085263/25000000000000 : ℝ)^3151 := by
    have hnat : (67491713 : ℕ)^4175*25000000000000^3151 ≤ 3281228085263^3151*312500000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67491713 312500000 3281228085263 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42130223/80000000 : ℝ)^4175 ≤ (342049619941/800000000000 : ℝ)^3151 := by
    have hnat : (42130223 : ℕ)^4175*800000000000^3151 ≤ 342049619941^3151*80000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42130223 80000000 342049619941 800000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078492863/2000000000 : ℝ)^4175 ≤ (8823777032389/20000000000000 : ℝ)^3151 := by
    have hnat : (1078492863 : ℕ)^4175*20000000000000^3151 ≤ 8823777032389^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078492863 2000000000 8823777032389 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67491713/312500000 : ℝ), (42130223/80000000 : ℝ), (1078492863/2000000000 : ℝ)] ![(3281228085263/25000000000000 : ℝ), (342049619941/800000000000 : ℝ), (8823777032389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67491713/312500000 : ℝ)|^4175 ≤ (3281228085263/25000000000000 : ℝ)^3151
        have hw : |(-67491713/312500000 : ℝ)|=(67491713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42130223/80000000 : ℝ)|^4175 ≤ (342049619941/800000000000 : ℝ)^3151
        have hw : |(42130223/80000000 : ℝ)|=(42130223/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078492863/2000000000 : ℝ)|^4175 ≤ (8823777032389/20000000000000 : ℝ)^3151
        have hw : |(1078492863/2000000000 : ℝ)|=(1078492863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s7_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656269833/5000000000 : ℝ)*x 0 + (-209754921/1000000000 : ℝ)*x 1 + (1348116073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656269833/5000000000 : ℝ)^4175 ≤ (2162728178513/5000000000000 : ℝ)^3151 := by
    have hnat : (2656269833 : ℕ)^4175*5000000000000^3151 ≤ 2162728178513^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656269833 5000000000 2162728178513 5000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209754921/1000000000 : ℝ)^4175 ≤ (3156637875987/25000000000000 : ℝ)^3151 := by
    have hnat : (209754921 : ℕ)^4175*25000000000000^3151 ≤ 3156637875987^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209754921 1000000000 3156637875987 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348116073/2500000000 : ℝ)^4175 ≤ (8823776982523/20000000000000 : ℝ)^3151 := by
    have hnat : (1348116073 : ℕ)^4175*20000000000000^3151 ≤ 8823776982523^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348116073 2500000000 8823776982523 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656269833/5000000000 : ℝ), (-209754921/1000000000 : ℝ), (1348116073/2500000000 : ℝ)] ![(2162728178513/5000000000000 : ℝ), (3156637875987/25000000000000 : ℝ), (8823776982523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656269833/5000000000 : ℝ)|^4175 ≤ (2162728178513/5000000000000 : ℝ)^3151
        have hw : |(2656269833/5000000000 : ℝ)|=(2656269833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209754921/1000000000 : ℝ)|^4175 ≤ (3156637875987/25000000000000 : ℝ)^3151
        have hw : |(-209754921/1000000000 : ℝ)|=(209754921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348116073/2500000000 : ℝ)|^4175 ≤ (8823776982523/20000000000000 : ℝ)^3151
        have hw : |(1348116073/2500000000 : ℝ)|=(1348116073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s7_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656269831/5000000000 : ℝ)*x 0 + (5392464291/10000000000 : ℝ)*x 1 + (-65548413/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656269831/5000000000 : ℝ)^4175 ≤ (10813640881777/25000000000000 : ℝ)^3151 := by
    have hnat : (2656269831 : ℕ)^4175*25000000000000^3151 ≤ 10813640881777^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656269831 5000000000 10813640881777 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392464291/10000000000 : ℝ)^4175 ≤ (1764755396071/4000000000000 : ℝ)^3151 := by
    have hnat : (5392464291 : ℕ)^4175*4000000000000^3151 ≤ 1764755396071^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392464291 10000000000 1764755396071 4000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65548413/312500000 : ℝ)^4175 ≤ (12626551551803/100000000000000 : ℝ)^3151 := by
    have hnat : (65548413 : ℕ)^4175*100000000000000^3151 ≤ 12626551551803^3151*312500000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65548413 312500000 12626551551803 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656269831/5000000000 : ℝ), (5392464291/10000000000 : ℝ), (-65548413/312500000 : ℝ)] ![(10813640881777/25000000000000 : ℝ), (1764755396071/4000000000000 : ℝ), (12626551551803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656269831/5000000000 : ℝ)|^4175 ≤ (10813640881777/25000000000000 : ℝ)^3151
        have hw : |(2656269831/5000000000 : ℝ)|=(2656269831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392464291/10000000000 : ℝ)|^4175 ≤ (1764755396071/4000000000000 : ℝ)^3151
        have hw : |(5392464291/10000000000 : ℝ)|=(5392464291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65548413/312500000 : ℝ)|^4175 ≤ (12626551551803/100000000000000 : ℝ)^3151
        have hw : |(-65548413/312500000 : ℝ)|=(65548413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s7_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362572841/10000000000 : ℝ)*x 0 + (4490275549/10000000000 : ℝ)*x 1 + (4238492103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362572841/10000000000 : ℝ)^4175 ≤ (4164641801133/12500000000000 : ℝ)^3151 := by
    have hnat : (4362572841 : ℕ)^4175*12500000000000^3151 ≤ 4164641801133^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362572841 10000000000 4164641801133 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490275549/10000000000 : ℝ)^4175 ≤ (34615450797103/100000000000000 : ℝ)^3151 := by
    have hnat : (4490275549 : ℕ)^4175*100000000000000^3151 ≤ 34615450797103^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490275549 10000000000 34615450797103 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238492103/10000000000 : ℝ)^4175 ≤ (32067414789643/100000000000000 : ℝ)^3151 := by
    have hnat : (4238492103 : ℕ)^4175*100000000000000^3151 ≤ 32067414789643^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238492103 10000000000 32067414789643 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362572841/10000000000 : ℝ), (4490275549/10000000000 : ℝ), (4238492103/10000000000 : ℝ)] ![(4164641801133/12500000000000 : ℝ), (34615450797103/100000000000000 : ℝ), (32067414789643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362572841/10000000000 : ℝ)|^4175 ≤ (4164641801133/12500000000000 : ℝ)^3151
        have hw : |(4362572841/10000000000 : ℝ)|=(4362572841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490275549/10000000000 : ℝ)|^4175 ≤ (34615450797103/100000000000000 : ℝ)^3151
        have hw : |(4490275549/10000000000 : ℝ)|=(4490275549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238492103/10000000000 : ℝ)|^4175 ≤ (32067414789643/100000000000000 : ℝ)^3151
        have hw : |(4238492103/10000000000 : ℝ)|=(4238492103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2843/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5683/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5683/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5683/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5683/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5683/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5683/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5683/50000 : ℝ) ^ (8349/2048 : ℝ) ≤ (14126459927605757/100000000000000000000 : ℝ) := by
    have hpowers : (5683/50000 : ℝ)^8349 ≤ (14126459927605757/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5683 : ℕ)^8349*100000000000000000000^2048 ≤ 14126459927605757^2048*50000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5683 50000 14126459927605757 100000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5683/50000 : ℝ)) (X := (14126459927605757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2813/20000 : ℝ) ^ (8349/2048 : ℝ) ≤ (4208867153416569/12500000000000000000 : ℝ) := by
    have hpowers : (2813/20000 : ℝ)^8349 ≤ (4208867153416569/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2813 : ℕ)^8349*12500000000000000000^2048 ≤ 4208867153416569^2048*20000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 20000 4208867153416569 12500000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/20000 : ℝ)) (X := (4208867153416569/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014126459927605757/50000000000000000000 : ℝ) ≤ (10000692966966931/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50014126459927605757/50000000000000000000 : ℝ)^2048 ≤ (10000692966966931/10000000000000000 : ℝ)^8349 := by
      have hnat : (50014126459927605757 : ℕ)^2048*10000000000000000^8349 ≤ 10000692966966931^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014126459927605757 50000000000000000000 10000692966966931 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000692966966931/10000000000000000 : ℝ)) (X := (50014126459927605757/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047797397154938309/100000000000000000000 : ℝ) ≤ (625073265824251/625000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (100047797397154938309/100000000000000000000 : ℝ)^2048 ≤ (625073265824251/625000000000000 : ℝ)^8349 := by
      have hnat : (100047797397154938309 : ℕ)^2048*625000000000000^8349 ≤ 625073265824251^8349*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047797397154938309 100000000000000000000 625073265824251 625000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625073265824251/625000000000000 : ℝ)) (X := (100047797397154938309/100000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254208867153416569/6250000000000000000 : ℝ) ≤ (10001651539409101/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (6254208867153416569/6250000000000000000 : ℝ)^2048 ≤ (10001651539409101/10000000000000000 : ℝ)^8349 := by
      have hnat : (6254208867153416569 : ℕ)^2048*10000000000000000^8349 ≤ 10001651539409101^8349*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254208867153416569 6250000000000000000 10001651539409101 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001651539409101/10000000000000000 : ℝ)) (X := (6254208867153416569/6250000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14126459927605757/100000000000000000000 : ℝ) ≤ ((26980975183466042549/26990000000000000000 : ℝ)+2*(95857244217/53980000000000 : ℝ)*(5683/50000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (26980975183466042549/26990000000000000000 : ℝ)+2*(95857244217/53980000000000 : ℝ)*(5683/50000 : ℝ)=(10000692966966931/10000000000000000 : ℝ) by norm_num, show 1+2*(14126459927605757/100000000000000000000 : ℝ)=(50014126459927605757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4208867153416569/12500000000000000000 : ℝ)+(14126459927605757/100000000000000000000 : ℝ) ≤ ((26980975183466042549/26990000000000000000 : ℝ)+(95857244217/53980000000000 : ℝ)*((2813/20000 : ℝ)+(5683/50000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (26980975183466042549/26990000000000000000 : ℝ)+(95857244217/53980000000000 : ℝ)*((2813/20000 : ℝ)+(5683/50000 : ℝ))=(625073265824251/625000000000000 : ℝ) by norm_num, show 1+(4208867153416569/12500000000000000000 : ℝ)+(14126459927605757/100000000000000000000 : ℝ)=(100047797397154938309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4208867153416569/12500000000000000000 : ℝ) ≤ ((26980975183466042549/26990000000000000000 : ℝ)+2*(95857244217/53980000000000 : ℝ)*(2813/20000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (26980975183466042549/26990000000000000000 : ℝ)+2*(95857244217/53980000000000 : ℝ)*(2813/20000 : ℝ)=(10001651539409101/10000000000000000 : ℝ) by norm_num, show 1+2*(4208867153416569/12500000000000000000 : ℝ)=(6254208867153416569/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26980975183466042549/26990000000000000000 : ℝ)*(X 1 0+X 2 0)+(95857244217/53980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (26980975183466042549/26990000000000000000 : ℝ)) (alpha := (95857244217/53980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26980975183466042549/26990000000000000000 : ℝ)*(X 0 1+X 2 1)+(95857244217/53980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (26980975183466042549/26990000000000000000 : ℝ)) (alpha := (95857244217/53980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26980975183466042549/26990000000000000000 : ℝ)*(X 0 2+X 1 2)+(95857244217/53980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (26980975183466042549/26990000000000000000 : ℝ)) (alpha := (95857244217/53980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107986499/500000000 : ℝ)*X 0 0+(539278443/1000000000 : ℝ)*X 0 1+(52659589/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344706989/10000000000 : ℝ)*X 1 0+(-2224054633/10000000000 : ℝ)*X 1 1+(5265958917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((10438881/19531250 : ℝ)*X 2 0+(5142538/9765625 : ℝ)*X 2 1+(-222405453/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362563123/10000000000 : ℝ)*X 0 0+(4237853431/10000000000 : ℝ)*X 0 1+(4490911951/10000000000 : ℝ)*X 0 2+(4362563123/10000000000 : ℝ)*X 1 0+(4237853431/10000000000 : ℝ)*X 1 1+(4490911951/10000000000 : ℝ)*X 1 2+(4362563123/10000000000 : ℝ)*X 2 0+(4237853431/10000000000 : ℝ)*X 2 1+(4490911951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-67491713/312500000 : ℝ)*X 0 0+(42130223/80000000 : ℝ)*X 0 1+(1078492863/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656269833/5000000000 : ℝ)*X 1 0+(-209754921/1000000000 : ℝ)*X 1 1+(1348116073/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656269831/5000000000 : ℝ)*X 2 0+(5392464291/10000000000 : ℝ)*X 2 1+(-65548413/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362572841/10000000000 : ℝ)*X 0 0+(4490275549/10000000000 : ℝ)*X 0 1+(4238492103/10000000000 : ℝ)*X 0 2+(4362572841/10000000000 : ℝ)*X 1 0+(4490275549/10000000000 : ℝ)*X 1 1+(4238492103/10000000000 : ℝ)*X 1 2+(4362572841/10000000000 : ℝ)*X 2 0+(4490275549/10000000000 : ℝ)*X 2 1+(4238492103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8437174005766524603234158109/1349500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216492703/100000000000000 : ℝ)*(base19) + (1273707039/100000000000000 : ℝ)*(base23) + (17432737/50000000000000 : ℝ)*(lower2) + (43677649/100000000000000 : ℝ)*(upper3) + (184534509/100000000000000 : ℝ)*(upper5) + (5918307940151073/100000000000000 : ℝ)*(major0) + (5918307940151073/100000000000000 : ℝ)*(major1) + (2959153970075537/50000000000000 : ℝ)*(major2) + (3942440710864831/50000000000000 : ℝ)*(sp0) + (3942461667678171/50000000000000 : ℝ)*(sp1) + (3942461639071003/50000000000000 : ℝ)*(sp2) + (1975837005701329/50000000000000 : ℝ)*(sp3) + (43130119383/100000000000000 : ℝ)*(sp4) + (17108647961/100000000000000 : ℝ)*(sp7) + (197584556002531/5000000000000 : ℝ)*(f.failure) + (1576984910369809/20000000000000 : ℝ)*(f.sum) + (27503563865793/5398000000000000000000000000 : ℝ)*base65 + (8033053461392994923/2699000000000000000000000000000000 : ℝ)*base68 + (7032240744810726187/1349500000000000000000000000000000 : ℝ)*base70 + (59745736799308005077/2699000000000000000000000000000000 : ℝ)*base71 + (47627904566099/5398000000000000000000000000 : ℝ)*base74 + (19187446576876226187/1349500000000000000000000000000000 : ℝ)*base76 + (22879695154406494923/2699000000000000000000000000000000 : ℝ)*base78 + (44768337094714494923/2699000000000000000000000000000000 : ℝ)*base80 + (6368903205351/1349500000000000000000000000 : ℝ)*base81 + (9912791/500000000000000000000 : ℝ)*base89 + (9912791/500000000000000000000 : ℝ)*base91 + (4912791/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7620602982117429704121057963/674750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1031716323/50000000000000 : ℝ)*(base19) + (2266875291/100000000000000 : ℝ)*(base23) + (102256911/50000000000000 : ℝ)*(upper3) + (98356529/100000000000000 : ℝ)*(lower4) + (225783631/100000000000000 : ℝ)*(upper5) + (5948223061444629/100000000000000 : ℝ)*(major0) + (5948223061444629/100000000000000 : ℝ)*(major1) + (5948223061444629/100000000000000 : ℝ)*(major2) + (57546419959/100000000000000 : ℝ)*(sp1) + (61554387589/100000000000000 : ℝ)*(sp2) + (7924780113325403/100000000000000 : ℝ)*(sp4) + (3962360251736399/50000000000000 : ℝ)*(sp5) + (1981179073015631/25000000000000 : ℝ)*(sp6) + (198583281654917/5000000000000 : ℝ)*(sp7) + (198583281654917/5000000000000 : ℝ)*(f.failure) + (7924780113325403/100000000000000 : ℝ)*(f.sum) + (1500128493037/539800000000000000000000000 : ℝ)*base65 + (16799934503553019321/2699000000000000000000000000000000 : ℝ)*base67 + (15498878876766980679/2699000000000000000000000000000000 : ℝ)*base70 + (17271527810672980679/2699000000000000000000000000000000 : ℝ)*base72 + (5416109025213/1349500000000000000000000000 : ℝ)*base73 + (10291588797092980679/2699000000000000000000000000000000 : ℝ)*base76 + (36617304971195980679/2699000000000000000000000000000000 : ℝ)*base78 + (42339784354319980679/2699000000000000000000000000000000 : ℝ)*base80 + (17724058861959/2699000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2661263/500000000000000000000 : ℝ)*base90 + (2661263/500000000000000000000 : ℝ)*base92 + (2661263/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1157_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1157_s8_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159734259/10000000000 : ℝ)*x 0 + (2696362489/5000000000 : ℝ)*x 1 + (526601561/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159734259/10000000000 : ℝ)^4175 ≤ (6562453928043/50000000000000 : ℝ)^3151 := by
    have hnat : (2159734259 : ℕ)^4175*50000000000000^3151 ≤ 6562453928043^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159734259 10000000000 6562453928043 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696362489/5000000000 : ℝ)^4175 ≤ (5515213859431/12500000000000 : ℝ)^3151 := by
    have hnat : (2696362489 : ℕ)^4175*12500000000000^3151 ≤ 5515213859431^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696362489 5000000000 5515213859431 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526601561/1000000000 : ℝ)^4175 ≤ (42753381251193/100000000000000 : ℝ)^3151 := by
    have hnat : (526601561 : ℕ)^4175*100000000000000^3151 ≤ 42753381251193^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526601561 1000000000 42753381251193 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159734259/10000000000 : ℝ), (2696362489/5000000000 : ℝ), (526601561/1000000000 : ℝ)] ![(6562453928043/50000000000000 : ℝ), (5515213859431/12500000000000 : ℝ), (42753381251193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159734259/10000000000 : ℝ)|^4175 ≤ (6562453928043/50000000000000 : ℝ)^3151
        have hw : |(-2159734259/10000000000 : ℝ)|=(2159734259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696362489/5000000000 : ℝ)|^4175 ≤ (5515213859431/12500000000000 : ℝ)^3151
        have hw : |(2696362489/5000000000 : ℝ)|=(2696362489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526601561/1000000000 : ℝ)|^4175 ≤ (42753381251193/100000000000000 : ℝ)^3151
        have hw : |(526601561/1000000000 : ℝ)|=(526601561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s8_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668086537/1250000000 : ℝ)*x 0 + (-1111999583/5000000000 : ℝ)*x 1 + (5266015599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668086537/1250000000 : ℝ)^4175 ≤ (43601764300193/100000000000000 : ℝ)^3151 := by
    have hnat : (668086537 : ℕ)^4175*100000000000000^3151 ≤ 43601764300193^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668086537 1250000000 43601764300193 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111999583/5000000000 : ℝ)^4175 ≤ (6822427282271/50000000000000 : ℝ)^3151 := by
    have hnat : (1111999583 : ℕ)^4175*50000000000000^3151 ≤ 6822427282271^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111999583 5000000000 6822427282271 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266015599/10000000000 : ℝ)^4175 ≤ (8550676226573/20000000000000 : ℝ)^3151 := by
    have hnat : (5266015599 : ℕ)^4175*20000000000000^3151 ≤ 8550676226573^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266015599 10000000000 8550676226573 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668086537/1250000000 : ℝ), (-1111999583/5000000000 : ℝ), (5266015599/10000000000 : ℝ)] ![(43601764300193/100000000000000 : ℝ), (6822427282271/50000000000000 : ℝ), (8550676226573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668086537/1250000000 : ℝ)|^4175 ≤ (43601764300193/100000000000000 : ℝ)^3151
        have hw : |(668086537/1250000000 : ℝ)|=(668086537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111999583/5000000000 : ℝ)|^4175 ≤ (6822427282271/50000000000000 : ℝ)^3151
        have hw : |(-1111999583/5000000000 : ℝ)|=(1111999583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266015599/10000000000 : ℝ)|^4175 ≤ (8550676226573/20000000000000 : ℝ)^3151
        have hw : |(5266015599/10000000000 : ℝ)|=(5266015599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s8_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344692293/10000000000 : ℝ)*x 0 + (658251951/1250000000 : ℝ)*x 1 + (-1111999579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344692293/10000000000 : ℝ)^4175 ≤ (21800882133883/50000000000000 : ℝ)^3151 := by
    have hnat : (5344692293 : ℕ)^4175*50000000000000^3151 ≤ 21800882133883^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344692293 10000000000 21800882133883 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658251951/1250000000 : ℝ)^4175 ≤ (42753381229679/100000000000000 : ℝ)^3151 := by
    have hnat : (658251951 : ℕ)^4175*100000000000000^3151 ≤ 42753381229679^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658251951 1250000000 42753381229679 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111999579/5000000000 : ℝ)^4175 ≤ (13644854499509/100000000000000 : ℝ)^3151 := by
    have hnat : (1111999579 : ℕ)^4175*100000000000000^3151 ≤ 13644854499509^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111999579 5000000000 13644854499509 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344692293/10000000000 : ℝ), (658251951/1250000000 : ℝ), (-1111999579/5000000000 : ℝ)] ![(21800882133883/50000000000000 : ℝ), (42753381229679/100000000000000 : ℝ), (13644854499509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344692293/10000000000 : ℝ)|^4175 ≤ (21800882133883/50000000000000 : ℝ)^3151
        have hw : |(5344692293/10000000000 : ℝ)|=(5344692293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658251951/1250000000 : ℝ)|^4175 ≤ (42753381229679/100000000000000 : ℝ)^3151
        have hw : |(658251951/1250000000 : ℝ)|=(658251951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111999579/5000000000 : ℝ)|^4175 ≤ (13644854499509/100000000000000 : ℝ)^3151
        have hw : |(-1111999579/5000000000 : ℝ)|=(1111999579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s8_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2181283051/5000000000 : ℝ)*x 0 + (4237968849/10000000000 : ℝ)*x 1 + (4490795737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181283051/5000000000 : ℝ)^4175 ≤ (33317066217857/100000000000000 : ℝ)^3151 := by
    have hnat : (2181283051 : ℕ)^4175*100000000000000^3151 ≤ 33317066217857^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181283051 5000000000 33317066217857 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237968849/10000000000 : ℝ)^4175 ≤ (32062169560173/100000000000000 : ℝ)^3151 := by
    have hnat : (4237968849 : ℕ)^4175*100000000000000^3151 ≤ 32062169560173^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237968849 10000000000 32062169560173 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490795737/10000000000 : ℝ)^4175 ≤ (34620764210177/100000000000000 : ℝ)^3151 := by
    have hnat : (4490795737 : ℕ)^4175*100000000000000^3151 ≤ 34620764210177^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490795737 10000000000 34620764210177 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181283051/5000000000 : ℝ), (4237968849/10000000000 : ℝ), (4490795737/10000000000 : ℝ)] ![(33317066217857/100000000000000 : ℝ), (32062169560173/100000000000000 : ℝ), (34620764210177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181283051/5000000000 : ℝ)|^4175 ≤ (33317066217857/100000000000000 : ℝ)^3151
        have hw : |(2181283051/5000000000 : ℝ)|=(2181283051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237968849/10000000000 : ℝ)|^4175 ≤ (32062169560173/100000000000000 : ℝ)^3151
        have hw : |(4237968849/10000000000 : ℝ)|=(4237968849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490795737/10000000000 : ℝ)|^4175 ≤ (34620764210177/100000000000000 : ℝ)^3151
        have hw : |(4490795737/10000000000 : ℝ)|=(4490795737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s8_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-539934751/2500000000 : ℝ)*x 0 + (5266334059/10000000000 : ℝ)*x 1 + (5392405449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539934751/2500000000 : ℝ)^4175 ≤ (6562473031431/50000000000000 : ℝ)^3151 := by
    have hnat : (539934751 : ℕ)^4175*50000000000000^3151 ≤ 6562473031431^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539934751 2500000000 6562473031431 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266334059/10000000000 : ℝ)^4175 ≤ (21378403441013/50000000000000 : ℝ)^3151 := by
    have hnat : (5266334059 : ℕ)^4175*50000000000000^3151 ≤ 21378403441013^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266334059 10000000000 21378403441013 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392405449/10000000000 : ℝ)^4175 ≤ (22059123516031/50000000000000 : ℝ)^3151 := by
    have hnat : (5392405449 : ℕ)^4175*50000000000000^3151 ≤ 22059123516031^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392405449 10000000000 22059123516031 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539934751/2500000000 : ℝ), (5266334059/10000000000 : ℝ), (5392405449/10000000000 : ℝ)] ![(6562473031431/50000000000000 : ℝ), (21378403441013/50000000000000 : ℝ), (22059123516031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539934751/2500000000 : ℝ)|^4175 ≤ (6562473031431/50000000000000 : ℝ)^3151
        have hw : |(-539934751/2500000000 : ℝ)|=(539934751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266334059/10000000000 : ℝ)|^4175 ≤ (21378403441013/50000000000000 : ℝ)^3151
        have hw : |(5266334059/10000000000 : ℝ)|=(5266334059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392405449/10000000000 : ℝ)|^4175 ≤ (22059123516031/50000000000000 : ℝ)^3151
        have hw : |(5392405449/10000000000 : ℝ)|=(5392405449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s8_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10625109/20000000 : ℝ)*x 0 + (-65550283/312500000 : ℝ)*x 1 + (5392405497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10625109/20000000 : ℝ)^4175 ≤ (43254723598377/100000000000000 : ℝ)^3151 := by
    have hnat : (10625109 : ℕ)^4175*100000000000000^3151 ≤ 43254723598377^3151*20000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10625109 20000000 43254723598377 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65550283/312500000 : ℝ)^4175 ≤ (12627028832941/100000000000000 : ℝ)^3151 := by
    have hnat : (65550283 : ℕ)^4175*100000000000000^3151 ≤ 12627028832941^3151*312500000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65550283 312500000 12627028832941 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392405497/10000000000 : ℝ)^4175 ≤ (110295618881/250000000000 : ℝ)^3151 := by
    have hnat : (5392405497 : ℕ)^4175*250000000000^3151 ≤ 110295618881^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392405497 10000000000 110295618881 250000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10625109/20000000 : ℝ), (-65550283/312500000 : ℝ), (5392405497/10000000000 : ℝ)] ![(43254723598377/100000000000000 : ℝ), (12627028832941/100000000000000 : ℝ), (110295618881/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10625109/20000000 : ℝ)|^4175 ≤ (43254723598377/100000000000000 : ℝ)^3151
        have hw : |(10625109/20000000 : ℝ)|=(10625109/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65550283/312500000 : ℝ)|^4175 ≤ (12627028832941/100000000000000 : ℝ)^3151
        have hw : |(-65550283/312500000 : ℝ)|=(65550283/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392405497/10000000000 : ℝ)|^4175 ≤ (110295618881/250000000000 : ℝ)^3151
        have hw : |(5392405497/10000000000 : ℝ)|=(5392405497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s8_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312554291/10000000000 : ℝ)*x 0 + (5392405513/10000000000 : ℝ)*x 1 + (-1048804659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312554291/10000000000 : ℝ)^4175 ≤ (432547213437/1000000000000 : ℝ)^3151 := by
    have hnat : (5312554291 : ℕ)^4175*1000000000000^3151 ≤ 432547213437^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312554291 10000000000 432547213437 1000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392405513/10000000000 : ℝ)^4175 ≤ (8823649545169/20000000000000 : ℝ)^3151 := by
    have hnat : (5392405513 : ℕ)^4175*20000000000000^3151 ≤ 8823649545169^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392405513 10000000000 8823649545169 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048804659/5000000000 : ℝ)^4175 ≤ (12627030922651/100000000000000 : ℝ)^3151 := by
    have hnat : (1048804659 : ℕ)^4175*100000000000000^3151 ≤ 12627030922651^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048804659 5000000000 12627030922651 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312554291/10000000000 : ℝ), (5392405513/10000000000 : ℝ), (-1048804659/5000000000 : ℝ)] ![(432547213437/1000000000000 : ℝ), (8823649545169/20000000000000 : ℝ), (12627030922651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312554291/10000000000 : ℝ)|^4175 ≤ (432547213437/1000000000000 : ℝ)^3151
        have hw : |(5312554291/10000000000 : ℝ)|=(5312554291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392405513/10000000000 : ℝ)|^4175 ≤ (8823649545169/20000000000000 : ℝ)^3151
        have hw : |(5392405513/10000000000 : ℝ)|=(5392405513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048804659/5000000000 : ℝ)|^4175 ≤ (12627030922651/100000000000000 : ℝ)^3151
        have hw : |(-1048804659/5000000000 : ℝ)|=(1048804659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s8_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362575591/10000000000 : ℝ)*x 0 + (4490160479/10000000000 : ℝ)*x 1 + (2119303287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362575591/10000000000 : ℝ)^4175 ≤ (4164645279503/12500000000000 : ℝ)^3151 := by
    have hnat : (4362575591 : ℕ)^4175*12500000000000^3151 ≤ 4164645279503^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362575591 10000000000 4164645279503 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490160479/10000000000 : ℝ)^4175 ≤ (17307137726029/50000000000000 : ℝ)^3151 := by
    have hnat : (4490160479 : ℕ)^4175*50000000000000^3151 ≤ 17307137726029^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490160479 10000000000 17307137726029 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119303287/5000000000 : ℝ)^4175 ≤ (16034281151871/50000000000000 : ℝ)^3151 := by
    have hnat : (2119303287 : ℕ)^4175*50000000000000^3151 ≤ 16034281151871^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119303287 5000000000 16034281151871 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362575591/10000000000 : ℝ), (4490160479/10000000000 : ℝ), (2119303287/5000000000 : ℝ)] ![(4164645279503/12500000000000 : ℝ), (17307137726029/50000000000000 : ℝ), (16034281151871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362575591/10000000000 : ℝ)|^4175 ≤ (4164645279503/12500000000000 : ℝ)^3151
        have hw : |(4362575591/10000000000 : ℝ)|=(4362575591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490160479/10000000000 : ℝ)|^4175 ≤ (17307137726029/50000000000000 : ℝ)^3151
        have hw : |(4490160479/10000000000 : ℝ)|=(4490160479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119303287/5000000000 : ℝ)|^4175 ≤ (16034281151871/50000000000000 : ℝ)^3151
        have hw : |(2119303287/5000000000 : ℝ)|=(2119303287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2843/25000 : ℝ) ^ (8349/2048 : ℝ) ≤ (14156885174574933/100000000000000000000 : ℝ) := by
    have hpowers : (2843/25000 : ℝ)^8349 ≤ (14156885174574933/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2843 : ℕ)^8349*100000000000000000000^2048 ≤ 14156885174574933^2048*25000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2843 25000 14156885174574933 100000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2843/25000 : ℝ)) (X := (14156885174574933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14059/100000 : ℝ) ^ (8349/2048 : ℝ) ≤ (33612419666126009/100000000000000000000 : ℝ) := by
    have hpowers : (14059/100000 : ℝ)^8349 ≤ (33612419666126009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14059 : ℕ)^8349*100000000000000000000^2048 ≤ 33612419666126009^2048*100000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14059 100000 33612419666126009 100000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14059/100000 : ℝ)) (X := (33612419666126009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014156885174574933/50000000000000000000 : ℝ) ≤ (5000347229651971/5000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50014156885174574933/50000000000000000000 : ℝ)^2048 ≤ (5000347229651971/5000000000000000 : ℝ)^8349 := by
      have hnat : (50014156885174574933 : ℕ)^2048*5000000000000000^8349 ≤ 5000347229651971^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014156885174574933 50000000000000000000 5000347229651971 5000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000347229651971/5000000000000000 : ℝ)) (X := (50014156885174574933/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023884652420350471/50000000000000000000 : ℝ) ≤ (2500292891083803/2500000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50023884652420350471/50000000000000000000 : ℝ)^2048 ≤ (2500292891083803/2500000000000000 : ℝ)^8349 := by
      have hnat : (50023884652420350471 : ℕ)^2048*2500000000000000^8349 ≤ 2500292891083803^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023884652420350471 50000000000000000000 2500292891083803 2500000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500292891083803/2500000000000000 : ℝ)) (X := (50023884652420350471/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033612419666126009/50000000000000000000 : ℝ) ≤ (5000824334683241/5000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50033612419666126009/50000000000000000000 : ℝ)^2048 ≤ (5000824334683241/5000000000000000 : ℝ)^8349 := by
      have hnat : (50033612419666126009 : ℕ)^2048*5000000000000000^8349 ≤ 5000824334683241^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033612419666126009 50000000000000000000 5000824334683241 5000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000824334683241/5000000000000000 : ℝ)) (X := (50033612419666126009/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14156885174574933/100000000000000000000 : ℝ) ≤ ((13430507367659243637/13435000000000000000 : ℝ)+2*(47710503127/26870000000000 : ℝ)*(2843/25000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (13430507367659243637/13435000000000000000 : ℝ)+2*(47710503127/26870000000000 : ℝ)*(2843/25000 : ℝ)=(5000347229651971/5000000000000000 : ℝ) by norm_num, show 1+2*(14156885174574933/100000000000000000000 : ℝ)=(50014156885174574933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33612419666126009/100000000000000000000 : ℝ)+(14156885174574933/100000000000000000000 : ℝ) ≤ ((13430507367659243637/13435000000000000000 : ℝ)+(47710503127/26870000000000 : ℝ)*((14059/100000 : ℝ)+(2843/25000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (13430507367659243637/13435000000000000000 : ℝ)+(47710503127/26870000000000 : ℝ)*((14059/100000 : ℝ)+(2843/25000 : ℝ))=(2500292891083803/2500000000000000 : ℝ) by norm_num, show 1+(33612419666126009/100000000000000000000 : ℝ)+(14156885174574933/100000000000000000000 : ℝ)=(50023884652420350471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33612419666126009/100000000000000000000 : ℝ) ≤ ((13430507367659243637/13435000000000000000 : ℝ)+2*(47710503127/26870000000000 : ℝ)*(14059/100000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (13430507367659243637/13435000000000000000 : ℝ)+2*(47710503127/26870000000000 : ℝ)*(14059/100000 : ℝ)=(5000824334683241/5000000000000000 : ℝ) by norm_num, show 1+2*(33612419666126009/100000000000000000000 : ℝ)=(50033612419666126009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13430507367659243637/13435000000000000000 : ℝ)*(X 1 0+X 2 0)+(47710503127/26870000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (13430507367659243637/13435000000000000000 : ℝ)) (alpha := (47710503127/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13430507367659243637/13435000000000000000 : ℝ)*(X 0 1+X 2 1)+(47710503127/26870000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (13430507367659243637/13435000000000000000 : ℝ)) (alpha := (47710503127/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13430507367659243637/13435000000000000000 : ℝ)*(X 0 2+X 1 2)+(47710503127/26870000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (13430507367659243637/13435000000000000000 : ℝ)) (alpha := (47710503127/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2159734259/10000000000 : ℝ)*X 0 0+(2696362489/5000000000 : ℝ)*X 0 1+(526601561/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668086537/1250000000 : ℝ)*X 1 0+(-1111999583/5000000000 : ℝ)*X 1 1+(5266015599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344692293/10000000000 : ℝ)*X 2 0+(658251951/1250000000 : ℝ)*X 2 1+(-1111999579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181283051/5000000000 : ℝ)*X 0 0+(4237968849/10000000000 : ℝ)*X 0 1+(4490795737/10000000000 : ℝ)*X 0 2+(2181283051/5000000000 : ℝ)*X 1 0+(4237968849/10000000000 : ℝ)*X 1 1+(4490795737/10000000000 : ℝ)*X 1 2+(2181283051/5000000000 : ℝ)*X 2 0+(4237968849/10000000000 : ℝ)*X 2 1+(4490795737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-539934751/2500000000 : ℝ)*X 0 0+(5266334059/10000000000 : ℝ)*X 0 1+(5392405449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10625109/20000000 : ℝ)*X 1 0+(-65550283/312500000 : ℝ)*X 1 1+(5392405497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312554291/10000000000 : ℝ)*X 2 0+(5392405513/10000000000 : ℝ)*X 2 1+(-1048804659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362575591/10000000000 : ℝ)*X 0 0+(4490160479/10000000000 : ℝ)*X 0 1+(2119303287/5000000000 : ℝ)*X 0 2+(4362575591/10000000000 : ℝ)*X 1 0+(4490160479/10000000000 : ℝ)*X 1 1+(2119303287/5000000000 : ℝ)*X 1 2+(4362575591/10000000000 : ℝ)*X 2 0+(4490160479/10000000000 : ℝ)*X 2 1+(2119303287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22378806969788741953983/2687000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1640648101/100000000000000 : ℝ)*(base19) + (302471193/20000000000000 : ℝ)*(base23) + (66200549/100000000000000 : ℝ)*(lower2) + (12565269/6250000000000 : ℝ)*(upper3) + (15193423/12500000000000 : ℝ)*(upper5) + (1184748937817891/20000000000000 : ℝ)*(major0) + (1184748937817891/20000000000000 : ℝ)*(major1) + (1184748937817891/20000000000000 : ℝ)*(major2) + (7892122971732323/100000000000000 : ℝ)*(sp0) + (1973041547172629/25000000000000 : ℝ)*(sp1) + (1973041579245663/25000000000000 : ℝ)*(sp2) + (247206075028979/6250000000000 : ℝ)*(sp3) + (44857606293/100000000000000 : ℝ)*(sp4) + (6017689593/25000000000000 : ℝ)*(sp7) + (988830317805509/25000000000000 : ℝ)*(f.failure) + (7892167829338617/100000000000000 : ℝ)*(f.sum) + (8271708750633/2687000000000000000000000000 : ℝ)*base65 + (4991739748671509567/268700000000000000000000000000000 : ℝ)*base67 + (1446879309897090433/268700000000000000000000000000000 : ℝ)*base70 + (3501099571975809567/268700000000000000000000000000000 : ℝ)*base71 + (10156664290227/1343500000000000000000000000 : ℝ)*base73 + (1315191185640990433/268700000000000000000000000000000 : ℝ)*base76 + (2972933098165809567/268700000000000000000000000000000 : ℝ)*base77 + (29332268972990433/268700000000000000000000000000000 : ℝ)*base80 + (1331192657701/268700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5766351/2500000000000000000000 : ℝ)*base90 + (5766351/2500000000000000000000 : ℝ)*base92 + (5766351/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2960607022028059685883257349/671750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8966241/1000000000000 : ℝ)*(base19) + (284572397/50000000000000 : ℝ)*(base23) + (29080127/12500000000000 : ℝ)*(lower1) + (758241/20000000000000 : ℝ)*(upper3) + (23206951/50000000000000 : ℝ)*(lower4) + (372657/2500000000000 : ℝ)*(upper5) + (5953634608382341/100000000000000 : ℝ)*(major0) + (5953634608382341/100000000000000 : ℝ)*(major1) + (5953634608382341/100000000000000 : ℝ)*(major2) + (16992604809/100000000000000 : ℝ)*(sp1) + (1982997528279443/25000000000000 : ℝ)*(sp4) + (7931972223888863/100000000000000 : ℝ)*(sp5) + (3965994771986489/50000000000000 : ℝ)*(sp6) + (3975278956736743/100000000000000 : ℝ)*(sp7) + (3975278956736743/100000000000000 : ℝ)*(f.failure) + (1982997528279443/25000000000000 : ℝ)*(f.sum) + (828122013561/2687000000000000000000000000 : ℝ)*base66 + (3719855528463414217/1343500000000000000000000000000000 : ℝ)*base67 + (18317590643464085783/1343500000000000000000000000000000 : ℝ)*base70 + (7472051341371414217/1343500000000000000000000000000000 : ℝ)*base71 + (8616182532689/2687000000000000000000000000 : ℝ)*base73 + (20041510560183085783/1343500000000000000000000000000000 : ℝ)*base76 + (8551468099092414217/1343500000000000000000000000000000 : ℝ)*base77 + (7577808256942414217/1343500000000000000000000000000000 : ℝ)*base79 + (3756207154193/671750000000000000000000000 : ℝ)*base82 + (7776523/10000000000000000000000 : ℝ)*base89 + (7776523/10000000000000000000000 : ℝ)*base91 + (7776523/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1157_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1157_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1157_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1157_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1157_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1157_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

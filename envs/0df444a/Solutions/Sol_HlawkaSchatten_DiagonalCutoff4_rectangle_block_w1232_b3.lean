-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1232_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:15:40.909001+00:00
-- url     : https://prove2.me/submissions/d4bb1344-d9ad-4094-a923-a14747b46568

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
theorem support_rectangle_w1232_box_0 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1000283041/5000000000 : ℝ)*x 0 + (671874367/1250000000 : ℝ)*x 1 + (5374995133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000283041/5000000000 : ℝ)^8425 ≤ (11932055289543/100000000000000 : ℝ)^6377 := by
    have hnat : (1000283041 : ℕ)^8425*100000000000000^6377 ≤ 11932055289543^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000283041 5000000000 11932055289543 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671874367/1250000000 : ℝ)^8425 ≤ (5504246410793/12500000000000 : ℝ)^6377 := by
    have hnat : (671874367 : ℕ)^8425*12500000000000^6377 ≤ 5504246410793^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671874367 1250000000 5504246410793 12500000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374995133/10000000000 : ℝ)^8425 ≤ (5504246677319/12500000000000 : ℝ)^6377 := by
    have hnat : (5374995133 : ℕ)^8425*12500000000000^6377 ≤ 5504246677319^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374995133 10000000000 5504246677319 12500000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1000283041/5000000000 : ℝ), (671874367/1250000000 : ℝ), (5374995133/10000000000 : ℝ)] ![(11932055289543/100000000000000 : ℝ), (5504246410793/12500000000000 : ℝ), (5504246677319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1000283041/5000000000 : ℝ)|^8425 ≤ (11932055289543/100000000000000 : ℝ)^6377
        have hw : |(-1000283041/5000000000 : ℝ)|=(1000283041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(671874367/1250000000 : ℝ)|^8425 ≤ (5504246410793/12500000000000 : ℝ)^6377
        have hw : |(671874367/1250000000 : ℝ)|=(671874367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374995133/10000000000 : ℝ)|^8425 ≤ (5504246677319/12500000000000 : ℝ)^6377
        have hw : |(5374995133/10000000000 : ℝ)|=(5374995133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_1 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296722563/10000000000 : ℝ)*x 0 + (-1053463851/5000000000 : ℝ)*x 1 + (2687497767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296722563/10000000000 : ℝ)^8425 ≤ (43188786479413/100000000000000 : ℝ)^6377 := by
    have hnat : (5296722563 : ℕ)^8425*100000000000000^6377 ≤ 43188786479413^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296722563 10000000000 43188786479413 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053463851/5000000000 : ℝ)^8425 ≤ (6388617871827/50000000000000 : ℝ)^6377 := by
    have hnat : (1053463851 : ℕ)^8425*50000000000000^6377 ≤ 6388617871827^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053463851 5000000000 6388617871827 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687497767/5000000000 : ℝ)^8425 ≤ (44033977758731/100000000000000 : ℝ)^6377 := by
    have hnat : (2687497767 : ℕ)^8425*100000000000000^6377 ≤ 44033977758731^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687497767 5000000000 44033977758731 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296722563/10000000000 : ℝ), (-1053463851/5000000000 : ℝ), (2687497767/5000000000 : ℝ)] ![(43188786479413/100000000000000 : ℝ), (6388617871827/50000000000000 : ℝ), (44033977758731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296722563/10000000000 : ℝ)|^8425 ≤ (43188786479413/100000000000000 : ℝ)^6377
        have hw : |(5296722563/10000000000 : ℝ)|=(5296722563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053463851/5000000000 : ℝ)|^8425 ≤ (6388617871827/50000000000000 : ℝ)^6377
        have hw : |(-1053463851/5000000000 : ℝ)|=(1053463851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687497767/5000000000 : ℝ)|^8425 ≤ (44033977758731/100000000000000 : ℝ)^6377
        have hw : |(2687497767/5000000000 : ℝ)|=(2687497767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_2 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529672409/1000000000 : ℝ)*x 0 + (5374995239/10000000000 : ℝ)*x 1 + (-65841439/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529672409/1000000000 : ℝ)^8425 ≤ (863776058581/2000000000000 : ℝ)^6377 := by
    have hnat : (529672409 : ℕ)^8425*2000000000000^6377 ≤ 863776058581^6377*1000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529672409 1000000000 863776058581 2000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374995239/10000000000 : ℝ)^8425 ≤ (44033974565831/100000000000000 : ℝ)^6377 := by
    have hnat : (5374995239 : ℕ)^8425*100000000000000^6377 ≤ 44033974565831^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374995239 10000000000 44033974565831 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65841439/312500000 : ℝ)^8425 ≤ (12777222491813/100000000000000 : ℝ)^6377 := by
    have hnat : (65841439 : ℕ)^8425*100000000000000^6377 ≤ 12777222491813^6377*312500000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65841439 312500000 12777222491813 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529672409/1000000000 : ℝ), (5374995239/10000000000 : ℝ), (-65841439/312500000 : ℝ)] ![(863776058581/2000000000000 : ℝ), (44033974565831/100000000000000 : ℝ), (12777222491813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529672409/1000000000 : ℝ)|^8425 ≤ (863776058581/2000000000000 : ℝ)^6377
        have hw : |(529672409/1000000000 : ℝ)|=(529672409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374995239/10000000000 : ℝ)|^8425 ≤ (44033974565831/100000000000000 : ℝ)^6377
        have hw : |(5374995239/10000000000 : ℝ)|=(5374995239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65841439/312500000 : ℝ)|^8425 ≤ (12777222491813/100000000000000 : ℝ)^6377
        have hw : |(-65841439/312500000 : ℝ)|=(65841439/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_3 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4458778013/10000000000 : ℝ)*x 0 + (4300882517/10000000000 : ℝ)*x 1 + (2150440627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4458778013/10000000000 : ℝ)^8425 ≤ (34400128624917/100000000000000 : ℝ)^6377 := by
    have hnat : (4458778013 : ℕ)^8425*100000000000000^6377 ≤ 34400128624917^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4458778013 10000000000 34400128624917 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4300882517/10000000000 : ℝ)^8425 ≤ (32799942040017/100000000000000 : ℝ)^6377 := by
    have hnat : (4300882517 : ℕ)^8425*100000000000000^6377 ≤ 32799942040017^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300882517 10000000000 32799942040017 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150440627/5000000000 : ℝ)^8425 ≤ (1024997791081/3125000000000 : ℝ)^6377 := by
    have hnat : (2150440627 : ℕ)^8425*3125000000000^6377 ≤ 1024997791081^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150440627 5000000000 1024997791081 3125000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4458778013/10000000000 : ℝ), (4300882517/10000000000 : ℝ), (2150440627/5000000000 : ℝ)] ![(34400128624917/100000000000000 : ℝ), (32799942040017/100000000000000 : ℝ), (1024997791081/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4458778013/10000000000 : ℝ)|^8425 ≤ (34400128624917/100000000000000 : ℝ)^6377
        have hw : |(4458778013/10000000000 : ℝ)|=(4458778013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4300882517/10000000000 : ℝ)|^8425 ≤ (32799942040017/100000000000000 : ℝ)^6377
        have hw : |(4300882517/10000000000 : ℝ)|=(4300882517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2150440627/5000000000 : ℝ)|^8425 ≤ (1024997791081/3125000000000 : ℝ)^6377
        have hw : |(2150440627/5000000000 : ℝ)|=(2150440627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_4 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-562492271/2500000000 : ℝ)*x 0 + (264109043/500000000 : ℝ)*x 1 + (2641090443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (562492271/2500000000 : ℝ)^8425 ≤ (3483897519957/25000000000000 : ℝ)^6377 := by
    have hnat : (562492271 : ℕ)^8425*25000000000000^6377 ≤ 3483897519957^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562492271 2500000000 3483897519957 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264109043/500000000 : ℝ)^8425 ≤ (10758051202567/25000000000000 : ℝ)^6377 := by
    have hnat : (264109043 : ℕ)^8425*25000000000000^6377 ≤ 10758051202567^6377*500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264109043 500000000 10758051202567 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641090443/5000000000 : ℝ)^8425 ≤ (21516102545053/50000000000000 : ℝ)^6377 := by
    have hnat : (2641090443 : ℕ)^8425*50000000000000^6377 ≤ 21516102545053^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641090443 5000000000 21516102545053 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-562492271/2500000000 : ℝ), (264109043/500000000 : ℝ), (2641090443/5000000000 : ℝ)] ![(3483897519957/25000000000000 : ℝ), (10758051202567/25000000000000 : ℝ), (21516102545053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-562492271/2500000000 : ℝ)|^8425 ≤ (3483897519957/25000000000000 : ℝ)^6377
        have hw : |(-562492271/2500000000 : ℝ)|=(562492271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264109043/500000000 : ℝ)|^8425 ≤ (10758051202567/25000000000000 : ℝ)^6377
        have hw : |(264109043/500000000 : ℝ)|=(264109043/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641090443/5000000000 : ℝ)|^8425 ≤ (21516102545053/50000000000000 : ℝ)^6377
        have hw : |(2641090443/5000000000 : ℝ)|=(2641090443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_5 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335135359/625000000 : ℝ)*x 0 + (-1071846803/5000000000 : ℝ)*x 1 + (5282180839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335135359/625000000 : ℝ)^8425 ≤ (21947584596043/50000000000000 : ℝ)^6377 := by
    have hnat : (335135359 : ℕ)^8425*50000000000000^6377 ≤ 21947584596043^6377*625000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335135359 625000000 21947584596043 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071846803/5000000000 : ℝ)^8425 ≤ (13072626214521/100000000000000 : ℝ)^6377 := by
    have hnat : (1071846803 : ℕ)^8425*100000000000000^6377 ≤ 13072626214521^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071846803 5000000000 13072626214521 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282180839/10000000000 : ℝ)^8425 ≤ (10758051146061/25000000000000 : ℝ)^6377 := by
    have hnat : (5282180839 : ℕ)^8425*25000000000000^6377 ≤ 10758051146061^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282180839 10000000000 10758051146061 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335135359/625000000 : ℝ), (-1071846803/5000000000 : ℝ), (5282180839/10000000000 : ℝ)] ![(21947584596043/50000000000000 : ℝ), (13072626214521/100000000000000 : ℝ), (10758051146061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335135359/625000000 : ℝ)|^8425 ≤ (21947584596043/50000000000000 : ℝ)^6377
        have hw : |(335135359/625000000 : ℝ)|=(335135359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1071846803/5000000000 : ℝ)|^8425 ≤ (13072626214521/100000000000000 : ℝ)^6377
        have hw : |(-1071846803/5000000000 : ℝ)|=(1071846803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282180839/10000000000 : ℝ)|^8425 ≤ (10758051146061/25000000000000 : ℝ)^6377
        have hw : |(5282180839/10000000000 : ℝ)|=(5282180839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_6 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362165711/10000000000 : ℝ)*x 0 + (5282180849/10000000000 : ℝ)*x 1 + (-2143693637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362165711/10000000000 : ℝ)^8425 ≤ (43895168835189/100000000000000 : ℝ)^6377 := by
    have hnat : (5362165711 : ℕ)^8425*100000000000000^6377 ≤ 43895168835189^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362165711 10000000000 43895168835189 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282180849/10000000000 : ℝ)^8425 ≤ (21516102345937/50000000000000 : ℝ)^6377 := by
    have hnat : (5282180849 : ℕ)^8425*50000000000000^6377 ≤ 21516102345937^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282180849 10000000000 21516102345937 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2143693637/10000000000 : ℝ)^8425 ≤ (3268156616069/25000000000000 : ℝ)^6377 := by
    have hnat : (2143693637 : ℕ)^8425*25000000000000^6377 ≤ 3268156616069^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143693637 10000000000 3268156616069 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362165711/10000000000 : ℝ), (5282180849/10000000000 : ℝ), (-2143693637/10000000000 : ℝ)] ![(43895168835189/100000000000000 : ℝ), (21516102345937/50000000000000 : ℝ), (3268156616069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362165711/10000000000 : ℝ)|^8425 ≤ (43895168835189/100000000000000 : ℝ)^6377
        have hw : |(5362165711/10000000000 : ℝ)|=(5362165711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282180849/10000000000 : ℝ)|^8425 ≤ (21516102345937/50000000000000 : ℝ)^6377
        have hw : |(5282180849/10000000000 : ℝ)|=(5282180849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2143693637/10000000000 : ℝ)|^8425 ≤ (3268156616069/25000000000000 : ℝ)^6377
        have hw : |(-2143693637/10000000000 : ℝ)|=(2143693637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_7 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (424512083/1000000000 : ℝ)*x 0 + (550961293/1250000000 : ℝ)*x 1 + (137740321/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424512083/1000000000 : ℝ)^8425 ≤ (32239285210769/100000000000000 : ℝ)^6377 := by
    have hnat : (424512083 : ℕ)^8425*100000000000000^6377 ≤ 32239285210769^6377*1000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424512083 1000000000 32239285210769 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550961293/1250000000 : ℝ)^8425 ≤ (33880357756677/100000000000000 : ℝ)^6377 := by
    have hnat : (550961293 : ℕ)^8425*100000000000000^6377 ≤ 33880357756677^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550961293 1250000000 33880357756677 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137740321/312500000 : ℝ)^8425 ≤ (33880357025499/100000000000000 : ℝ)^6377 := by
    have hnat : (137740321 : ℕ)^8425*100000000000000^6377 ≤ 33880357025499^6377*312500000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137740321 312500000 33880357025499 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424512083/1000000000 : ℝ), (550961293/1250000000 : ℝ), (137740321/312500000 : ℝ)] ![(32239285210769/100000000000000 : ℝ), (33880357756677/100000000000000 : ℝ), (33880357025499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424512083/1000000000 : ℝ)|^8425 ≤ (32239285210769/100000000000000 : ℝ)^6377
        have hw : |(424512083/1000000000 : ℝ)|=(424512083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550961293/1250000000 : ℝ)|^8425 ≤ (33880357756677/100000000000000 : ℝ)^6377
        have hw : |(550961293/1250000000 : ℝ)|=(550961293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137740321/312500000 : ℝ)|^8425 ≤ (33880357025499/100000000000000 : ℝ)^6377
        have hw : |(137740321/312500000 : ℝ)|=(137740321/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_8 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197717273/10000000000 : ℝ)*x 0 + (2609445057/5000000000 : ℝ)*x 1 + (336538037/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197717273/10000000000 : ℝ)^8425 ≤ (13509626513733/100000000000000 : ℝ)^6377 := by
    have hnat : (2197717273 : ℕ)^8425*100000000000000^6377 ≤ 13509626513733^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197717273 10000000000 13509626513733 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609445057/5000000000 : ℝ)^8425 ≤ (42352319967789/100000000000000 : ℝ)^6377 := by
    have hnat : (2609445057 : ℕ)^8425*100000000000000^6377 ≤ 42352319967789^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609445057 5000000000 42352319967789 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336538037/625000000 : ℝ)^8425 ≤ (8827610700451/20000000000000 : ℝ)^6377 := by
    have hnat : (336538037 : ℕ)^8425*20000000000000^6377 ≤ 8827610700451^6377*625000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336538037 625000000 8827610700451 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197717273/10000000000 : ℝ), (2609445057/5000000000 : ℝ), (336538037/625000000 : ℝ)] ![(13509626513733/100000000000000 : ℝ), (42352319967789/100000000000000 : ℝ), (8827610700451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197717273/10000000000 : ℝ)|^8425 ≤ (13509626513733/100000000000000 : ℝ)^6377
        have hw : |(-2197717273/10000000000 : ℝ)|=(2197717273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609445057/5000000000 : ℝ)|^8425 ≤ (42352319967789/100000000000000 : ℝ)^6377
        have hw : |(2609445057/5000000000 : ℝ)|=(2609445057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336538037/625000000 : ℝ)|^8425 ≤ (8827610700451/20000000000000 : ℝ)^6377
        have hw : |(336538037/625000000 : ℝ)|=(336538037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_9 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289942363/10000000000 : ℝ)*x 0 + (-1051525543/5000000000 : ℝ)*x 1 + (538460853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289942363/10000000000 : ℝ)^8425 ≤ (8623152332779/20000000000000 : ℝ)^6377 := by
    have hnat : (5289942363 : ℕ)^8425*20000000000000^6377 ≤ 8623152332779^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289942363 10000000000 8623152332779 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051525543/5000000000 : ℝ)^8425 ≤ (12746185489071/100000000000000 : ℝ)^6377 := by
    have hnat : (1051525543 : ℕ)^8425*100000000000000^6377 ≤ 12746185489071^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051525543 5000000000 12746185489071 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538460853/1000000000 : ℝ)^8425 ≤ (44138052830819/100000000000000 : ℝ)^6377 := by
    have hnat : (538460853 : ℕ)^8425*100000000000000^6377 ≤ 44138052830819^6377*1000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538460853 1000000000 44138052830819 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289942363/10000000000 : ℝ), (-1051525543/5000000000 : ℝ), (538460853/1000000000 : ℝ)] ![(8623152332779/20000000000000 : ℝ), (12746185489071/100000000000000 : ℝ), (44138052830819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289942363/10000000000 : ℝ)|^8425 ≤ (8623152332779/20000000000000 : ℝ)^6377
        have hw : |(5289942363/10000000000 : ℝ)|=(5289942363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1051525543/5000000000 : ℝ)|^8425 ≤ (12746185489071/100000000000000 : ℝ)^6377
        have hw : |(-1051525543/5000000000 : ℝ)|=(1051525543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538460853/1000000000 : ℝ)|^8425 ≤ (44138052830819/100000000000000 : ℝ)^6377
        have hw : |(538460853/1000000000 : ℝ)|=(538460853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_10 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330621397/625000000 : ℝ)*x 0 + (336538039/625000000 : ℝ)*x 1 + (-2103050973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330621397/625000000 : ℝ)^8425 ≤ (21557880772723/50000000000000 : ℝ)^6377 := by
    have hnat : (330621397 : ℕ)^8425*50000000000000^6377 ≤ 21557880772723^6377*625000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330621397 625000000 21557880772723 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336538039/625000000 : ℝ)^8425 ≤ (22069026924401/50000000000000 : ℝ)^6377 := by
    have hnat : (336538039 : ℕ)^8425*50000000000000^6377 ≤ 22069026924401^6377*625000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336538039 625000000 22069026924401 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103050973/10000000000 : ℝ)^8425 ≤ (50984738337/400000000000 : ℝ)^6377 := by
    have hnat : (2103050973 : ℕ)^8425*400000000000^6377 ≤ 50984738337^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103050973 10000000000 50984738337 400000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330621397/625000000 : ℝ), (336538039/625000000 : ℝ), (-2103050973/10000000000 : ℝ)] ![(21557880772723/50000000000000 : ℝ), (22069026924401/50000000000000 : ℝ), (50984738337/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330621397/625000000 : ℝ)|^8425 ≤ (21557880772723/50000000000000 : ℝ)^6377
        have hw : |(330621397/625000000 : ℝ)|=(330621397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336538039/625000000 : ℝ)|^8425 ≤ (22069026924401/50000000000000 : ℝ)^6377
        have hw : |(336538039/625000000 : ℝ)|=(336538039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103050973/10000000000 : ℝ)|^8425 ≤ (50984738337/400000000000 : ℝ)^6377
        have hw : |(-2103050973/10000000000 : ℝ)|=(2103050973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_11 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (112015877/250000000 : ℝ)*x 0 + (4289812767/10000000000 : ℝ)*x 1 + (4289812841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112015877/250000000 : ℝ)^8425 ≤ (6924618133627/20000000000000 : ℝ)^6377 := by
    have hnat : (112015877 : ℕ)^8425*20000000000000^6377 ≤ 6924618133627^6377*250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112015877 250000000 6924618133627 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4289812767/10000000000 : ℝ)^8425 ≤ (16344227142911/50000000000000 : ℝ)^6377 := by
    have hnat : (4289812767 : ℕ)^8425*50000000000000^6377 ≤ 16344227142911^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289812767 10000000000 16344227142911 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4289812841/10000000000 : ℝ)^8425 ≤ (8172113757699/25000000000000 : ℝ)^6377 := by
    have hnat : (4289812841 : ℕ)^8425*25000000000000^6377 ≤ 8172113757699^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289812841 10000000000 8172113757699 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112015877/250000000 : ℝ), (4289812767/10000000000 : ℝ), (4289812841/10000000000 : ℝ)] ![(6924618133627/20000000000000 : ℝ), (16344227142911/50000000000000 : ℝ), (8172113757699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112015877/250000000 : ℝ)|^8425 ≤ (6924618133627/20000000000000 : ℝ)^6377
        have hw : |(112015877/250000000 : ℝ)|=(112015877/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4289812767/10000000000 : ℝ)|^8425 ≤ (16344227142911/50000000000000 : ℝ)^6377
        have hw : |(4289812767/10000000000 : ℝ)|=(4289812767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4289812841/10000000000 : ℝ)|^8425 ≤ (8172113757699/25000000000000 : ℝ)^6377
        have hw : |(4289812841/10000000000 : ℝ)|=(4289812841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_12 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-513270731/2500000000 : ℝ)*x 0 + (5437070807/10000000000 : ℝ)*x 1 + (52741047/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513270731/2500000000 : ℝ)^8425 ≤ (771725766563/6250000000000 : ℝ)^6377 := by
    have hnat : (513270731 : ℕ)^8425*6250000000000^6377 ≤ 771725766563^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513270731 2500000000 771725766563 6250000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437070807/10000000000 : ℝ)^8425 ≤ (44707085366423/100000000000000 : ℝ)^6377 := by
    have hnat : (5437070807 : ℕ)^8425*100000000000000^6377 ≤ 44707085366423^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437070807 10000000000 44707085366423 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52741047/100000000 : ℝ)^8425 ≤ (42945302351791/100000000000000 : ℝ)^6377 := by
    have hnat : (52741047 : ℕ)^8425*100000000000000^6377 ≤ 42945302351791^6377*100000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52741047 100000000 42945302351791 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513270731/2500000000 : ℝ), (5437070807/10000000000 : ℝ), (52741047/100000000 : ℝ)] ![(771725766563/6250000000000 : ℝ), (44707085366423/100000000000000 : ℝ), (42945302351791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513270731/2500000000 : ℝ)|^8425 ≤ (771725766563/6250000000000 : ℝ)^6377
        have hw : |(-513270731/2500000000 : ℝ)|=(513270731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437070807/10000000000 : ℝ)|^8425 ≤ (44707085366423/100000000000000 : ℝ)^6377
        have hw : |(5437070807/10000000000 : ℝ)|=(5437070807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52741047/100000000 : ℝ)|^8425 ≤ (42945302351791/100000000000000 : ℝ)^6377
        have hw : |(52741047/100000000 : ℝ)|=(52741047/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_13 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683928827/5000000000 : ℝ)*x 0 + (-429367383/2000000000 : ℝ)*x 1 + (5274104959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683928827/5000000000 : ℝ)^8425 ≤ (43956738179719/100000000000000 : ℝ)^6377 := by
    have hnat : (2683928827 : ℕ)^8425*100000000000000^6377 ≤ 43956738179719^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683928827 5000000000 43956738179719 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429367383/2000000000 : ℝ)^8425 ≤ (3274489166207/25000000000000 : ℝ)^6377 := by
    have hnat : (429367383 : ℕ)^8425*25000000000000^6377 ≤ 3274489166207^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429367383 2000000000 3274489166207 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274104959/10000000000 : ℝ)^8425 ≤ (21472652569021/50000000000000 : ℝ)^6377 := by
    have hnat : (5274104959 : ℕ)^8425*50000000000000^6377 ≤ 21472652569021^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274104959 10000000000 21472652569021 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683928827/5000000000 : ℝ), (-429367383/2000000000 : ℝ), (5274104959/10000000000 : ℝ)] ![(43956738179719/100000000000000 : ℝ), (3274489166207/25000000000000 : ℝ), (21472652569021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683928827/5000000000 : ℝ)|^8425 ≤ (43956738179719/100000000000000 : ℝ)^6377
        have hw : |(2683928827/5000000000 : ℝ)|=(2683928827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429367383/2000000000 : ℝ)|^8425 ≤ (3274489166207/25000000000000 : ℝ)^6377
        have hw : |(-429367383/2000000000 : ℝ)|=(429367383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274104959/10000000000 : ℝ)|^8425 ≤ (21472652569021/50000000000000 : ℝ)^6377
        have hw : |(5274104959/10000000000 : ℝ)|=(5274104959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_14 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367857809/10000000000 : ℝ)*x 0 + (527410477/1000000000 : ℝ)*x 1 + (-13417731/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367857809/10000000000 : ℝ)^8425 ≤ (43956739856629/100000000000000 : ℝ)^6377 := by
    have hnat : (5367857809 : ℕ)^8425*100000000000000^6377 ≤ 43956739856629^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367857809 10000000000 43956739856629 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527410477/1000000000 : ℝ)^8425 ≤ (671020361013/1562500000000 : ℝ)^6377 := by
    have hnat : (527410477 : ℕ)^8425*1562500000000^6377 ≤ 671020361013^6377*1000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527410477 1000000000 671020361013 1562500000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13417731/62500000 : ℝ)^8425 ≤ (13097957027547/100000000000000 : ℝ)^6377 := by
    have hnat : (13417731 : ℕ)^8425*100000000000000^6377 ≤ 13097957027547^6377*62500000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13417731 62500000 13097957027547 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367857809/10000000000 : ℝ), (527410477/1000000000 : ℝ), (-13417731/62500000 : ℝ)] ![(43956739856629/100000000000000 : ℝ), (671020361013/1562500000000 : ℝ), (13097957027547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367857809/10000000000 : ℝ)|^8425 ≤ (43956739856629/100000000000000 : ℝ)^6377
        have hw : |(5367857809/10000000000 : ℝ)|=(5367857809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527410477/1000000000 : ℝ)|^8425 ≤ (671020361013/1562500000000 : ℝ)^6377
        have hw : |(527410477/1000000000 : ℝ)|=(527410477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13417731/62500000 : ℝ)|^8425 ≤ (13097957027547/100000000000000 : ℝ)^6377
        have hw : |(-13417731/62500000 : ℝ)|=(13417731/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_box_15 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (52828723/125000000 : ℝ)*x 0 + (4416979009/10000000000 : ℝ)*x 1 + (2208489623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52828723/125000000 : ℝ)^8425 ≤ (32050560915699/100000000000000 : ℝ)^6377 := by
    have hnat : (52828723 : ℕ)^8425*100000000000000^6377 ≤ 32050560915699^6377*125000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52828723 125000000 32050560915699 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416979009/10000000000 : ℝ)^8425 ≤ (33974718330433/100000000000000 : ℝ)^6377 := by
    have hnat : (4416979009 : ℕ)^8425*100000000000000^6377 ≤ 33974718330433^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416979009 10000000000 33974718330433 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208489623/5000000000 : ℝ)^8425 ≤ (33974720738853/100000000000000 : ℝ)^6377 := by
    have hnat : (2208489623 : ℕ)^8425*100000000000000^6377 ≤ 33974720738853^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208489623 5000000000 33974720738853 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52828723/125000000 : ℝ), (4416979009/10000000000 : ℝ), (2208489623/5000000000 : ℝ)] ![(32050560915699/100000000000000 : ℝ), (33974718330433/100000000000000 : ℝ), (33974720738853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52828723/125000000 : ℝ)|^8425 ≤ (32050560915699/100000000000000 : ℝ)^6377
        have hw : |(52828723/125000000 : ℝ)|=(52828723/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416979009/10000000000 : ℝ)|^8425 ≤ (33974718330433/100000000000000 : ℝ)^6377
        have hw : |(4416979009/10000000000 : ℝ)|=(4416979009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208489623/5000000000 : ℝ)|^8425 ≤ (33974720738853/100000000000000 : ℝ)^6377
        have hw : |(2208489623/5000000000 : ℝ)|=(2208489623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1232_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12449/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59369/100000 : ℝ) ∧ (80079/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20831/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11467/100000 : ℝ) ^ (1053/256 : ℝ) ≤ (13528590434117091/100000000000000000000 : ℝ) := by
    have hpowers : (11467/100000 : ℝ)^1053 ≤ (13528590434117091/100000000000000000000 : ℝ)^256 := by
      have hnat : (11467 : ℕ)^1053*100000000000000000000^256 ≤ 13528590434117091^256*100000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11467 100000 13528590434117091 100000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11467/100000 : ℝ)) (X := (13528590434117091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14099/100000 : ℝ) ^ (1053/256 : ℝ) ≤ (15824945928902633/50000000000000000000 : ℝ) := by
    have hpowers : (14099/100000 : ℝ)^1053 ≤ (15824945928902633/50000000000000000000 : ℝ)^256 := by
      have hnat : (14099 : ℕ)^1053*50000000000000000000^256 ≤ 15824945928902633^256*100000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14099 100000 15824945928902633 50000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14099/100000 : ℝ)) (X := (15824945928902633/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013528590434117091/50000000000000000000 : ℝ) ≤ (1000065773306319/1000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (50013528590434117091/50000000000000000000 : ℝ)^256 ≤ (1000065773306319/1000000000000000 : ℝ)^1053 := by
      have hnat : (50013528590434117091 : ℕ)^256*1000000000000000^1053 ≤ 1000065773306319^1053*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013528590434117091 50000000000000000000 1000065773306319 1000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000065773306319/1000000000000000 : ℝ)) (X := (50013528590434117091/50000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045178482291922357/100000000000000000000 : ℝ) ≤ (312534317766353/312500000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (100045178482291922357/100000000000000000000 : ℝ)^256 ≤ (312534317766353/312500000000000 : ℝ)^1053 := by
      have hnat : (100045178482291922357 : ℕ)^256*312500000000000^1053 ≤ 312534317766353^1053*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045178482291922357 100000000000000000000 312534317766353 312500000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312534317766353/312500000000000 : ℝ)) (X := (100045178482291922357/100000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015824945928902633/25000000000000000000 : ℝ) ≤ (5000769301991701/5000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (25015824945928902633/25000000000000000000 : ℝ)^256 ≤ (5000769301991701/5000000000000000 : ℝ)^1053 := by
      have hnat : (25015824945928902633 : ℕ)^256*5000000000000000^1053 ≤ 5000769301991701^1053*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015824945928902633 25000000000000000000 5000769301991701 5000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000769301991701/5000000000000000 : ℝ)) (X := (25015824945928902633/25000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13528590434117091/100000000000000000000 : ℝ) ≤ ((6577907551645061269/6580000000000000000 : ℝ)+2*(220217730053/131600000000000 : ℝ)*(11467/100000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (6577907551645061269/6580000000000000000 : ℝ)+2*(220217730053/131600000000000 : ℝ)*(11467/100000 : ℝ)=(1000065773306319/1000000000000000 : ℝ) by norm_num, show 1+2*(13528590434117091/100000000000000000000 : ℝ)=(50013528590434117091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15824945928902633/50000000000000000000 : ℝ)+(13528590434117091/100000000000000000000 : ℝ) ≤ ((6577907551645061269/6580000000000000000 : ℝ)+(220217730053/131600000000000 : ℝ)*((14099/100000 : ℝ)+(11467/100000 : ℝ)))^(1053/256 : ℝ) := by
    rw [show (6577907551645061269/6580000000000000000 : ℝ)+(220217730053/131600000000000 : ℝ)*((14099/100000 : ℝ)+(11467/100000 : ℝ))=(312534317766353/312500000000000 : ℝ) by norm_num, show 1+(15824945928902633/50000000000000000000 : ℝ)+(13528590434117091/100000000000000000000 : ℝ)=(100045178482291922357/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15824945928902633/50000000000000000000 : ℝ) ≤ ((6577907551645061269/6580000000000000000 : ℝ)+2*(220217730053/131600000000000 : ℝ)*(14099/100000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (6577907551645061269/6580000000000000000 : ℝ)+2*(220217730053/131600000000000 : ℝ)*(14099/100000 : ℝ)=(5000769301991701/5000000000000000 : ℝ) by norm_num, show 1+2*(15824945928902633/50000000000000000000 : ℝ)=(25015824945928902633/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6577907551645061269/6580000000000000000 : ℝ)*(X 1 0+X 2 0)+(220217730053/131600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (6577907551645061269/6580000000000000000 : ℝ)) (alpha := (220217730053/131600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6577907551645061269/6580000000000000000 : ℝ)*(X 0 1+X 2 1)+(220217730053/131600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (6577907551645061269/6580000000000000000 : ℝ)) (alpha := (220217730053/131600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6577907551645061269/6580000000000000000 : ℝ)*(X 0 2+X 1 2)+(220217730053/131600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (6577907551645061269/6580000000000000000 : ℝ)) (alpha := (220217730053/131600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1000283041/5000000000 : ℝ)*X 0 0+(671874367/1250000000 : ℝ)*X 0 1+(5374995133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296722563/10000000000 : ℝ)*X 1 0+(-1053463851/5000000000 : ℝ)*X 1 1+(2687497767/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529672409/1000000000 : ℝ)*X 2 0+(5374995239/10000000000 : ℝ)*X 2 1+(-65841439/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4458778013/10000000000 : ℝ)*X 0 0+(4300882517/10000000000 : ℝ)*X 0 1+(2150440627/5000000000 : ℝ)*X 0 2+(4458778013/10000000000 : ℝ)*X 1 0+(4300882517/10000000000 : ℝ)*X 1 1+(2150440627/5000000000 : ℝ)*X 1 2+(4458778013/10000000000 : ℝ)*X 2 0+(4300882517/10000000000 : ℝ)*X 2 1+(2150440627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-562492271/2500000000 : ℝ)*X 0 0+(264109043/500000000 : ℝ)*X 0 1+(2641090443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((335135359/625000000 : ℝ)*X 1 0+(-1071846803/5000000000 : ℝ)*X 1 1+(5282180839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362165711/10000000000 : ℝ)*X 2 0+(5282180849/10000000000 : ℝ)*X 2 1+(-2143693637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((424512083/1000000000 : ℝ)*X 0 0+(550961293/1250000000 : ℝ)*X 0 1+(137740321/312500000 : ℝ)*X 0 2+(424512083/1000000000 : ℝ)*X 1 0+(550961293/1250000000 : ℝ)*X 1 1+(137740321/312500000 : ℝ)*X 1 2+(424512083/1000000000 : ℝ)*X 2 0+(550961293/1250000000 : ℝ)*X 2 1+(137740321/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2197717273/10000000000 : ℝ)*X 0 0+(2609445057/5000000000 : ℝ)*X 0 1+(336538037/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289942363/10000000000 : ℝ)*X 1 0+(-1051525543/5000000000 : ℝ)*X 1 1+(538460853/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((330621397/625000000 : ℝ)*X 2 0+(336538039/625000000 : ℝ)*X 2 1+(-2103050973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((112015877/250000000 : ℝ)*X 0 0+(4289812767/10000000000 : ℝ)*X 0 1+(4289812841/10000000000 : ℝ)*X 0 2+(112015877/250000000 : ℝ)*X 1 0+(4289812767/10000000000 : ℝ)*X 1 1+(4289812841/10000000000 : ℝ)*X 1 2+(112015877/250000000 : ℝ)*X 2 0+(4289812767/10000000000 : ℝ)*X 2 1+(4289812841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-513270731/2500000000 : ℝ)*X 0 0+(5437070807/10000000000 : ℝ)*X 0 1+(52741047/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683928827/5000000000 : ℝ)*X 1 0+(-429367383/2000000000 : ℝ)*X 1 1+(5274104959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367857809/10000000000 : ℝ)*X 2 0+(527410477/1000000000 : ℝ)*X 2 1+(-13417731/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((52828723/125000000 : ℝ)*X 0 0+(4416979009/10000000000 : ℝ)*X 0 1+(2208489623/5000000000 : ℝ)*X 0 2+(52828723/125000000 : ℝ)*X 1 0+(4416979009/10000000000 : ℝ)*X 1 1+(2208489623/5000000000 : ℝ)*X 1 2+(52828723/125000000 : ℝ)*X 2 0+(4416979009/10000000000 : ℝ)*X 2 1+(2208489623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12449/20000 : ℝ) ≤ (-914183915705685377418283318047/1468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3012527/10000000000000 : ℝ)*(lower0) + (457341/800000000000 : ℝ)*(lower2) + (16205573/20000000000000 : ℝ)*(lower4) + (1042183/50000000000000 : ℝ)*(lower5) + (1997389713241951/50000000000000 : ℝ)*(major0) + (1997389713241951/50000000000000 : ℝ)*(major1) + (62418428538811/1562500000000 : ℝ)*(major2) + (2718695687/100000000000000 : ℝ)*(sp1) + (228592061/6250000000000 : ℝ)*(sp2) + (671103494466669/12500000000000 : ℝ)*(sp4) + (1073765047407533/20000000000000 : ℝ)*(sp5) + (671103037282547/12500000000000 : ℝ)*(sp6) + (2641470011347261/100000000000000 : ℝ)*(sp7) + (832227197/10000000000000 : ℝ)*(sp15) + (264147833361923/10000000000000 : ℝ)*(f.failure) + (671103494466669/12500000000000 : ℝ)*(f.sum) + (36503040415101/6580000000000000000000000000 : ℝ)*base66 + (3182266409797104181/329000000000000000000000000000000 : ℝ)*base68 + (250387685255956693/20562500000000000000000000000000 : ℝ)*base69 + (32939842223729895819/329000000000000000000000000000000 : ℝ)*base71 + (142699847528141/6580000000000000000000000000 : ℝ)*base74 + (310692297067894193/20562500000000000000000000000000 : ℝ)*base75 + (110988292391148189/1000000000000000000000000000000 : ℝ)*base78 + (14598132212851811/1000000000000000000000000000000 : ℝ)*base79 + (51808136613/10000000000000000000000000 : ℝ)*base82 + (1568217/250000000000000000000 : ℝ)*base89 + (1568217/250000000000000000000 : ℝ)*base91 + (3431783/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59369/100000 : ℝ) ≤ (97666439825204608532841228032253/164500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (557859/6250000000000 : ℝ)*(upper0) + (143432769/50000000000000 : ℝ)*(lower1) + (129033377/10000000000000 : ℝ)*(upper4) + (2030210683651807/50000000000000 : ℝ)*(major0) + (2030210683651807/50000000000000 : ℝ)*(major1) + (2030210683651807/50000000000000 : ℝ)*(major2) + (13540360609361/250000000000 : ℝ)*(sp0) + (2708035880148549/50000000000000 : ℝ)*(sp1) + (5416108551876111/100000000000000 : ℝ)*(sp2) + (671212178430267/25000000000000 : ℝ)*(sp3) + (60693471071/100000000000000 : ℝ)*(sp6) + (17105112421/50000000000000 : ℝ)*(sp7) + (25001602781/100000000000000 : ℝ)*(sp8) + (97485050083/100000000000000 : ℝ)*(sp9) + (268488292394591/10000000000000 : ℝ)*(f.failure) + (2708084622673591/50000000000000 : ℝ)*(f.sum) + (7443454140781/3290000000000000000000000000 : ℝ)*base65 + (4369513742664113083/329000000000000000000000000000000 : ℝ)*base67 + (2541380297974113083/329000000000000000000000000000000 : ℝ)*base69 + (3775318091503113083/329000000000000000000000000000000 : ℝ)*base71 + (63968335033471/3290000000000000000000000000 : ℝ)*base73 + (2336588072644113083/329000000000000000000000000000000 : ℝ)*base75 + (315069748231113083/329000000000000000000000000000000 : ℝ)*base77 + (9593905638618113083/329000000000000000000000000000000 : ℝ)*base79 + (8377412727881/3290000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (159789/250000000000000000000 : ℝ)*base89 + (159789/250000000000000000000 : ℝ)*base91 + (159789/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80079/100000 : ℝ) ≤ (263468738724492697504929487616193/329000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79614377/100000000000000 : ℝ)*(lower3) + (13076651/50000000000000 : ℝ)*(upper4) + (4002419/50000000000000 : ℝ)*(lower5) + (1131830253768229/25000000000000 : ℝ)*(major0) + (1131830253768229/25000000000000 : ℝ)*(major1) + (4527321015072917/100000000000000 : ℝ)*(major2) + (1073325147/50000000000000 : ℝ)*(sp0) + (46047213399/100000000000000 : ℝ)*(sp1) + (94388788391/100000000000000 : ℝ)*(sp2) + (41588297647/100000000000000 : ℝ)*(sp3) + (1508583450801847/25000000000000 : ℝ)*(sp8) + (6034289902644283/100000000000000 : ℝ)*(sp9) + (1508560390267323/25000000000000 : ℝ)*(sp10) + (2993570597489533/100000000000000 : ℝ)*(sp11) + (149680609289359/5000000000000 : ℝ)*(f.failure) + (3017167974928841/50000000000000 : ℝ)*(f.sum) + (48104889350891/13160000000000000000000000000 : ℝ)*base66 + (1134005520336135101/164500000000000000000000000000000 : ℝ)*base67 + (3153607150232951673/658000000000000000000000000000000 : ℝ)*base69 + (1683214355333364899/164500000000000000000000000000000 : ℝ)*base72 + (28776187877309/13160000000000000000000000000 : ℝ)*base73 + (4810584554468951673/658000000000000000000000000000000 : ℝ)*base75 + (2764891586475027399/164500000000000000000000000000000 : ℝ)*base78 + (617443270434027399/164500000000000000000000000000000 : ℝ)*base80 + (3044087891561/822500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2867261/125000000000000000000 : ℝ)*base89 + (2867261/125000000000000000000 : ℝ)*base91 + (1617261/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-20831/25000 : ℝ) ≤ (-137063801265002999905610942029149/164500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68891659/25000000000000 : ℝ)*(upper3) + (28171881/100000000000000 : ℝ)*(lower4) + (96882299/25000000000000 : ℝ)*(upper5) + (4562778659847493/100000000000000 : ℝ)*(major0) + (4562778659847493/100000000000000 : ℝ)*(major1) + (2281389329923747/50000000000000 : ℝ)*(major2) + (31207075577/100000000000000 : ℝ)*(sp4) + (87817410561/50000000000000 : ℝ)*(sp5) + (392217202623/100000000000000 : ℝ)*(sp6) + (61227168973/25000000000000 : ℝ)*(sp7) + (767030249571271/12500000000000 : ℝ)*(sp12) + (6136097568824623/100000000000000 : ℝ)*(sp13) + (3067940493221561/50000000000000 : ℝ)*(sp14) + (754203256821299/25000000000000 : ℝ)*(sp15) + (2946345640587/97656250000 : ℝ)*(f.failure) + (383517075227859/6250000000000 : ℝ)*(f.sum) + (21506360043689/13160000000000000000000000000 : ℝ)*base66 + (8827697837423851383/658000000000000000000000000000000 : ℝ)*base68 + (1259795053706720057/329000000000000000000000000000000 : ℝ)*base70 + (8977910553139851383/658000000000000000000000000000000 : ℝ)*base72 + (8388463292289/13160000000000000000000000000 : ℝ)*base74 + (1348820944596279943/329000000000000000000000000000000 : ℝ)*base75 + (6779120849820501383/658000000000000000000000000000000 : ℝ)*base78 + (5334409356644501383/658000000000000000000000000000000 : ℝ)*base80 + (3858428610891/6580000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (424043/39062500000000000000 : ℝ)*base89 + (424043/39062500000000000000 : ℝ)*base91 + (16709/19531250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1232_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59369/100000 : ℝ) else (80079/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20831/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1232_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1232_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59369/100000 : ℝ) else (80079/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20831/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1232_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59369/100000 : ℝ) else (80079/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20831/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1232_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

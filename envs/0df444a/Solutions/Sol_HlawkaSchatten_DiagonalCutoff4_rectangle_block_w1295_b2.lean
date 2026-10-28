-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1295_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:38.169089+00:00
-- url     : https://prove2.me/submissions/2a1dae70-b52c-4c3c-934b-e7a58659c4a6

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
theorem support_rectangle_w1295_s6_0 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2085275601/10000000000 : ℝ)*x 0 + (2707582717/5000000000 : ℝ)*x 1 + (5243015389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085275601/10000000000 : ℝ)^4255 ≤ (6343896909219/50000000000000 : ℝ)^3231 := by
    have hnat : (2085275601 : ℕ)^4255*50000000000000^3231 ≤ 6343896909219^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085275601 10000000000 6343896909219 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707582717/5000000000 : ℝ)^4255 ≤ (5573081261753/12500000000000 : ℝ)^3231 := by
    have hnat : (2707582717 : ℕ)^4255*12500000000000^3231 ≤ 5573081261753^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707582717 5000000000 5573081261753 12500000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243015389/10000000000 : ℝ)^4255 ≤ (42727556070987/100000000000000 : ℝ)^3231 := by
    have hnat : (5243015389 : ℕ)^4255*100000000000000^3231 ≤ 42727556070987^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243015389 10000000000 42727556070987 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2085275601/10000000000 : ℝ), (2707582717/5000000000 : ℝ), (5243015389/10000000000 : ℝ)] ![(6343896909219/50000000000000 : ℝ), (5573081261753/12500000000000 : ℝ), (42727556070987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2085275601/10000000000 : ℝ)|^4255 ≤ (6343896909219/50000000000000 : ℝ)^3231
        have hw : |(-2085275601/10000000000 : ℝ)|=(2085275601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707582717/5000000000 : ℝ)|^4255 ≤ (5573081261753/12500000000000 : ℝ)^3231
        have hw : |(2707582717/5000000000 : ℝ)|=(2707582717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243015389/10000000000 : ℝ)|^4255 ≤ (42727556070987/100000000000000 : ℝ)^3231
        have hw : |(5243015389/10000000000 : ℝ)|=(5243015389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s6_1 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349762187/10000000000 : ℝ)*x 0 + (-2173027519/10000000000 : ℝ)*x 1 + (5243015389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349762187/10000000000 : ℝ)^4255 ≤ (21938432629881/50000000000000 : ℝ)^3231 := by
    have hnat : (5349762187 : ℕ)^4255*50000000000000^3231 ≤ 21938432629881^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349762187 10000000000 21938432629881 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173027519/10000000000 : ℝ)^4255 ≤ (2679115730331/20000000000000 : ℝ)^3231 := by
    have hnat : (2173027519 : ℕ)^4255*20000000000000^3231 ≤ 2679115730331^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173027519 10000000000 2679115730331 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243015389/10000000000 : ℝ)^4255 ≤ (42727556070987/100000000000000 : ℝ)^3231 := by
    have hnat : (5243015389 : ℕ)^4255*100000000000000^3231 ≤ 42727556070987^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243015389 10000000000 42727556070987 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349762187/10000000000 : ℝ), (-2173027519/10000000000 : ℝ), (5243015389/10000000000 : ℝ)] ![(21938432629881/50000000000000 : ℝ), (2679115730331/20000000000000 : ℝ), (42727556070987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349762187/10000000000 : ℝ)|^4255 ≤ (21938432629881/50000000000000 : ℝ)^3231
        have hw : |(5349762187/10000000000 : ℝ)|=(5349762187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173027519/10000000000 : ℝ)|^4255 ≤ (2679115730331/20000000000000 : ℝ)^3231
        have hw : |(-2173027519/10000000000 : ℝ)|=(2173027519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243015389/10000000000 : ℝ)|^4255 ≤ (42727556070987/100000000000000 : ℝ)^3231
        have hw : |(5243015389/10000000000 : ℝ)|=(5243015389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s6_2 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337440547/2500000000 : ℝ)*x 0 + (1310753847/2500000000 : ℝ)*x 1 + (-2173027519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337440547/2500000000 : ℝ)^4255 ≤ (43876865270563/100000000000000 : ℝ)^3231 := by
    have hnat : (1337440547 : ℕ)^4255*100000000000000^3231 ≤ 43876865270563^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337440547 2500000000 43876865270563 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310753847/2500000000 : ℝ)^4255 ≤ (21363778030127/50000000000000 : ℝ)^3231 := by
    have hnat : (1310753847 : ℕ)^4255*50000000000000^3231 ≤ 21363778030127^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310753847 2500000000 21363778030127 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173027519/10000000000 : ℝ)^4255 ≤ (2679115730331/20000000000000 : ℝ)^3231 := by
    have hnat : (2173027519 : ℕ)^4255*20000000000000^3231 ≤ 2679115730331^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173027519 10000000000 2679115730331 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337440547/2500000000 : ℝ), (1310753847/2500000000 : ℝ), (-2173027519/10000000000 : ℝ)] ![(43876865270563/100000000000000 : ℝ), (21363778030127/50000000000000 : ℝ), (2679115730331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337440547/2500000000 : ℝ)|^4255 ≤ (43876865270563/100000000000000 : ℝ)^3231
        have hw : |(1337440547/2500000000 : ℝ)|=(1337440547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310753847/2500000000 : ℝ)|^4255 ≤ (21363778030127/50000000000000 : ℝ)^3231
        have hw : |(1310753847/2500000000 : ℝ)|=(1310753847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173027519/10000000000 : ℝ)|^4255 ≤ (2679115730331/20000000000000 : ℝ)^3231
        have hw : |(-2173027519/10000000000 : ℝ)|=(2173027519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s6_3 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339056347/10000000000 : ℝ)*x 0 + (833079863/2000000000 : ℝ)*x 1 + (2259807057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339056347/10000000000 : ℝ)^4255 ≤ (33302364681611/100000000000000 : ℝ)^3231 := by
    have hnat : (4339056347 : ℕ)^4255*100000000000000^3231 ≤ 33302364681611^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339056347 10000000000 33302364681611 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833079863/2000000000 : ℝ)^4255 ≤ (15779183351643/50000000000000 : ℝ)^3231 := by
    have hnat : (833079863 : ℕ)^4255*50000000000000^3231 ≤ 15779183351643^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833079863 2000000000 15779183351643 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259807057/5000000000 : ℝ)^4255 ≤ (8784817148261/25000000000000 : ℝ)^3231 := by
    have hnat : (2259807057 : ℕ)^4255*25000000000000^3231 ≤ 8784817148261^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259807057 5000000000 8784817148261 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339056347/10000000000 : ℝ), (833079863/2000000000 : ℝ), (2259807057/5000000000 : ℝ)] ![(33302364681611/100000000000000 : ℝ), (15779183351643/50000000000000 : ℝ), (8784817148261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339056347/10000000000 : ℝ)|^4255 ≤ (33302364681611/100000000000000 : ℝ)^3231
        have hw : |(4339056347/10000000000 : ℝ)|=(4339056347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833079863/2000000000 : ℝ)|^4255 ≤ (15779183351643/50000000000000 : ℝ)^3231
        have hw : |(833079863/2000000000 : ℝ)|=(833079863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259807057/5000000000 : ℝ)|^4255 ≤ (8784817148261/25000000000000 : ℝ)^3231
        have hw : |(2259807057/5000000000 : ℝ)|=(2259807057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s6_4 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-130330511/625000000 : ℝ)*x 0 + (5243629789/10000000000 : ℝ)*x 1 + (5414547977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130330511/625000000 : ℝ)^4255 ≤ (3171973644929/25000000000000 : ℝ)^3231 := by
    have hnat : (130330511 : ℕ)^4255*25000000000000^3231 ≤ 3171973644929^3231*625000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130330511 625000000 3171973644929 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243629789/10000000000 : ℝ)^4255 ≤ (4273415006879/10000000000000 : ℝ)^3231 := by
    have hnat : (5243629789 : ℕ)^4255*10000000000000^3231 ≤ 4273415006879^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243629789 10000000000 4273415006879 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414547977/10000000000 : ℝ)^4255 ≤ (22288977666253/50000000000000 : ℝ)^3231 := by
    have hnat : (5414547977 : ℕ)^4255*50000000000000^3231 ≤ 22288977666253^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414547977 10000000000 22288977666253 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130330511/625000000 : ℝ), (5243629789/10000000000 : ℝ), (5414547977/10000000000 : ℝ)] ![(3171973644929/25000000000000 : ℝ), (4273415006879/10000000000000 : ℝ), (22288977666253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130330511/625000000 : ℝ)|^4255 ≤ (3171973644929/25000000000000 : ℝ)^3231
        have hw : |(-130330511/625000000 : ℝ)|=(130330511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243629789/10000000000 : ℝ)|^4255 ≤ (4273415006879/10000000000000 : ℝ)^3231
        have hw : |(5243629789/10000000000 : ℝ)|=(5243629789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414547977/10000000000 : ℝ)|^4255 ≤ (22288977666253/50000000000000 : ℝ)^3231
        have hw : |(5414547977/10000000000 : ℝ)|=(5414547977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s6_5 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165802209/312500000 : ℝ)*x 0 + (-2001494893/10000000000 : ℝ)*x 1 + (1353636997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165802209/312500000 : ℝ)^4255 ≤ (5425157048961/12500000000000 : ℝ)^3231 := by
    have hnat : (165802209 : ℕ)^4255*12500000000000^3231 ≤ 5425157048961^3231*312500000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165802209 312500000 5425157048961 12500000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001494893/10000000000 : ℝ)^4255 ≤ (2404157628581/20000000000000 : ℝ)^3231 := by
    have hnat : (2001494893 : ℕ)^4255*20000000000000^3231 ≤ 2404157628581^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001494893 10000000000 2404157628581 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353636997/2500000000 : ℝ)^4255 ≤ (44577955451771/100000000000000 : ℝ)^3231 := by
    have hnat : (1353636997 : ℕ)^4255*100000000000000^3231 ≤ 44577955451771^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353636997 2500000000 44577955451771 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165802209/312500000 : ℝ), (-2001494893/10000000000 : ℝ), (1353636997/2500000000 : ℝ)] ![(5425157048961/12500000000000 : ℝ), (2404157628581/20000000000000 : ℝ), (44577955451771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165802209/312500000 : ℝ)|^4255 ≤ (5425157048961/12500000000000 : ℝ)^3231
        have hw : |(165802209/312500000 : ℝ)|=(165802209/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2001494893/10000000000 : ℝ)|^4255 ≤ (2404157628581/20000000000000 : ℝ)^3231
        have hw : |(-2001494893/10000000000 : ℝ)|=(2001494893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353636997/2500000000 : ℝ)|^4255 ≤ (44577955451771/100000000000000 : ℝ)^3231
        have hw : |(1353636997/2500000000 : ℝ)|=(1353636997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s6_6 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106113413/200000000 : ℝ)*x 0 + (2707274003/5000000000 : ℝ)*x 1 + (-50037373/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106113413/200000000 : ℝ)^4255 ≤ (1736050239293/4000000000000 : ℝ)^3231 := by
    have hnat : (106113413 : ℕ)^4255*4000000000000^3231 ≤ 1736050239293^3231*200000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106113413 200000000 1736050239293 4000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707274003/5000000000 : ℝ)^4255 ≤ (11144488911733/25000000000000 : ℝ)^3231 := by
    have hnat : (2707274003 : ℕ)^4255*25000000000000^3231 ≤ 11144488911733^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707274003 5000000000 11144488911733 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50037373/250000000 : ℝ)^4255 ≤ (6010394178229/50000000000000 : ℝ)^3231 := by
    have hnat : (50037373 : ℕ)^4255*50000000000000^3231 ≤ 6010394178229^3231*250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50037373 250000000 6010394178229 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106113413/200000000 : ℝ), (2707274003/5000000000 : ℝ), (-50037373/250000000 : ℝ)] ![(1736050239293/4000000000000 : ℝ), (11144488911733/25000000000000 : ℝ), (6010394178229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106113413/200000000 : ℝ)|^4255 ≤ (1736050239293/4000000000000 : ℝ)^3231
        have hw : |(106113413/200000000 : ℝ)|=(106113413/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707274003/5000000000 : ℝ)|^4255 ≤ (11144488911733/25000000000000 : ℝ)^3231
        have hw : |(2707274003/5000000000 : ℝ)|=(2707274003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50037373/250000000 : ℝ)|^4255 ≤ (6010394178229/50000000000000 : ℝ)^3231
        have hw : |(-50037373/250000000 : ℝ)|=(50037373/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s6_7 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173563299/400000000 : ℝ)*x 0 + (903670011/2000000000 : ℝ)*x 1 + (416666991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173563299/400000000 : ℝ)^4255 ≤ (6660525753959/20000000000000 : ℝ)^3231 := by
    have hnat : (173563299 : ℕ)^4255*20000000000000^3231 ≤ 6660525753959^3231*400000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173563299 400000000 6660525753959 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903670011/2000000000 : ℝ)^4255 ≤ (1756316328657/5000000000000 : ℝ)^3231 := by
    have hnat : (903670011 : ℕ)^4255*5000000000000^3231 ≤ 1756316328657^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903670011 2000000000 1756316328657 5000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416666991/1000000000 : ℝ)^4255 ≤ (31571044641069/100000000000000 : ℝ)^3231 := by
    have hnat : (416666991 : ℕ)^4255*100000000000000^3231 ≤ 31571044641069^3231*1000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416666991 1000000000 31571044641069 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173563299/400000000 : ℝ), (903670011/2000000000 : ℝ), (416666991/1000000000 : ℝ)] ![(6660525753959/20000000000000 : ℝ), (1756316328657/5000000000000 : ℝ), (31571044641069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173563299/400000000 : ℝ)|^4255 ≤ (6660525753959/20000000000000 : ℝ)^3231
        have hw : |(173563299/400000000 : ℝ)|=(173563299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903670011/2000000000 : ℝ)|^4255 ≤ (1756316328657/5000000000000 : ℝ)^3231
        have hw : |(903670011/2000000000 : ℝ)|=(903670011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416666991/1000000000 : ℝ)|^4255 ≤ (31571044641069/100000000000000 : ℝ)^3231
        have hw : |(416666991/1000000000 : ℝ)|=(416666991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1295_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11033/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14677/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5511/50000 : ℝ) ^ (2127/512 : ℝ) ≤ (5250920037553241/50000000000000000000 : ℝ) := by
    have hpowers : (5511/50000 : ℝ)^2127 ≤ (5250920037553241/50000000000000000000 : ℝ)^512 := by
      have hnat : (5511 : ℕ)^2127*50000000000000000000^512 ≤ 5250920037553241^512*50000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5511 50000 5250920037553241 50000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5511/50000 : ℝ)) (X := (5250920037553241/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hpowhi : (459/3125 : ℝ) ^ (2127/512 : ℝ) ≤ (34619086007272747/100000000000000000000 : ℝ) := by
    have hpowers : (459/3125 : ℝ)^2127 ≤ (34619086007272747/100000000000000000000 : ℝ)^512 := by
      have hnat : (459 : ℕ)^2127*100000000000000000000^512 ≤ 34619086007272747^512*3125^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 3125 34619086007272747 100000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/3125 : ℝ)) (X := (34619086007272747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005250920037553241/25000000000000000000 : ℝ) ≤ (2500126387245407/2500000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (25005250920037553241/25000000000000000000 : ℝ)^512 ≤ (2500126387245407/2500000000000000 : ℝ)^2127 := by
      have hnat : (25005250920037553241 : ℕ)^512*2500000000000000^2127 ≤ 2500126387245407^2127*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005250920037553241 25000000000000000000 2500126387245407 2500000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500126387245407/2500000000000000 : ℝ)) (X := (25005250920037553241/25000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045120926082379229/100000000000000000000 : ℝ) ≤ (10001085940662079/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (100045120926082379229/100000000000000000000 : ℝ)^512 ≤ (10001085940662079/10000000000000000 : ℝ)^2127 := by
      have hnat : (100045120926082379229 : ℕ)^512*10000000000000000^2127 ≤ 10001085940662079^2127*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045120926082379229 100000000000000000000 10001085940662079 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001085940662079/10000000000000000 : ℝ)) (X := (100045120926082379229/100000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034619086007272747/50000000000000000000 : ℝ) ≤ (1000166633234253/1000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (50034619086007272747/50000000000000000000 : ℝ)^512 ≤ (1000166633234253/1000000000000000 : ℝ)^2127 := by
      have hnat : (50034619086007272747 : ℕ)^512*1000000000000000^2127 ≤ 1000166633234253^2127*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034619086007272747 50000000000000000000 1000166633234253 1000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000166633234253/1000000000000000 : ℝ)) (X := (50034619086007272747/50000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5250920037553241/50000000000000000000 : ℝ) ≤ ((3054088265696898867/3055000000000000000 : ℝ)+2*(580391680451/366600000000000 : ℝ)*(5511/50000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (3054088265696898867/3055000000000000000 : ℝ)+2*(580391680451/366600000000000 : ℝ)*(5511/50000 : ℝ)=(2500126387245407/2500000000000000 : ℝ) by norm_num, show 1+2*(5250920037553241/50000000000000000000 : ℝ)=(25005250920037553241/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34619086007272747/100000000000000000000 : ℝ)+(5250920037553241/50000000000000000000 : ℝ) ≤ ((3054088265696898867/3055000000000000000 : ℝ)+(580391680451/366600000000000 : ℝ)*((459/3125 : ℝ)+(5511/50000 : ℝ)))^(2127/512 : ℝ) := by
    rw [show (3054088265696898867/3055000000000000000 : ℝ)+(580391680451/366600000000000 : ℝ)*((459/3125 : ℝ)+(5511/50000 : ℝ))=(10001085940662079/10000000000000000 : ℝ) by norm_num, show 1+(34619086007272747/100000000000000000000 : ℝ)+(5250920037553241/50000000000000000000 : ℝ)=(100045120926082379229/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34619086007272747/100000000000000000000 : ℝ) ≤ ((3054088265696898867/3055000000000000000 : ℝ)+2*(580391680451/366600000000000 : ℝ)*(459/3125 : ℝ))^(2127/512 : ℝ) := by
    rw [show (3054088265696898867/3055000000000000000 : ℝ)+2*(580391680451/366600000000000 : ℝ)*(459/3125 : ℝ)=(1000166633234253/1000000000000000 : ℝ) by norm_num, show 1+2*(34619086007272747/100000000000000000000 : ℝ)=(50034619086007272747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3054088265696898867/3055000000000000000 : ℝ)*(X 1 0+X 2 0)+(580391680451/366600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (3054088265696898867/3055000000000000000 : ℝ)) (alpha := (580391680451/366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3054088265696898867/3055000000000000000 : ℝ)*(X 0 1+X 2 1)+(580391680451/366600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (3054088265696898867/3055000000000000000 : ℝ)) (alpha := (580391680451/366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3054088265696898867/3055000000000000000 : ℝ)*(X 0 2+X 1 2)+(580391680451/366600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (3054088265696898867/3055000000000000000 : ℝ)) (alpha := (580391680451/366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2085275601/10000000000 : ℝ)*X 0 0+(2707582717/5000000000 : ℝ)*X 0 1+(5243015389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349762187/10000000000 : ℝ)*X 1 0+(-2173027519/10000000000 : ℝ)*X 1 1+(5243015389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337440547/2500000000 : ℝ)*X 2 0+(1310753847/2500000000 : ℝ)*X 2 1+(-2173027519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339056347/10000000000 : ℝ)*X 0 0+(833079863/2000000000 : ℝ)*X 0 1+(2259807057/5000000000 : ℝ)*X 0 2+(4339056347/10000000000 : ℝ)*X 1 0+(833079863/2000000000 : ℝ)*X 1 1+(2259807057/5000000000 : ℝ)*X 1 2+(4339056347/10000000000 : ℝ)*X 2 0+(833079863/2000000000 : ℝ)*X 2 1+(2259807057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-130330511/625000000 : ℝ)*X 0 0+(5243629789/10000000000 : ℝ)*X 0 1+(5414547977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165802209/312500000 : ℝ)*X 1 0+(-2001494893/10000000000 : ℝ)*X 1 1+(1353636997/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106113413/200000000 : ℝ)*X 2 0+(2707274003/5000000000 : ℝ)*X 2 1+(-50037373/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173563299/400000000 : ℝ)*X 0 0+(903670011/2000000000 : ℝ)*X 0 1+(416666991/1000000000 : ℝ)*X 0 2+(173563299/400000000 : ℝ)*X 1 0+(903670011/2000000000 : ℝ)*X 1 1+(416666991/1000000000 : ℝ)*X 1 2+(173563299/400000000 : ℝ)*X 2 0+(903670011/2000000000 : ℝ)*X 2 1+(416666991/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82443737716142262385449651/9546875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1654175063/100000000000000 : ℝ)*(base19) + (308421261/20000000000000 : ℝ)*(base23) + (7566877/12500000000000 : ℝ)*(lower2) + (218216363/100000000000000 : ℝ)*(upper3) + (67160677/50000000000000 : ℝ)*(upper5) + (4316066516177061/100000000000000 : ℝ)*(major0) + (4316066516177061/100000000000000 : ℝ)*(major1) + (2158033258088531/50000000000000 : ℝ)*(major2) + (5808920737631089/100000000000000 : ℝ)*(sp0) + (5808952235883509/100000000000000 : ℝ)*(sp1) + (5808952347952267/100000000000000 : ℝ)*(sp2) + (352895174134557/12500000000000 : ℝ)*(sp3) + (33152427483/100000000000000 : ℝ)*(sp4) + (8730681579/50000000000000 : ℝ)*(sp7) + (1411589427219807/50000000000000 : ℝ)*(f.failure) + (1452238472514643/25000000000000 : ℝ)*(f.sum) + (86736154288627/36660000000000000000000000000 : ℝ)*base66 + (3428778543911419661/916500000000000000000000000000000 : ℝ)*base67 + (1765295627741056877/152750000000000000000000000000000 : ℝ)*base69 + (1166099128148419661/916500000000000000000000000000000 : ℝ)*base71 + (21869780699467/36660000000000000000000000000 : ℝ)*base74 + (1161988195796306877/152750000000000000000000000000000 : ℝ)*base75 + (1532419075074214887/305500000000000000000000000000000 : ℝ)*base77 + (3443754331710214887/305500000000000000000000000000000 : ℝ)*base79 + (30603840122173/6110000000000000000000000000 : ℝ)*base82 + (6162369/500000000000000000000 : ℝ)*base89 + (6162369/500000000000000000000 : ℝ)*base91 + (1162369/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (199356949986907445652499597/19093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1588436741/100000000000000 : ℝ)*(base19) + (1856581579/100000000000000 : ℝ)*(base23) + (164187093/100000000000000 : ℝ)*(upper3) + (36310193/25000000000000 : ℝ)*(lower4) + (2665943/1562500000000 : ℝ)*(upper5) + (1086780172850603/25000000000000 : ℝ)*(major0) + (1086780172850603/25000000000000 : ℝ)*(major1) + (1086780172850603/25000000000000 : ℝ)*(major2) + (8316477139/25000000000000 : ℝ)*(sp1) + (1505370647/4000000000000 : ℝ)*(sp2) + (1170149871668771/20000000000000 : ℝ)*(sp4) + (5850714503998559/100000000000000 : ℝ)*(sp5) + (5850709867496101/100000000000000 : ℝ)*(sp6) + (2843491676429189/100000000000000 : ℝ)*(sp7) + (2843491676429189/100000000000000 : ℝ)*(f.failure) + (1170149871668771/20000000000000 : ℝ)*(f.sum) + (56978271039769/9165000000000000000000000000 : ℝ)*base66 + (3116821987512975403/229125000000000000000000000000000 : ℝ)*base67 + (2615729660006100403/229125000000000000000000000000000 : ℝ)*base69 + (1505839220923350403/229125000000000000000000000000000 : ℝ)*base71 + (13286128913323/4582500000000000000000000000 : ℝ)*base73 + (959189999963024597/229125000000000000000000000000000 : ℝ)*base76 + (168112158131100403/229125000000000000000000000000000 : ℝ)*base77 + (1808030450780100403/229125000000000000000000000000000 : ℝ)*base79 + (23436405211519/9165000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (731237/1000000000000000000000 : ℝ)*base90 + (731237/1000000000000000000000 : ℝ)*base92 + (731237/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1295_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1295_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1295_s7_0 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-521321387/2500000000 : ℝ)*x 0 + (5415067743/10000000000 : ℝ)*x 1 + (5243106659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521321387/2500000000 : ℝ)^4255 ≤ (2537574704399/20000000000000 : ℝ)^3231 := by
    have hnat : (521321387 : ℕ)^4255*20000000000000^3231 ≤ 2537574704399^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521321387 2500000000 2537574704399 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415067743/10000000000 : ℝ)^4255 ≤ (22291795432889/50000000000000 : ℝ)^3231 := by
    have hnat : (5415067743 : ℕ)^4255*50000000000000^3231 ≤ 22291795432889^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415067743 10000000000 22291795432889 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243106659/10000000000 : ℝ)^4255 ≤ (21364267801659/50000000000000 : ℝ)^3231 := by
    have hnat : (5243106659 : ℕ)^4255*50000000000000^3231 ≤ 21364267801659^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243106659 10000000000 21364267801659 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-521321387/2500000000 : ℝ), (5415067743/10000000000 : ℝ), (5243106659/10000000000 : ℝ)] ![(2537574704399/20000000000000 : ℝ), (22291795432889/50000000000000 : ℝ), (21364267801659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-521321387/2500000000 : ℝ)|^4255 ≤ (2537574704399/20000000000000 : ℝ)^3231
        have hw : |(-521321387/2500000000 : ℝ)|=(521321387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415067743/10000000000 : ℝ)|^4255 ≤ (22291795432889/50000000000000 : ℝ)^3231
        have hw : |(5415067743/10000000000 : ℝ)|=(5415067743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243106659/10000000000 : ℝ)|^4255 ≤ (21364267801659/50000000000000 : ℝ)^3231
        have hw : |(5243106659/10000000000 : ℝ)|=(5243106659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s7_1 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069947539/2000000000 : ℝ)*x 0 + (-1086469769/5000000000 : ℝ)*x 1 + (5243106589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069947539/2000000000 : ℝ)^4255 ≤ (43876600722011/100000000000000 : ℝ)^3231 := by
    have hnat : (1069947539 : ℕ)^4255*100000000000000^3231 ≤ 43876600722011^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069947539 2000000000 43876600722011 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086469769/5000000000 : ℝ)^4255 ≤ (13394864410343/100000000000000 : ℝ)^3231 := by
    have hnat : (1086469769 : ℕ)^4255*100000000000000^3231 ≤ 13394864410343^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086469769 5000000000 13394864410343 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243106589/10000000000 : ℝ)^4255 ≤ (42728534852059/100000000000000 : ℝ)^3231 := by
    have hnat : (5243106589 : ℕ)^4255*100000000000000^3231 ≤ 42728534852059^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243106589 10000000000 42728534852059 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069947539/2000000000 : ℝ), (-1086469769/5000000000 : ℝ), (5243106589/10000000000 : ℝ)] ![(43876600722011/100000000000000 : ℝ), (13394864410343/100000000000000 : ℝ), (42728534852059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069947539/2000000000 : ℝ)|^4255 ≤ (43876600722011/100000000000000 : ℝ)^3231
        have hw : |(1069947539/2000000000 : ℝ)|=(1069947539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1086469769/5000000000 : ℝ)|^4255 ≤ (13394864410343/100000000000000 : ℝ)^3231
        have hw : |(-1086469769/5000000000 : ℝ)|=(1086469769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243106589/10000000000 : ℝ)|^4255 ≤ (42728534852059/100000000000000 : ℝ)^3231
        have hw : |(5243106589/10000000000 : ℝ)|=(5243106589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s7_2 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337434399/2500000000 : ℝ)*x 0 + (5243107897/10000000000 : ℝ)*x 1 + (-108646897/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337434399/2500000000 : ℝ)^4255 ≤ (21938299826357/50000000000000 : ℝ)^3231 := by
    have hnat : (1337434399 : ℕ)^4255*50000000000000^3231 ≤ 21938299826357^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337434399 2500000000 21938299826357 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243107897/10000000000 : ℝ)^4255 ≤ (42728548889879/100000000000000 : ℝ)^3231 := by
    have hnat : (5243107897 : ℕ)^4255*100000000000000^3231 ≤ 42728548889879^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243107897 10000000000 42728548889879 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108646897/500000000 : ℝ)^4255 ≤ (6697425718827/50000000000000 : ℝ)^3231 := by
    have hnat : (108646897 : ℕ)^4255*50000000000000^3231 ≤ 6697425718827^3231*500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108646897 500000000 6697425718827 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337434399/2500000000 : ℝ), (5243107897/10000000000 : ℝ), (-108646897/500000000 : ℝ)] ![(21938299826357/50000000000000 : ℝ), (42728548889879/100000000000000 : ℝ), (6697425718827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337434399/2500000000 : ℝ)|^4255 ≤ (21938299826357/50000000000000 : ℝ)^3231
        have hw : |(1337434399/2500000000 : ℝ)|=(1337434399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243107897/10000000000 : ℝ)|^4255 ≤ (42728548889879/100000000000000 : ℝ)^3231
        have hw : |(5243107897/10000000000 : ℝ)|=(5243107897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108646897/500000000 : ℝ)|^4255 ≤ (6697425718827/50000000000000 : ℝ)^3231
        have hw : |(-108646897/500000000 : ℝ)|=(108646897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s7_3 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339064133/10000000000 : ℝ)*x 0 + (2082796699/5000000000 : ℝ)*x 1 + (4519417299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339064133/10000000000 : ℝ)^4255 ≤ (16651221689191/50000000000000 : ℝ)^3231 := by
    have hnat : (4339064133 : ℕ)^4255*50000000000000^3231 ≤ 16651221689191^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339064133 10000000000 16651221689191 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082796699/5000000000 : ℝ)^4255 ≤ (3156030317513/10000000000000 : ℝ)^3231 := by
    have hnat : (2082796699 : ℕ)^4255*10000000000000^3231 ≤ 3156030317513^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082796699 5000000000 3156030317513 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519417299/10000000000 : ℝ)^4255 ≤ (17568626717377/50000000000000 : ℝ)^3231 := by
    have hnat : (4519417299 : ℕ)^4255*50000000000000^3231 ≤ 17568626717377^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519417299 10000000000 17568626717377 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339064133/10000000000 : ℝ), (2082796699/5000000000 : ℝ), (4519417299/10000000000 : ℝ)] ![(16651221689191/50000000000000 : ℝ), (3156030317513/10000000000000 : ℝ), (17568626717377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339064133/10000000000 : ℝ)|^4255 ≤ (16651221689191/50000000000000 : ℝ)^3231
        have hw : |(4339064133/10000000000 : ℝ)|=(4339064133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082796699/5000000000 : ℝ)|^4255 ≤ (3156030317513/10000000000000 : ℝ)^3231
        have hw : |(2082796699/5000000000 : ℝ)|=(2082796699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519417299/10000000000 : ℝ)|^4255 ≤ (17568626717377/50000000000000 : ℝ)^3231
        have hw : |(4519417299/10000000000 : ℝ)|=(4519417299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s7_4 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1042648953/5000000000 : ℝ)*x 0 + (163866253/312500000 : ℝ)*x 1 + (5414451393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042648953/5000000000 : ℝ)^4255 ≤ (6343986272319/50000000000000 : ℝ)^3231 := by
    have hnat : (1042648953 : ℕ)^4255*50000000000000^3231 ≤ 6343986272319^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042648953 5000000000 6343986272319 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163866253/312500000 : ℝ)^4255 ≤ (10683779825483/25000000000000 : ℝ)^3231 := by
    have hnat : (163866253 : ℕ)^4255*25000000000000^3231 ≤ 10683779825483^3231*312500000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163866253 312500000 10683779825483 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414451393/10000000000 : ℝ)^4255 ≤ (5572113518109/12500000000000 : ℝ)^3231 := by
    have hnat : (5414451393 : ℕ)^4255*12500000000000^3231 ≤ 5572113518109^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414451393 10000000000 5572113518109 12500000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1042648953/5000000000 : ℝ), (163866253/312500000 : ℝ), (5414451393/10000000000 : ℝ)] ![(6343986272319/50000000000000 : ℝ), (10683779825483/25000000000000 : ℝ), (5572113518109/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1042648953/5000000000 : ℝ)|^4255 ≤ (6343986272319/50000000000000 : ℝ)^3231
        have hw : |(-1042648953/5000000000 : ℝ)|=(1042648953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163866253/312500000 : ℝ)|^4255 ≤ (10683779825483/25000000000000 : ℝ)^3231
        have hw : |(163866253/312500000 : ℝ)|=(163866253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414451393/10000000000 : ℝ)|^4255 ≤ (5572113518109/12500000000000 : ℝ)^3231
        have hw : |(5414451393/10000000000 : ℝ)|=(5414451393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s7_5 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305694863/10000000000 : ℝ)*x 0 + (-1954682/9765625 : ℝ)*x 1 + (5414451401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305694863/10000000000 : ℝ)^4255 ≤ (4340151682193/10000000000000 : ℝ)^3231 := by
    have hnat : (5305694863 : ℕ)^4255*10000000000000^3231 ≤ 4340151682193^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305694863 10000000000 4340151682193 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1954682/9765625 : ℝ)^4255 ≤ (601078746609/5000000000000 : ℝ)^3231 := by
    have hnat : (1954682 : ℕ)^4255*5000000000000^3231 ≤ 601078746609^3231*9765625^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954682 9765625 601078746609 5000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414451401/10000000000 : ℝ)^4255 ≤ (4457690823161/10000000000000 : ℝ)^3231 := by
    have hnat : (5414451401 : ℕ)^4255*10000000000000^3231 ≤ 4457690823161^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414451401 10000000000 4457690823161 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305694863/10000000000 : ℝ), (-1954682/9765625 : ℝ), (5414451401/10000000000 : ℝ)] ![(4340151682193/10000000000000 : ℝ), (601078746609/5000000000000 : ℝ), (4457690823161/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305694863/10000000000 : ℝ)|^4255 ≤ (4340151682193/10000000000000 : ℝ)^3231
        have hw : |(5305694863/10000000000 : ℝ)|=(5305694863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1954682/9765625 : ℝ)|^4255 ≤ (601078746609/5000000000000 : ℝ)^3231
        have hw : |(-1954682/9765625 : ℝ)|=(1954682/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414451401/10000000000 : ℝ)|^4255 ≤ (4457690823161/10000000000000 : ℝ)^3231
        have hw : |(5414451401/10000000000 : ℝ)|=(5414451401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s7_6 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652847439/5000000000 : ℝ)*x 0 + (1353612847/2500000000 : ℝ)*x 1 + (-400318873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652847439/5000000000 : ℝ)^4255 ≤ (271259481147/625000000000 : ℝ)^3231 := by
    have hnat : (2652847439 : ℕ)^4255*625000000000^3231 ≤ 271259481147^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652847439 5000000000 271259481147 625000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353612847/2500000000 : ℝ)^4255 ≤ (44576908090661/100000000000000 : ℝ)^3231 := by
    have hnat : (1353612847 : ℕ)^4255*100000000000000^3231 ≤ 44576908090661^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353612847 2500000000 44576908090661 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400318873/2000000000 : ℝ)^4255 ≤ (3005393727113/25000000000000 : ℝ)^3231 := by
    have hnat : (400318873 : ℕ)^4255*25000000000000^3231 ≤ 3005393727113^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400318873 2000000000 3005393727113 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652847439/5000000000 : ℝ), (1353612847/2500000000 : ℝ), (-400318873/2000000000 : ℝ)] ![(271259481147/625000000000 : ℝ), (44576908090661/100000000000000 : ℝ), (3005393727113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652847439/5000000000 : ℝ)|^4255 ≤ (271259481147/625000000000 : ℝ)^3231
        have hw : |(2652847439/5000000000 : ℝ)|=(2652847439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353612847/2500000000 : ℝ)|^4255 ≤ (44576908090661/100000000000000 : ℝ)^3231
        have hw : |(1353612847/2500000000 : ℝ)|=(1353612847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400318873/2000000000 : ℝ)|^4255 ≤ (3005393727113/25000000000000 : ℝ)^3231
        have hw : |(-400318873/2000000000 : ℝ)|=(400318873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s7_7 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173563567/400000000 : ℝ)*x 0 + (1129539219/2500000000 : ℝ)*x 1 + (166674453/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173563567/400000000 : ℝ)^4255 ≤ (33302696489979/100000000000000 : ℝ)^3231 := by
    have hnat : (173563567 : ℕ)^4255*100000000000000^3231 ≤ 33302696489979^3231*400000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173563567 400000000 33302696489979 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129539219/2500000000 : ℝ)^4255 ≤ (35124348818383/100000000000000 : ℝ)^3231 := by
    have hnat : (1129539219 : ℕ)^4255*100000000000000^3231 ≤ 35124348818383^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129539219 2500000000 35124348818383 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166674453/400000000 : ℝ)^4255 ≤ (789323866931/2500000000000 : ℝ)^3231 := by
    have hnat : (166674453 : ℕ)^4255*2500000000000^3231 ≤ 789323866931^3231*400000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166674453 400000000 789323866931 2500000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173563567/400000000 : ℝ), (1129539219/2500000000 : ℝ), (166674453/400000000 : ℝ)] ![(33302696489979/100000000000000 : ℝ), (35124348818383/100000000000000 : ℝ), (789323866931/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173563567/400000000 : ℝ)|^4255 ≤ (33302696489979/100000000000000 : ℝ)^3231
        have hw : |(173563567/400000000 : ℝ)|=(173563567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129539219/2500000000 : ℝ)|^4255 ≤ (35124348818383/100000000000000 : ℝ)^3231
        have hw : |(1129539219/2500000000 : ℝ)|=(1129539219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166674453/400000000 : ℝ)|^4255 ≤ (789323866931/2500000000000 : ℝ)^3231
        have hw : |(166674453/400000000 : ℝ)|=(166674453/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1295_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2207/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (587/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11033/100000 : ℝ) ^ (2127/512 : ℝ) ≤ (2109089867466197/20000000000000000000 : ℝ) := by
    have hpowers : (11033/100000 : ℝ)^2127 ≤ (2109089867466197/20000000000000000000 : ℝ)^512 := by
      have hnat : (11033 : ℕ)^2127*20000000000000000000^512 ≤ 2109089867466197^512*100000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11033 100000 2109089867466197 20000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11033/100000 : ℝ)) (X := (2109089867466197/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14677/100000 : ℝ) ^ (2127/512 : ℝ) ≤ (17255753174938797/50000000000000000000 : ℝ) := by
    have hpowers : (14677/100000 : ℝ)^2127 ≤ (17255753174938797/50000000000000000000 : ℝ)^512 := by
      have hnat : (14677 : ℕ)^2127*50000000000000000000^512 ≤ 17255753174938797^512*100000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14677 100000 17255753174938797 50000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14677/100000 : ℝ)) (X := (17255753174938797/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002109089867466197/10000000000000000000 : ℝ) ≤ (2000101529624717/2000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (10002109089867466197/10000000000000000000 : ℝ)^512 ≤ (2000101529624717/2000000000000000 : ℝ)^2127 := by
      have hnat : (10002109089867466197 : ℕ)^512*2000000000000000^2127 ≤ 2000101529624717^2127*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002109089867466197 10000000000000000000 2000101529624717 2000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000101529624717/2000000000000000 : ℝ)) (X := (10002109089867466197/10000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045056955687208579/100000000000000000000 : ℝ) ≤ (10001084401328101/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (100045056955687208579/100000000000000000000 : ℝ)^512 ≤ (10001084401328101/10000000000000000 : ℝ)^2127 := by
      have hnat : (100045056955687208579 : ℕ)^512*10000000000000000^2127 ≤ 10001084401328101^2127*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045056955687208579 100000000000000000000 10001084401328101 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001084401328101/10000000000000000 : ℝ)) (X := (100045056955687208579/100000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017255753174938797/25000000000000000000 : ℝ) ≤ (10001661154532617/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (25017255753174938797/25000000000000000000 : ℝ)^512 ≤ (10001661154532617/10000000000000000 : ℝ)^2127 := by
      have hnat : (25017255753174938797 : ℕ)^512*10000000000000000^2127 ≤ 10001661154532617^2127*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017255753174938797 25000000000000000000 10001661154532617 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001661154532617/10000000000000000 : ℝ)) (X := (25017255753174938797/25000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2109089867466197/20000000000000000000 : ℝ) ≤ ((9107280808387873421/9110000000000000000 : ℝ)+2*(144188301129/91100000000000 : ℝ)*(11033/100000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (9107280808387873421/9110000000000000000 : ℝ)+2*(144188301129/91100000000000 : ℝ)*(11033/100000 : ℝ)=(2000101529624717/2000000000000000 : ℝ) by norm_num, show 1+2*(2109089867466197/20000000000000000000 : ℝ)=(10002109089867466197/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17255753174938797/50000000000000000000 : ℝ)+(2109089867466197/20000000000000000000 : ℝ) ≤ ((9107280808387873421/9110000000000000000 : ℝ)+(144188301129/91100000000000 : ℝ)*((14677/100000 : ℝ)+(11033/100000 : ℝ)))^(2127/512 : ℝ) := by
    rw [show (9107280808387873421/9110000000000000000 : ℝ)+(144188301129/91100000000000 : ℝ)*((14677/100000 : ℝ)+(11033/100000 : ℝ))=(10001084401328101/10000000000000000 : ℝ) by norm_num, show 1+(17255753174938797/50000000000000000000 : ℝ)+(2109089867466197/20000000000000000000 : ℝ)=(100045056955687208579/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17255753174938797/50000000000000000000 : ℝ) ≤ ((9107280808387873421/9110000000000000000 : ℝ)+2*(144188301129/91100000000000 : ℝ)*(14677/100000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (9107280808387873421/9110000000000000000 : ℝ)+2*(144188301129/91100000000000 : ℝ)*(14677/100000 : ℝ)=(10001661154532617/10000000000000000 : ℝ) by norm_num, show 1+2*(17255753174938797/50000000000000000000 : ℝ)=(25017255753174938797/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9107280808387873421/9110000000000000000 : ℝ)*(X 1 0+X 2 0)+(144188301129/91100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (9107280808387873421/9110000000000000000 : ℝ)) (alpha := (144188301129/91100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9107280808387873421/9110000000000000000 : ℝ)*(X 0 1+X 2 1)+(144188301129/91100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (9107280808387873421/9110000000000000000 : ℝ)) (alpha := (144188301129/91100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9107280808387873421/9110000000000000000 : ℝ)*(X 0 2+X 1 2)+(144188301129/91100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (9107280808387873421/9110000000000000000 : ℝ)) (alpha := (144188301129/91100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-521321387/2500000000 : ℝ)*X 0 0+(5415067743/10000000000 : ℝ)*X 0 1+(5243106659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069947539/2000000000 : ℝ)*X 1 0+(-1086469769/5000000000 : ℝ)*X 1 1+(5243106589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337434399/2500000000 : ℝ)*X 2 0+(5243107897/10000000000 : ℝ)*X 2 1+(-108646897/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339064133/10000000000 : ℝ)*X 0 0+(2082796699/5000000000 : ℝ)*X 0 1+(4519417299/10000000000 : ℝ)*X 0 2+(4339064133/10000000000 : ℝ)*X 1 0+(2082796699/5000000000 : ℝ)*X 1 1+(4519417299/10000000000 : ℝ)*X 1 2+(4339064133/10000000000 : ℝ)*X 2 0+(2082796699/5000000000 : ℝ)*X 2 1+(4519417299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1042648953/5000000000 : ℝ)*X 0 0+(163866253/312500000 : ℝ)*X 0 1+(5414451393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305694863/10000000000 : ℝ)*X 1 0+(-1954682/9765625 : ℝ)*X 1 1+(5414451401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652847439/5000000000 : ℝ)*X 2 0+(1353612847/2500000000 : ℝ)*X 2 1+(-400318873/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173563567/400000000 : ℝ)*X 0 0+(1129539219/2500000000 : ℝ)*X 0 1+(166674453/400000000 : ℝ)*X 0 2+(173563567/400000000 : ℝ)*X 1 0+(1129539219/2500000000 : ℝ)*X 1 1+(166674453/400000000 : ℝ)*X 1 2+(173563567/400000000 : ℝ)*X 2 0+(1129539219/2500000000 : ℝ)*X 2 1+(166674453/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1549498290180145956216379737/227750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1903328123/100000000000000 : ℝ)*(base19) + (868058337/50000000000000 : ℝ)*(base23) + (151221627/100000000000000 : ℝ)*(lower2) + (31044153/4000000000000 : ℝ)*(upper5) + (2160424729927091/50000000000000 : ℝ)*(major0) + (2160424729927091/50000000000000 : ℝ)*(major1) + (540106182481773/12500000000000 : ℝ)*(major2) + (2907656854957449/50000000000000 : ℝ)*(sp0) + (5815362271246627/100000000000000 : ℝ)*(sp1) + (581538953486373/10000000000000 : ℝ)*(sp2) + (706572727379437/25000000000000 : ℝ)*(sp3) + (38780532753/50000000000000 : ℝ)*(sp4) + (13548202827/50000000000000 : ℝ)*(sp5) + (8256213351/50000000000000 : ℝ)*(sp7) + (56526148438889/2000000000000 : ℝ)*(f.failure) + (1453847817745101/25000000000000 : ℝ)*(f.sum) + (18769356965937/4555000000000000000000000000 : ℝ)*base65 + (2713075181599451689/455500000000000000000000000000000 : ℝ)*base68 + (1696090019124380433/113875000000000000000000000000000 : ℝ)*base69 + (2070714986151951689/455500000000000000000000000000000 : ℝ)*base72 + (11611476649583/4555000000000000000000000000 : ℝ)*base74 + (206685765951005433/113875000000000000000000000000000 : ℝ)*base75 + (2004206458136351689/455500000000000000000000000000000 : ℝ)*base78 + (4031063753177648311/455500000000000000000000000000000 : ℝ)*base79 + (921819549921/569375000000000000000000000 : ℝ)*base81 + (148663/20000000000000000000 : ℝ)*base89 + (148663/20000000000000000000 : ℝ)*base91 + (251337/20000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (297813669405066982079758281/28468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231782369/12500000000000 : ℝ)*(base19) + (2019120097/100000000000000 : ℝ)*(base23) + (320469199/50000000000000 : ℝ)*(lower1) + (53506687/25000000000000 : ℝ)*(upper3) + (6764223/10000000000000 : ℝ)*(lower4) + (112497141/50000000000000 : ℝ)*(upper5) + (543981628829113/12500000000000 : ℝ)*(major0) + (543981628829113/12500000000000 : ℝ)*(major1) + (543981628829113/12500000000000 : ℝ)*(major2) + (1253599739/50000000000000 : ℝ)*(sp2) + (5857118569463893/100000000000000 : ℝ)*(sp4) + (2928558357602471/50000000000000 : ℝ)*(sp5) + (5857114043144319/100000000000000 : ℝ)*(sp6) + (1423293571549737/50000000000000 : ℝ)*(sp7) + (1423293571549737/50000000000000 : ℝ)*(f.failure) + (5857118569463893/100000000000000 : ℝ)*(f.sum) + (3204471627639/1138750000000000000000000000 : ℝ)*base65 + (531344125732405573/113875000000000000000000000000000 : ℝ)*base67 + (1421035944255280573/113875000000000000000000000000000 : ℝ)*base69 + (665644890859405573/113875000000000000000000000000000 : ℝ)*base71 + (159994012209/71171875000000000000000000 : ℝ)*base73 + (2393431604797594427/113875000000000000000000000000000 : ℝ)*base76 + (927596105626405573/113875000000000000000000000000000 : ℝ)*base77 + (1137221892493655573/113875000000000000000000000000000 : ℝ)*base79 + (2861570229891/4555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1885321/500000000000000000000 : ℝ)*base90 + (1885321/500000000000000000000 : ℝ)*base92 + (1885321/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1295_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2207/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (587/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1295_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1295_s8_0 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208528607/1000000000 : ℝ)*x 0 + (2707525291/5000000000 : ℝ)*x 1 + (5243123607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208528607/1000000000 : ℝ)^4255 ≤ (12687877704693/100000000000000 : ℝ)^3231 := by
    have hnat : (208528607 : ℕ)^4255*100000000000000^3231 ≤ 12687877704693^3231*1000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208528607 1000000000 12687877704693 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707525291/5000000000 : ℝ)^4255 ≤ (356667238367/800000000000 : ℝ)^3231 := by
    have hnat : (2707525291 : ℕ)^4255*800000000000^3231 ≤ 356667238367^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707525291 5000000000 356667238367 800000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243123607/10000000000 : ℝ)^4255 ≤ (42728717494063/100000000000000 : ℝ)^3231 := by
    have hnat : (5243123607 : ℕ)^4255*100000000000000^3231 ≤ 42728717494063^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243123607 10000000000 42728717494063 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208528607/1000000000 : ℝ), (2707525291/5000000000 : ℝ), (5243123607/10000000000 : ℝ)] ![(12687877704693/100000000000000 : ℝ), (356667238367/800000000000 : ℝ), (42728717494063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208528607/1000000000 : ℝ)|^4255 ≤ (12687877704693/100000000000000 : ℝ)^3231
        have hw : |(-208528607/1000000000 : ℝ)|=(208528607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707525291/5000000000 : ℝ)|^4255 ≤ (356667238367/800000000000 : ℝ)^3231
        have hw : |(2707525291/5000000000 : ℝ)|=(2707525291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243123607/10000000000 : ℝ)|^4255 ≤ (42728717494063/100000000000000 : ℝ)^3231
        have hw : |(5243123607/10000000000 : ℝ)|=(5243123607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s8_1 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349733697/10000000000 : ℝ)*x 0 + (-2172922047/10000000000 : ℝ)*x 1 + (1310780961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349733697/10000000000 : ℝ)^4255 ≤ (8775311507941/20000000000000 : ℝ)^3231 := by
    have hnat : (5349733697 : ℕ)^4255*20000000000000^3231 ≤ 8775311507941^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349733697 10000000000 8775311507941 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2172922047/10000000000 : ℝ)^4255 ≤ (33486806043/250000000000 : ℝ)^3231 := by
    have hnat : (2172922047 : ℕ)^4255*250000000000^3231 ≤ 33486806043^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172922047 10000000000 33486806043 250000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310780961/2500000000 : ℝ)^4255 ≤ (8545744007523/20000000000000 : ℝ)^3231 := by
    have hnat : (1310780961 : ℕ)^4255*20000000000000^3231 ≤ 8545744007523^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310780961 2500000000 8545744007523 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349733697/10000000000 : ℝ), (-2172922047/10000000000 : ℝ), (1310780961/2500000000 : ℝ)] ![(8775311507941/20000000000000 : ℝ), (33486806043/250000000000 : ℝ), (8545744007523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349733697/10000000000 : ℝ)|^4255 ≤ (8775311507941/20000000000000 : ℝ)^3231
        have hw : |(5349733697/10000000000 : ℝ)|=(5349733697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2172922047/10000000000 : ℝ)|^4255 ≤ (33486806043/250000000000 : ℝ)^3231
        have hw : |(-2172922047/10000000000 : ℝ)|=(2172922047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310780961/2500000000 : ℝ)|^4255 ≤ (8545744007523/20000000000000 : ℝ)^3231
        have hw : |(1310780961/2500000000 : ℝ)|=(1310780961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s8_2 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213989319/400000000 : ℝ)*x 0 + (1310781207/2500000000 : ℝ)*x 1 + (-1086460853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213989319/400000000 : ℝ)^4255 ≤ (43876549741401/100000000000000 : ℝ)^3231 := by
    have hnat : (213989319 : ℕ)^4255*100000000000000^3231 ≤ 43876549741401^3231*400000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213989319 400000000 43876549741401 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310781207/2500000000 : ℝ)^4255 ≤ (10682182649547/25000000000000 : ℝ)^3231 := by
    have hnat : (1310781207 : ℕ)^4255*25000000000000^3231 ≤ 10682182649547^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310781207 2500000000 10682182649547 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086460853/5000000000 : ℝ)^4255 ≤ (6697359824471/50000000000000 : ℝ)^3231 := by
    have hnat : (1086460853 : ℕ)^4255*50000000000000^3231 ≤ 6697359824471^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086460853 5000000000 6697359824471 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213989319/400000000 : ℝ), (1310781207/2500000000 : ℝ), (-1086460853/5000000000 : ℝ)] ![(43876549741401/100000000000000 : ℝ), (10682182649547/25000000000000 : ℝ), (6697359824471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213989319/400000000 : ℝ)|^4255 ≤ (43876549741401/100000000000000 : ℝ)^3231
        have hw : |(213989319/400000000 : ℝ)|=(213989319/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310781207/2500000000 : ℝ)|^4255 ≤ (10682182649547/25000000000000 : ℝ)^3231
        have hw : |(1310781207/2500000000 : ℝ)|=(1310781207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086460853/5000000000 : ℝ)|^4255 ≤ (6697359824471/50000000000000 : ℝ)^3231
        have hw : |(-1086460853/5000000000 : ℝ)|=(1086460853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s8_3 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2169531741/5000000000 : ℝ)*x 0 + (833125689/2000000000 : ℝ)*x 1 + (4519383789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169531741/5000000000 : ℝ)^4255 ≤ (2081402299901/6250000000000 : ℝ)^3231 := by
    have hnat : (2169531741 : ℕ)^4255*6250000000000^3231 ≤ 2081402299901^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169531741 5000000000 2081402299901 6250000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833125689/2000000000 : ℝ)^4255 ≤ (31560652861193/100000000000000 : ℝ)^3231 := by
    have hnat : (833125689 : ℕ)^4255*100000000000000^3231 ≤ 31560652861193^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833125689 2000000000 31560652861193 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519383789/10000000000 : ℝ)^4255 ≤ (35136910333827/100000000000000 : ℝ)^3231 := by
    have hnat : (4519383789 : ℕ)^4255*100000000000000^3231 ≤ 35136910333827^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519383789 10000000000 35136910333827 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169531741/5000000000 : ℝ), (833125689/2000000000 : ℝ), (4519383789/10000000000 : ℝ)] ![(2081402299901/6250000000000 : ℝ), (31560652861193/100000000000000 : ℝ), (35136910333827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169531741/5000000000 : ℝ)|^4255 ≤ (2081402299901/6250000000000 : ℝ)^3231
        have hw : |(2169531741/5000000000 : ℝ)|=(2169531741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833125689/2000000000 : ℝ)|^4255 ≤ (31560652861193/100000000000000 : ℝ)^3231
        have hw : |(833125689/2000000000 : ℝ)|=(833125689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519383789/10000000000 : ℝ)|^4255 ≤ (35136910333827/100000000000000 : ℝ)^3231
        have hw : |(4519383789/10000000000 : ℝ)|=(4519383789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s8_4 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208529963/1000000000 : ℝ)*x 0 + (2621868249/5000000000 : ℝ)*x 1 + (2707216941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208529963/1000000000 : ℝ)^4255 ≤ (24781223357/195312500000 : ℝ)^3231 := by
    have hnat : (208529963 : ℕ)^4255*195312500000^3231 ≤ 24781223357^3231*1000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208529963 1000000000 24781223357 195312500000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621868249/5000000000 : ℝ)^4255 ≤ (42735295339373/100000000000000 : ℝ)^3231 := by
    have hnat : (2621868249 : ℕ)^4255*100000000000000^3231 ≤ 42735295339373^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621868249 5000000000 42735295339373 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707216941/5000000000 : ℝ)^4255 ≤ (4457671828691/10000000000000 : ℝ)^3231 := by
    have hnat : (2707216941 : ℕ)^4255*10000000000000^3231 ≤ 4457671828691^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707216941 5000000000 4457671828691 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208529963/1000000000 : ℝ), (2621868249/5000000000 : ℝ), (2707216941/5000000000 : ℝ)] ![(24781223357/195312500000 : ℝ), (42735295339373/100000000000000 : ℝ), (4457671828691/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208529963/1000000000 : ℝ)|^4255 ≤ (24781223357/195312500000 : ℝ)^3231
        have hw : |(-208529963/1000000000 : ℝ)|=(208529963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621868249/5000000000 : ℝ)|^4255 ≤ (42735295339373/100000000000000 : ℝ)^3231
        have hw : |(2621868249/5000000000 : ℝ)|=(2621868249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707216941/5000000000 : ℝ)|^4255 ≤ (4457671828691/10000000000000 : ℝ)^3231
        have hw : |(2707216941/5000000000 : ℝ)|=(2707216941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s8_5 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652849633/5000000000 : ℝ)*x 0 + (-2001612371/10000000000 : ℝ)*x 1 + (5414433893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652849633/5000000000 : ℝ)^4255 ≤ (10596085023/24414062500 : ℝ)^3231 := by
    have hnat : (2652849633 : ℕ)^4255*24414062500^3231 ≤ 10596085023^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652849633 5000000000 10596085023 24414062500 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001612371/10000000000 : ℝ)^4255 ≤ (12021717326743/100000000000000 : ℝ)^3231 := by
    have hnat : (2001612371 : ℕ)^4255*100000000000000^3231 ≤ 12021717326743^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001612371 10000000000 12021717326743 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414433893/10000000000 : ℝ)^4255 ≤ (22288359203087/50000000000000 : ℝ)^3231 := by
    have hnat : (5414433893 : ℕ)^4255*50000000000000^3231 ≤ 22288359203087^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414433893 10000000000 22288359203087 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652849633/5000000000 : ℝ), (-2001612371/10000000000 : ℝ), (5414433893/10000000000 : ℝ)] ![(10596085023/24414062500 : ℝ), (12021717326743/100000000000000 : ℝ), (22288359203087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652849633/5000000000 : ℝ)|^4255 ≤ (10596085023/24414062500 : ℝ)^3231
        have hw : |(2652849633/5000000000 : ℝ)|=(2652849633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2001612371/10000000000 : ℝ)|^4255 ≤ (12021717326743/100000000000000 : ℝ)^3231
        have hw : |(-2001612371/10000000000 : ℝ)|=(2001612371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414433893/10000000000 : ℝ)|^4255 ≤ (22288359203087/50000000000000 : ℝ)^3231
        have hw : |(5414433893/10000000000 : ℝ)|=(5414433893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s8_6 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652849631/5000000000 : ℝ)*x 0 + (2707216949/5000000000 : ℝ)*x 1 + (-2001612369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652849631/5000000000 : ℝ)^4255 ≤ (43401564211117/100000000000000 : ℝ)^3231 := by
    have hnat : (2652849631 : ℕ)^4255*100000000000000^3231 ≤ 43401564211117^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652849631 5000000000 43401564211117 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707216949/5000000000 : ℝ)^4255 ≤ (8915343692077/20000000000000 : ℝ)^3231 := by
    have hnat : (2707216949 : ℕ)^4255*20000000000000^3231 ≤ 8915343692077^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707216949 5000000000 8915343692077 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001612369/10000000000 : ℝ)^4255 ≤ (3005429327731/25000000000000 : ℝ)^3231 := by
    have hnat : (2001612369 : ℕ)^4255*25000000000000^3231 ≤ 3005429327731^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001612369 10000000000 3005429327731 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652849631/5000000000 : ℝ), (2707216949/5000000000 : ℝ), (-2001612369/10000000000 : ℝ)] ![(43401564211117/100000000000000 : ℝ), (8915343692077/20000000000000 : ℝ), (3005429327731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652849631/5000000000 : ℝ)|^4255 ≤ (43401564211117/100000000000000 : ℝ)^3231
        have hw : |(2652849631/5000000000 : ℝ)|=(2652849631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707216949/5000000000 : ℝ)|^4255 ≤ (8915343692077/20000000000000 : ℝ)^3231
        have hw : |(2707216949/5000000000 : ℝ)|=(2707216949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2001612369/10000000000 : ℝ)|^4255 ≤ (3005429327731/25000000000000 : ℝ)^3231
        have hw : |(-2001612369/10000000000 : ℝ)|=(2001612369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s8_7 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339090377/10000000000 : ℝ)*x 0 + (4518121847/10000000000 : ℝ)*x 1 + (4166896047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339090377/10000000000 : ℝ)^4255 ≤ (16651354319593/50000000000000 : ℝ)^3231 := by
    have hnat : (4339090377 : ℕ)^4255*50000000000000^3231 ≤ 16651354319593^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339090377 10000000000 16651354319593 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518121847/10000000000 : ℝ)^4255 ≤ (35123990196499/100000000000000 : ℝ)^3231 := by
    have hnat : (4518121847 : ℕ)^4255*100000000000000^3231 ≤ 35123990196499^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518121847 10000000000 35123990196499 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4166896047/10000000000 : ℝ)^4255 ≤ (6314660230797/20000000000000 : ℝ)^3231 := by
    have hnat : (4166896047 : ℕ)^4255*20000000000000^3231 ≤ 6314660230797^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166896047 10000000000 6314660230797 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339090377/10000000000 : ℝ), (4518121847/10000000000 : ℝ), (4166896047/10000000000 : ℝ)] ![(16651354319593/50000000000000 : ℝ), (35123990196499/100000000000000 : ℝ), (6314660230797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339090377/10000000000 : ℝ)|^4255 ≤ (16651354319593/50000000000000 : ℝ)^3231
        have hw : |(4339090377/10000000000 : ℝ)|=(4339090377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518121847/10000000000 : ℝ)|^4255 ≤ (35123990196499/100000000000000 : ℝ)^3231
        have hw : |(4518121847/10000000000 : ℝ)|=(4518121847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4166896047/10000000000 : ℝ)|^4255 ≤ (6314660230797/20000000000000 : ℝ)^3231
        have hw : |(4166896047/10000000000 : ℝ)|=(4166896047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1295_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2207/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2759/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7337/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2207/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2207/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2207/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2207/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2207/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2207/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (2207/20000 : ℝ) ^ (2127/512 : ℝ) ≤ (1055339304324599/10000000000000000000 : ℝ) := by
    have hpowers : (2207/20000 : ℝ)^2127 ≤ (1055339304324599/10000000000000000000 : ℝ)^512 := by
      have hnat : (2207 : ℕ)^2127*10000000000000000000^512 ≤ 1055339304324599^512*20000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2207 20000 1055339304324599 10000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2207/20000 : ℝ)) (X := (1055339304324599/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hpowhi : (587/4000 : ℝ) ^ (2127/512 : ℝ) ≤ (689839474320543/2000000000000000000 : ℝ) := by
    have hpowers : (587/4000 : ℝ)^2127 ≤ (689839474320543/2000000000000000000 : ℝ)^512 := by
      have hnat : (587 : ℕ)^2127*2000000000000000000^512 ≤ 689839474320543^512*4000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        587 4000 689839474320543 2000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (587/4000 : ℝ)) (X := (689839474320543/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001055339304324599/5000000000000000000 : ℝ) ≤ (10000508030495563/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (5001055339304324599/5000000000000000000 : ℝ)^512 ≤ (10000508030495563/10000000000000000 : ℝ)^2127 := by
      have hnat : (5001055339304324599 : ℕ)^512*10000000000000000^2127 ≤ 10000508030495563^2127*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001055339304324599 5000000000000000000 10000508030495563 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000508030495563/10000000000000000 : ℝ)) (X := (5001055339304324599/5000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002252268337963657/5000000000000000000 : ℝ) ≤ (10001084122461047/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (5002252268337963657/5000000000000000000 : ℝ)^512 ≤ (10001084122461047/10000000000000000 : ℝ)^2127 := by
      have hnat : (5002252268337963657 : ℕ)^512*10000000000000000^2127 ≤ 10001084122461047^2127*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002252268337963657 5000000000000000000 10001084122461047 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001084122461047/10000000000000000 : ℝ)) (X := (5002252268337963657/5000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000689839474320543/1000000000000000000 : ℝ) ≤ (10001660214426531/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (1000689839474320543/1000000000000000000 : ℝ)^512 ≤ (10001660214426531/10000000000000000 : ℝ)^2127 := by
      have hnat : (1000689839474320543 : ℕ)^512*10000000000000000^2127 ≤ 10001660214426531^2127*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000689839474320543 1000000000000000000 10001660214426531 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001660214426531/10000000000000000 : ℝ)) (X := (1000689839474320543/1000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1055339304324599/10000000000000000000 : ℝ) ≤ ((32490299001183587/32500000000000000 : ℝ)+2*(20574713053/13000000000000 : ℝ)*(2207/20000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (32490299001183587/32500000000000000 : ℝ)+2*(20574713053/13000000000000 : ℝ)*(2207/20000 : ℝ)=(10000508030495563/10000000000000000 : ℝ) by norm_num, show 1+2*(1055339304324599/10000000000000000000 : ℝ)=(5001055339304324599/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(689839474320543/2000000000000000000 : ℝ)+(1055339304324599/10000000000000000000 : ℝ) ≤ ((32490299001183587/32500000000000000 : ℝ)+(20574713053/13000000000000 : ℝ)*((587/4000 : ℝ)+(2207/20000 : ℝ)))^(2127/512 : ℝ) := by
    rw [show (32490299001183587/32500000000000000 : ℝ)+(20574713053/13000000000000 : ℝ)*((587/4000 : ℝ)+(2207/20000 : ℝ))=(10001084122461047/10000000000000000 : ℝ) by norm_num, show 1+(689839474320543/2000000000000000000 : ℝ)+(1055339304324599/10000000000000000000 : ℝ)=(5002252268337963657/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(689839474320543/2000000000000000000 : ℝ) ≤ ((32490299001183587/32500000000000000 : ℝ)+2*(20574713053/13000000000000 : ℝ)*(587/4000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (32490299001183587/32500000000000000 : ℝ)+2*(20574713053/13000000000000 : ℝ)*(587/4000 : ℝ)=(10001660214426531/10000000000000000 : ℝ) by norm_num, show 1+2*(689839474320543/2000000000000000000 : ℝ)=(1000689839474320543/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32490299001183587/32500000000000000 : ℝ)*(X 1 0+X 2 0)+(20574713053/13000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (2207/20000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (32490299001183587/32500000000000000 : ℝ)) (alpha := (20574713053/13000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32490299001183587/32500000000000000 : ℝ)*(X 0 1+X 2 1)+(20574713053/13000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (2207/20000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (32490299001183587/32500000000000000 : ℝ)) (alpha := (20574713053/13000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32490299001183587/32500000000000000 : ℝ)*(X 0 2+X 1 2)+(20574713053/13000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (2207/20000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (32490299001183587/32500000000000000 : ℝ)) (alpha := (20574713053/13000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-208528607/1000000000 : ℝ)*X 0 0+(2707525291/5000000000 : ℝ)*X 0 1+(5243123607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349733697/10000000000 : ℝ)*X 1 0+(-2172922047/10000000000 : ℝ)*X 1 1+(1310780961/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213989319/400000000 : ℝ)*X 2 0+(1310781207/2500000000 : ℝ)*X 2 1+(-1086460853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169531741/5000000000 : ℝ)*X 0 0+(833125689/2000000000 : ℝ)*X 0 1+(4519383789/10000000000 : ℝ)*X 0 2+(2169531741/5000000000 : ℝ)*X 1 0+(833125689/2000000000 : ℝ)*X 1 1+(4519383789/10000000000 : ℝ)*X 1 2+(2169531741/5000000000 : ℝ)*X 2 0+(833125689/2000000000 : ℝ)*X 2 1+(4519383789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208529963/1000000000 : ℝ)*X 0 0+(2621868249/5000000000 : ℝ)*X 0 1+(2707216941/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652849633/5000000000 : ℝ)*X 1 0+(-2001612371/10000000000 : ℝ)*X 1 1+(5414433893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652849631/5000000000 : ℝ)*X 2 0+(2707216949/5000000000 : ℝ)*X 2 1+(-2001612369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339090377/10000000000 : ℝ)*X 0 0+(4518121847/10000000000 : ℝ)*X 0 1+(4166896047/10000000000 : ℝ)*X 0 2+(4339090377/10000000000 : ℝ)*X 1 0+(4518121847/10000000000 : ℝ)*X 1 1+(4166896047/10000000000 : ℝ)*X 1 2+(4339090377/10000000000 : ℝ)*X 2 0+(4518121847/10000000000 : ℝ)*X 2 1+(4166896047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (677188095805919908058091/406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1357461/3125000000000 : ℝ)*(base8) + (185959033/25000000000000 : ℝ)*(base21) + (93840117/100000000000000 : ℝ)*(lower2) + (120078839/20000000000000 : ℝ)*(lower3) + (167886829/100000000000000 : ℝ)*(lower4) + (1080415900539427/25000000000000 : ℝ)*(major0) + (1080415900539427/25000000000000 : ℝ)*(major1) + (1080415900539427/25000000000000 : ℝ)*(major2) + (2908221360938677/50000000000000 : ℝ)*(sp0) + (5816487188828721/100000000000000 : ℝ)*(sp1) + (5816486444992589/100000000000000 : ℝ)*(sp2) + (1413414775401361/50000000000000 : ℝ)*(sp3) + (8884702523/20000000000000 : ℝ)*(sp4) + (1301139977/12500000000000 : ℝ)*(sp7) + (1413419979961269/50000000000000 : ℝ)*(f.failure) + (5816487188828721/100000000000000 : ℝ)*(f.sum) + (355085365539/40625000000000000000000000 : ℝ)*base65 + (3812958053387851/812500000000000000000000000000 : ℝ)*base68 + (5367732523012851/812500000000000000000000000000 : ℝ)*base70 + (4023420280200351/812500000000000000000000000000 : ℝ)*base72 + (67907025887/325000000000000000000000000 : ℝ)*base73 + (3158225073512851/812500000000000000000000000000 : ℝ)*base76 + (9149329004825351/812500000000000000000000000000 : ℝ)*base78 + (4716992186012851/812500000000000000000000000000 : ℝ)*base80 + (948727637969/162500000000000000000000000 : ℝ)*base82 + (1750123/500000000000000000000 : ℝ)*base89 + (1750123/500000000000000000000 : ℝ)*base91 + (1750123/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3510244548034993501687611/812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155688949/20000000000000 : ℝ)*(base19) + (26260207/3125000000000 : ℝ)*(base23) + (68585567/25000000000000 : ℝ)*(lower1) + (11132857/12500000000000 : ℝ)*(upper3) + (7553523/25000000000000 : ℝ)*(lower4) + (92487173/100000000000000 : ℝ)*(upper5) + (2176366835340851/50000000000000 : ℝ)*(major0) + (2176366835340851/50000000000000 : ℝ)*(major1) + (2176366835340851/50000000000000 : ℝ)*(major2) + (281709779/25000000000000 : ℝ)*(sp2) + (5858304019488239/100000000000000 : ℝ)*(sp4) + (5858303241043493/100000000000000 : ℝ)*(sp5) + (2929151026161249/50000000000000 : ℝ)*(sp6) + (711790794466279/25000000000000 : ℝ)*(sp7) + (711790794466279/25000000000000 : ℝ)*(f.failure) + (5858304019488239/100000000000000 : ℝ)*(f.sum) + (1543124250453/325000000000000000000000000 : ℝ)*base65 + (15172934803179963/1625000000000000000000000000000 : ℝ)*base68 + (23430167514179963/1625000000000000000000000000000 : ℝ)*base70 + (48480443771679963/1625000000000000000000000000000 : ℝ)*base72 + (736234594839/162500000000000000000000000 : ℝ)*base73 + (77898016502945037/1625000000000000000000000000000 : ℝ)*base75 + (11959333233429963/1625000000000000000000000000000 : ℝ)*base78 + (22308726573070037/1625000000000000000000000000000 : ℝ)*base79 + (2225585379947/325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (964793/250000000000000000000 : ℝ)*base89 + (964793/250000000000000000000 : ℝ)*base91 + (964793/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1295_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2207/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1295_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1295_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1295_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1295_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1295_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1295_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

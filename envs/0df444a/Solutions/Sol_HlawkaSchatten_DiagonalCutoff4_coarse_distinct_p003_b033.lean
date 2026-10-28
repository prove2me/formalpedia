-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:54:59.792183+00:00
-- url     : https://prove2.me/submissions/a057d564-82c1-45db-a4e3-a6ec02203bea

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c303077_s0_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-5588422173/10000000000 : ℝ)*x 0 + (469193519/1250000000 : ℝ)*x 1 + (362277667/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5588422173/10000000000 : ℝ)^33 ≤ (46389720234439/100000000000000 : ℝ)^25 := by
    have hnat : (5588422173 : ℕ)^33*100000000000000^25 ≤ 46389720234439^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588422173 10000000000 46389720234439 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469193519/1250000000 : ℝ)^33 ≤ (27432376256237/100000000000000 : ℝ)^25 := by
    have hnat : (469193519 : ℕ)^33*100000000000000^25 ≤ 27432376256237^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469193519 1250000000 27432376256237 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362277667/1000000000 : ℝ)^33 ≤ (26177903488877/100000000000000 : ℝ)^25 := by
    have hnat : (362277667 : ℕ)^33*100000000000000^25 ≤ 26177903488877^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362277667 1000000000 26177903488877 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5588422173/10000000000 : ℝ), (469193519/1250000000 : ℝ), (362277667/1000000000 : ℝ)] ![(46389720234439/100000000000000 : ℝ), (27432376256237/100000000000000 : ℝ), (26177903488877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5588422173/10000000000 : ℝ)|^33 ≤ (46389720234439/100000000000000 : ℝ)^25
        have hw : |(-5588422173/10000000000 : ℝ)|=(5588422173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469193519/1250000000 : ℝ)|^33 ≤ (27432376256237/100000000000000 : ℝ)^25
        have hw : |(469193519/1250000000 : ℝ)|=(469193519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362277667/1000000000 : ℝ)|^33 ≤ (26177903488877/100000000000000 : ℝ)^25
        have hw : |(362277667/1000000000 : ℝ)|=(362277667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4526309051/10000000000 : ℝ)*x 0 + (1366617239/2500000000 : ℝ)*x 1 + (-586849251/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4526309051/10000000000 : ℝ)^33 ≤ (35122251541461/100000000000000 : ℝ)^25 := by
    have hnat : (4526309051 : ℕ)^33*100000000000000^25 ≤ 35122251541461^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526309051 10000000000 35122251541461 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366617239/2500000000 : ℝ)^33 ≤ (45058122317267/100000000000000 : ℝ)^25 := by
    have hnat : (1366617239 : ℕ)^33*100000000000000^25 ≤ 45058122317267^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366617239 2500000000 45058122317267 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586849251/2000000000 : ℝ)^33 ≤ (19819626128699/100000000000000 : ℝ)^25 := by
    have hnat : (586849251 : ℕ)^33*100000000000000^25 ≤ 19819626128699^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586849251 2000000000 19819626128699 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4526309051/10000000000 : ℝ), (1366617239/2500000000 : ℝ), (-586849251/2000000000 : ℝ)] ![(35122251541461/100000000000000 : ℝ), (45058122317267/100000000000000 : ℝ), (19819626128699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4526309051/10000000000 : ℝ)|^33 ≤ (35122251541461/100000000000000 : ℝ)^25
        have hw : |(4526309051/10000000000 : ℝ)|=(4526309051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366617239/2500000000 : ℝ)|^33 ≤ (45058122317267/100000000000000 : ℝ)^25
        have hw : |(1366617239/2500000000 : ℝ)|=(1366617239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-586849251/2000000000 : ℝ)|^33 ≤ (19819626128699/100000000000000 : ℝ)^25
        have hw : |(-586849251/2000000000 : ℝ)|=(586849251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (132548341/625000000 : ℝ)*x 0 + (6823481663/10000000000 : ℝ)*x 1 + (919589377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132548341/625000000 : ℝ)^33 ≤ (3227843403039/25000000000000 : ℝ)^25 := by
    have hnat : (132548341 : ℕ)^33*25000000000000^25 ≤ 3227843403039^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132548341 625000000 3227843403039 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6823481663/10000000000 : ℝ)^33 ≤ (30189641952193/50000000000000 : ℝ)^25 := by
    have hnat : (6823481663 : ℕ)^33*50000000000000^25 ≤ 30189641952193^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6823481663 10000000000 30189641952193 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919589377/2500000000 : ℝ)^33 ≤ (6677335620243/25000000000000 : ℝ)^25 := by
    have hnat : (919589377 : ℕ)^33*25000000000000^25 ≤ 6677335620243^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919589377 2500000000 6677335620243 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132548341/625000000 : ℝ), (6823481663/10000000000 : ℝ), (919589377/2500000000 : ℝ)] ![(3227843403039/25000000000000 : ℝ), (30189641952193/50000000000000 : ℝ), (6677335620243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132548341/625000000 : ℝ)|^33 ≤ (3227843403039/25000000000000 : ℝ)^25
        have hw : |(132548341/625000000 : ℝ)|=(132548341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6823481663/10000000000 : ℝ)|^33 ≤ (30189641952193/50000000000000 : ℝ)^25
        have hw : |(6823481663/10000000000 : ℝ)|=(6823481663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(919589377/2500000000 : ℝ)|^33 ≤ (6677335620243/25000000000000 : ℝ)^25
        have hw : |(919589377/2500000000 : ℝ)|=(919589377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-5752434173/10000000000 : ℝ)*x 0 + (3388262117/10000000000 : ℝ)*x 1 + (3795745311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5752434173/10000000000 : ℝ)^33 ≤ (6024405565079/12500000000000 : ℝ)^25 := by
    have hnat : (5752434173 : ℕ)^33*12500000000000^25 ≤ 6024405565079^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5752434173 10000000000 6024405565079 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3388262117/10000000000 : ℝ)^33 ≤ (479291399299/2000000000000 : ℝ)^25 := by
    have hnat : (3388262117 : ℕ)^33*2000000000000^25 ≤ 479291399299^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3388262117 10000000000 479291399299 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3795745311/10000000000 : ℝ)^33 ≤ (27840185505339/100000000000000 : ℝ)^25 := by
    have hnat : (3795745311 : ℕ)^33*100000000000000^25 ≤ 27840185505339^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3795745311 10000000000 27840185505339 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5752434173/10000000000 : ℝ), (3388262117/10000000000 : ℝ), (3795745311/10000000000 : ℝ)] ![(6024405565079/12500000000000 : ℝ), (479291399299/2000000000000 : ℝ), (27840185505339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5752434173/10000000000 : ℝ)|^33 ≤ (6024405565079/12500000000000 : ℝ)^25
        have hw : |(-5752434173/10000000000 : ℝ)|=(5752434173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3388262117/10000000000 : ℝ)|^33 ≤ (479291399299/2000000000000 : ℝ)^25
        have hw : |(3388262117/10000000000 : ℝ)|=(3388262117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3795745311/10000000000 : ℝ)|^33 ≤ (27840185505339/100000000000000 : ℝ)^25
        have hw : |(3795745311/10000000000 : ℝ)|=(3795745311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (47247173/125000000 : ℝ)*x 0 + (-1942318909/10000000000 : ℝ)*x 1 + (6860955703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47247173/125000000 : ℝ)^33 ≤ (27685659652927/100000000000000 : ℝ)^25 := by
    have hnat : (47247173 : ℕ)^33*100000000000000^25 ≤ 27685659652927^25*125000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47247173 125000000 27685659652927 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942318909/10000000000 : ℝ)^33 ≤ (11496962382497/100000000000000 : ℝ)^25 := by
    have hnat : (1942318909 : ℕ)^33*100000000000000^25 ≤ 11496962382497^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942318909 10000000000 11496962382497 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6860955703/10000000000 : ℝ)^33 ≤ (3040868897641/5000000000000 : ℝ)^25 := by
    have hnat : (6860955703 : ℕ)^33*5000000000000^25 ≤ 3040868897641^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6860955703 10000000000 3040868897641 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(47247173/125000000 : ℝ), (-1942318909/10000000000 : ℝ), (6860955703/10000000000 : ℝ)] ![(27685659652927/100000000000000 : ℝ), (11496962382497/100000000000000 : ℝ), (3040868897641/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(47247173/125000000 : ℝ)|^33 ≤ (27685659652927/100000000000000 : ℝ)^25
        have hw : |(47247173/125000000 : ℝ)|=(47247173/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942318909/10000000000 : ℝ)|^33 ≤ (11496962382497/100000000000000 : ℝ)^25
        have hw : |(-1942318909/10000000000 : ℝ)|=(1942318909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6860955703/10000000000 : ℝ)|^33 ≤ (3040868897641/5000000000000 : ℝ)^25
        have hw : |(6860955703/10000000000 : ℝ)|=(6860955703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2099074377/5000000000 : ℝ)*x 0 + (1474902643/2500000000 : ℝ)*x 1 + (-2770149639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099074377/5000000000 : ℝ)^33 ≤ (31800674116181/100000000000000 : ℝ)^25 := by
    have hnat : (2099074377 : ℕ)^33*100000000000000^25 ≤ 31800674116181^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099074377 5000000000 31800674116181 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1474902643/2500000000 : ℝ)^33 ≤ (24914766423123/50000000000000 : ℝ)^25 := by
    have hnat : (1474902643 : ℕ)^33*50000000000000^25 ≤ 24914766423123^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474902643 2500000000 24914766423123 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2770149639/10000000000 : ℝ)^33 ≤ (18369793023831/100000000000000 : ℝ)^25 := by
    have hnat : (2770149639 : ℕ)^33*100000000000000^25 ≤ 18369793023831^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770149639 10000000000 18369793023831 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099074377/5000000000 : ℝ), (1474902643/2500000000 : ℝ), (-2770149639/10000000000 : ℝ)] ![(31800674116181/100000000000000 : ℝ), (24914766423123/50000000000000 : ℝ), (18369793023831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099074377/5000000000 : ℝ)|^33 ≤ (31800674116181/100000000000000 : ℝ)^25
        have hw : |(2099074377/5000000000 : ℝ)|=(2099074377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1474902643/2500000000 : ℝ)|^33 ≤ (24914766423123/50000000000000 : ℝ)^25
        have hw : |(1474902643/2500000000 : ℝ)|=(1474902643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2770149639/10000000000 : ℝ)|^33 ≤ (18369793023831/100000000000000 : ℝ)^25
        have hw : |(-2770149639/10000000000 : ℝ)|=(2770149639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_12 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (858735059/5000000000 : ℝ)*x 0 + (376464271/500000000 : ℝ)*x 1 + (389688871/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858735059/5000000000 : ℝ)^33 ≤ (9773581307039/100000000000000 : ℝ)^25 := by
    have hnat : (858735059 : ℕ)^33*100000000000000^25 ≤ 9773581307039^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858735059 5000000000 9773581307039 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376464271/500000000 : ℝ)^33 ≤ (68756690451057/100000000000000 : ℝ)^25 := by
    have hnat : (376464271 : ℕ)^33*100000000000000^25 ≤ 68756690451057^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376464271 500000000 68756690451057 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389688871/1250000000 : ℝ)^33 ≤ (21469728223319/100000000000000 : ℝ)^25 := by
    have hnat : (389688871 : ℕ)^33*100000000000000^25 ≤ 21469728223319^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389688871 1250000000 21469728223319 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858735059/5000000000 : ℝ), (376464271/500000000 : ℝ), (389688871/1250000000 : ℝ)] ![(9773581307039/100000000000000 : ℝ), (68756690451057/100000000000000 : ℝ), (21469728223319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858735059/5000000000 : ℝ)|^33 ≤ (9773581307039/100000000000000 : ℝ)^25
        have hw : |(858735059/5000000000 : ℝ)|=(858735059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(376464271/500000000 : ℝ)|^33 ≤ (68756690451057/100000000000000 : ℝ)^25
        have hw : |(376464271/500000000 : ℝ)|=(376464271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(389688871/1250000000 : ℝ)|^33 ≤ (21469728223319/100000000000000 : ℝ)^25
        have hw : |(389688871/1250000000 : ℝ)|=(389688871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2876873689/5000000000 : ℝ)*x 0 + (1895435847/5000000000 : ℝ)*x 1 + (3391758847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2876873689/5000000000 : ℝ)^33 ≤ (24104884069877/50000000000000 : ℝ)^25 := by
    have hnat : (2876873689 : ℕ)^33*50000000000000^25 ≤ 24104884069877^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876873689 5000000000 24104884069877 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895435847/5000000000 : ℝ)^33 ≤ (27793010589517/100000000000000 : ℝ)^25 := by
    have hnat : (1895435847 : ℕ)^33*100000000000000^25 ≤ 27793010589517^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895435847 5000000000 27793010589517 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3391758847/10000000000 : ℝ)^33 ≤ (11998610628057/50000000000000 : ℝ)^25 := by
    have hnat : (3391758847 : ℕ)^33*50000000000000^25 ≤ 11998610628057^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3391758847 10000000000 11998610628057 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2876873689/5000000000 : ℝ), (1895435847/5000000000 : ℝ), (3391758847/10000000000 : ℝ)] ![(24104884069877/50000000000000 : ℝ), (27793010589517/100000000000000 : ℝ), (11998610628057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2876873689/5000000000 : ℝ)|^33 ≤ (24104884069877/50000000000000 : ℝ)^25
        have hw : |(-2876873689/5000000000 : ℝ)|=(2876873689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1895435847/5000000000 : ℝ)|^33 ≤ (27793010589517/100000000000000 : ℝ)^25
        have hw : |(1895435847/5000000000 : ℝ)|=(1895435847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3391758847/10000000000 : ℝ)|^33 ≤ (11998610628057/50000000000000 : ℝ)^25
        have hw : |(3391758847/10000000000 : ℝ)|=(3391758847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (744835877/2000000000 : ℝ)*x 0 + (-2286293491/10000000000 : ℝ)*x 1 + (6669972911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (744835877/2000000000 : ℝ)^33 ≤ (13574704531447/50000000000000 : ℝ)^25 := by
    have hnat : (744835877 : ℕ)^33*50000000000000^25 ≤ 13574704531447^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744835877 2000000000 13574704531447 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286293491/10000000000 : ℝ)^33 ≤ (14257855650219/100000000000000 : ℝ)^25 := by
    have hnat : (2286293491 : ℕ)^33*100000000000000^25 ≤ 14257855650219^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286293491 10000000000 14257855650219 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6669972911/10000000000 : ℝ)^33 ≤ (11718547053903/20000000000000 : ℝ)^25 := by
    have hnat : (6669972911 : ℕ)^33*20000000000000^25 ≤ 11718547053903^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6669972911 10000000000 11718547053903 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(744835877/2000000000 : ℝ), (-2286293491/10000000000 : ℝ), (6669972911/10000000000 : ℝ)] ![(13574704531447/50000000000000 : ℝ), (14257855650219/100000000000000 : ℝ), (11718547053903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(744835877/2000000000 : ℝ)|^33 ≤ (13574704531447/50000000000000 : ℝ)^25
        have hw : |(744835877/2000000000 : ℝ)|=(744835877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2286293491/10000000000 : ℝ)|^33 ≤ (14257855650219/100000000000000 : ℝ)^25
        have hw : |(-2286293491/10000000000 : ℝ)|=(2286293491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6669972911/10000000000 : ℝ)|^33 ≤ (11718547053903/20000000000000 : ℝ)^25
        have hw : |(6669972911/10000000000 : ℝ)|=(6669972911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (135141293/312500000 : ℝ)*x 0 + (5455949503/10000000000 : ℝ)*x 1 + (-317413783/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135141293/312500000 : ℝ)^33 ≤ (33070306769131/100000000000000 : ℝ)^25 := by
    have hnat : (135141293 : ℕ)^33*100000000000000^25 ≤ 33070306769131^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135141293 312500000 33070306769131 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455949503/10000000000 : ℝ)^33 ≤ (44943702962299/100000000000000 : ℝ)^25 := by
    have hnat : (5455949503 : ℕ)^33*100000000000000^25 ≤ 44943702962299^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455949503 10000000000 44943702962299 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317413783/1000000000 : ℝ)^33 ≤ (21985990251789/100000000000000 : ℝ)^25 := by
    have hnat : (317413783 : ℕ)^33*100000000000000^25 ≤ 21985990251789^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317413783 1000000000 21985990251789 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135141293/312500000 : ℝ), (5455949503/10000000000 : ℝ), (-317413783/1000000000 : ℝ)] ![(33070306769131/100000000000000 : ℝ), (44943702962299/100000000000000 : ℝ), (21985990251789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135141293/312500000 : ℝ)|^33 ≤ (33070306769131/100000000000000 : ℝ)^25
        have hw : |(135141293/312500000 : ℝ)|=(135141293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455949503/10000000000 : ℝ)|^33 ≤ (44943702962299/100000000000000 : ℝ)^25
        have hw : |(5455949503/10000000000 : ℝ)|=(5455949503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-317413783/1000000000 : ℝ)|^33 ≤ (21985990251789/100000000000000 : ℝ)^25
        have hw : |(-317413783/1000000000 : ℝ)|=(317413783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_19 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2363163219/10000000000 : ℝ)*x 0 + (3399031827/5000000000 : ℝ)*x 1 + (700215931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2363163219/10000000000 : ℝ)^33 ≤ (297880246201/2000000000000 : ℝ)^25 := by
    have hnat : (2363163219 : ℕ)^33*2000000000000^25 ≤ 297880246201^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363163219 10000000000 297880246201 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3399031827/5000000000 : ℝ)^33 ≤ (469395076257/781250000000 : ℝ)^25 := by
    have hnat : (3399031827 : ℕ)^33*781250000000^25 ≤ 469395076257^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3399031827 5000000000 469395076257 781250000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (700215931/2000000000 : ℝ)^33 ≤ (5004683583043/20000000000000 : ℝ)^25 := by
    have hnat : (700215931 : ℕ)^33*20000000000000^25 ≤ 5004683583043^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700215931 2000000000 5004683583043 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2363163219/10000000000 : ℝ), (3399031827/5000000000 : ℝ), (700215931/2000000000 : ℝ)] ![(297880246201/2000000000000 : ℝ), (469395076257/781250000000 : ℝ), (5004683583043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2363163219/10000000000 : ℝ)|^33 ≤ (297880246201/2000000000000 : ℝ)^25
        have hw : |(2363163219/10000000000 : ℝ)|=(2363163219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3399031827/5000000000 : ℝ)|^33 ≤ (469395076257/781250000000 : ℝ)^25
        have hw : |(3399031827/5000000000 : ℝ)|=(3399031827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(700215931/2000000000 : ℝ)|^33 ≤ (5004683583043/20000000000000 : ℝ)^25
        have hw : |(700215931/2000000000 : ℝ)|=(700215931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-281429457/500000000 : ℝ)*x 0 + (973627253/2500000000 : ℝ)*x 1 + (3431526261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281429457/500000000 : ℝ)^33 ≤ (936607000593/2000000000000 : ℝ)^25 := by
    have hnat : (281429457 : ℕ)^33*2000000000000^25 ≤ 936607000593^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281429457 500000000 936607000593 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973627253/2500000000 : ℝ)^33 ≤ (28800337780833/100000000000000 : ℝ)^25 := by
    have hnat : (973627253 : ℕ)^33*100000000000000^25 ≤ 28800337780833^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973627253 2500000000 28800337780833 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3431526261/10000000000 : ℝ)^33 ≤ (6092328044419/25000000000000 : ℝ)^25 := by
    have hnat : (3431526261 : ℕ)^33*25000000000000^25 ≤ 6092328044419^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3431526261 10000000000 6092328044419 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-281429457/500000000 : ℝ), (973627253/2500000000 : ℝ), (3431526261/10000000000 : ℝ)] ![(936607000593/2000000000000 : ℝ), (28800337780833/100000000000000 : ℝ), (6092328044419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-281429457/500000000 : ℝ)|^33 ≤ (936607000593/2000000000000 : ℝ)^25
        have hw : |(-281429457/500000000 : ℝ)|=(281429457/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973627253/2500000000 : ℝ)|^33 ≤ (28800337780833/100000000000000 : ℝ)^25
        have hw : |(973627253/2500000000 : ℝ)|=(973627253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3431526261/10000000000 : ℝ)|^33 ≤ (6092328044419/25000000000000 : ℝ)^25
        have hw : |(3431526261/10000000000 : ℝ)|=(3431526261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3637799813/10000000000 : ℝ)*x 0 + (-553308539/2500000000 : ℝ)*x 1 + (1358525647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3637799813/10000000000 : ℝ)^33 ≤ (1316064624177/5000000000000 : ℝ)^25 := by
    have hnat : (3637799813 : ℕ)^33*5000000000000^25 ≤ 1316064624177^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3637799813 10000000000 1316064624177 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553308539/2500000000 : ℝ)^33 ≤ (2731908289947/20000000000000 : ℝ)^25 := by
    have hnat : (553308539 : ℕ)^33*20000000000000^25 ≤ 2731908289947^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553308539 2500000000 2731908289947 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358525647/2000000000 : ℝ)^33 ≤ (937799469571/1562500000000 : ℝ)^25 := by
    have hnat : (1358525647 : ℕ)^33*1562500000000^25 ≤ 937799469571^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358525647 2000000000 937799469571 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3637799813/10000000000 : ℝ), (-553308539/2500000000 : ℝ), (1358525647/2000000000 : ℝ)] ![(1316064624177/5000000000000 : ℝ), (2731908289947/20000000000000 : ℝ), (937799469571/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3637799813/10000000000 : ℝ)|^33 ≤ (1316064624177/5000000000000 : ℝ)^25
        have hw : |(3637799813/10000000000 : ℝ)|=(3637799813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553308539/2500000000 : ℝ)|^33 ≤ (2731908289947/20000000000000 : ℝ)^25
        have hw : |(-553308539/2500000000 : ℝ)|=(553308539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358525647/2000000000 : ℝ)|^33 ≤ (937799469571/1562500000000 : ℝ)^25
        have hw : |(1358525647/2000000000 : ℝ)|=(1358525647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2458875243/5000000000 : ℝ)*x 0 + (2517429/5000000 : ℝ)*x 1 + (-2998156291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2458875243/5000000000 : ℝ)^33 ≤ (39186075127177/100000000000000 : ℝ)^25 := by
    have hnat : (2458875243 : ℕ)^33*100000000000000^25 ≤ 39186075127177^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458875243 5000000000 39186075127177 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517429/5000000 : ℝ)^33 ≤ (40422497138739/100000000000000 : ℝ)^25 := by
    have hnat : (2517429 : ℕ)^33*100000000000000^25 ≤ 40422497138739^25*5000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517429 5000000 40422497138739 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2998156291/10000000000 : ℝ)^33 ≤ (20391427724141/100000000000000 : ℝ)^25 := by
    have hnat : (2998156291 : ℕ)^33*100000000000000^25 ≤ 20391427724141^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2998156291 10000000000 20391427724141 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2458875243/5000000000 : ℝ), (2517429/5000000 : ℝ), (-2998156291/10000000000 : ℝ)] ![(39186075127177/100000000000000 : ℝ), (40422497138739/100000000000000 : ℝ), (20391427724141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2458875243/5000000000 : ℝ)|^33 ≤ (39186075127177/100000000000000 : ℝ)^25
        have hw : |(2458875243/5000000000 : ℝ)|=(2458875243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517429/5000000 : ℝ)|^33 ≤ (40422497138739/100000000000000 : ℝ)^25
        have hw : |(2517429/5000000 : ℝ)|=(2517429/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2998156291/10000000000 : ℝ)|^33 ≤ (20391427724141/100000000000000 : ℝ)^25
        have hw : |(-2998156291/10000000000 : ℝ)|=(2998156291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s0_25 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1596570817/10000000000 : ℝ)*x 0 + (1926300293/2500000000 : ℝ)*x 1 + (1490586697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1596570817/10000000000 : ℝ)^33 ≤ (1775163674033/20000000000000 : ℝ)^25 := by
    have hnat : (1596570817 : ℕ)^33*20000000000000^25 ≤ 1775163674033^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596570817 10000000000 1775163674033 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926300293/2500000000 : ℝ)^33 ≤ (70885083661701/100000000000000 : ℝ)^25 := by
    have hnat : (1926300293 : ℕ)^33*100000000000000^25 ≤ 70885083661701^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926300293 2500000000 70885083661701 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1490586697/5000000000 : ℝ)^33 ≤ (20239097955957/100000000000000 : ℝ)^25 := by
    have hnat : (1490586697 : ℕ)^33*100000000000000^25 ≤ 20239097955957^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490586697 5000000000 20239097955957 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1596570817/10000000000 : ℝ), (1926300293/2500000000 : ℝ), (1490586697/5000000000 : ℝ)] ![(1775163674033/20000000000000 : ℝ), (70885083661701/100000000000000 : ℝ), (20239097955957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1596570817/10000000000 : ℝ)|^33 ≤ (1775163674033/20000000000000 : ℝ)^25
        have hw : |(1596570817/10000000000 : ℝ)|=(1596570817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1926300293/2500000000 : ℝ)|^33 ≤ (70885083661701/100000000000000 : ℝ)^25
        have hw : |(1926300293/2500000000 : ℝ)|=(1926300293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1490586697/5000000000 : ℝ)|^33 ≤ (20239097955957/100000000000000 : ℝ)^25
        have hw : |(1490586697/5000000000 : ℝ)|=(1490586697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-122366217/250000000 : ℝ)*x 0 + (4070246581/10000000000 : ℝ)*x 1 + (407030617/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122366217/250000000 : ℝ)^33 ≤ (4867908722693/12500000000000 : ℝ)^25 := by
    have hnat : (122366217 : ℕ)^33*12500000000000^25 ≤ 4867908722693^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122366217 250000000 4867908722693 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4070246581/10000000000 : ℝ)^33 ≤ (30528070124233/100000000000000 : ℝ)^25 := by
    have hnat : (4070246581 : ℕ)^33*100000000000000^25 ≤ 30528070124233^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4070246581 10000000000 30528070124233 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407030617/1000000000 : ℝ)^33 ≤ (30528660080307/100000000000000 : ℝ)^25 := by
    have hnat : (407030617 : ℕ)^33*100000000000000^25 ≤ 30528660080307^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407030617 1000000000 30528660080307 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122366217/250000000 : ℝ), (4070246581/10000000000 : ℝ), (407030617/1000000000 : ℝ)] ![(4867908722693/12500000000000 : ℝ), (30528070124233/100000000000000 : ℝ), (30528660080307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122366217/250000000 : ℝ)|^33 ≤ (4867908722693/12500000000000 : ℝ)^25
        have hw : |(-122366217/250000000 : ℝ)|=(122366217/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4070246581/10000000000 : ℝ)|^33 ≤ (30528070124233/100000000000000 : ℝ)^25
        have hw : |(4070246581/10000000000 : ℝ)|=(4070246581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(407030617/1000000000 : ℝ)|^33 ≤ (30528660080307/100000000000000 : ℝ)^25
        have hw : |(407030617/1000000000 : ℝ)|=(407030617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1053514437/2500000000 : ℝ)*x 0 + (-1752143541/5000000000 : ℝ)*x 1 + (2637491593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053514437/2500000000 : ℝ)^33 ≤ (3994980374981/12500000000000 : ℝ)^25 := by
    have hnat : (1053514437 : ℕ)^33*12500000000000^25 ≤ 3994980374981^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053514437 2500000000 3994980374981 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1752143541/5000000000 : ℝ)^33 ≤ (6263420699397/25000000000000 : ℝ)^25 := by
    have hnat : (1752143541 : ℕ)^33*25000000000000^25 ≤ 6263420699397^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752143541 5000000000 6263420699397 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637491593/5000000000 : ℝ)^33 ≤ (8597294838109/20000000000000 : ℝ)^25 := by
    have hnat : (2637491593 : ℕ)^33*20000000000000^25 ≤ 8597294838109^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637491593 5000000000 8597294838109 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053514437/2500000000 : ℝ), (-1752143541/5000000000 : ℝ), (2637491593/5000000000 : ℝ)] ![(3994980374981/12500000000000 : ℝ), (6263420699397/25000000000000 : ℝ), (8597294838109/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053514437/2500000000 : ℝ)|^33 ≤ (3994980374981/12500000000000 : ℝ)^25
        have hw : |(1053514437/2500000000 : ℝ)|=(1053514437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1752143541/5000000000 : ℝ)|^33 ≤ (6263420699397/25000000000000 : ℝ)^25
        have hw : |(-1752143541/5000000000 : ℝ)|=(1752143541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637491593/5000000000 : ℝ)|^33 ≤ (8597294838109/20000000000000 : ℝ)^25
        have hw : |(2637491593/5000000000 : ℝ)|=(2637491593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4214011449/10000000000 : ℝ)*x 0 + (5275015043/10000000000 : ℝ)*x 1 + (-876074971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214011449/10000000000 : ℝ)^33 ≤ (7989844875177/25000000000000 : ℝ)^25 := by
    have hnat : (4214011449 : ℕ)^33*25000000000000^25 ≤ 7989844875177^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214011449 10000000000 7989844875177 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5275015043/10000000000 : ℝ)^33 ≤ (21493408435751/50000000000000 : ℝ)^25 := by
    have hnat : (5275015043 : ℕ)^33*50000000000000^25 ≤ 21493408435751^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275015043 10000000000 21493408435751 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876074971/2500000000 : ℝ)^33 ≤ (6263450903359/25000000000000 : ℝ)^25 := by
    have hnat : (876074971 : ℕ)^33*25000000000000^25 ≤ 6263450903359^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876074971 2500000000 6263450903359 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214011449/10000000000 : ℝ), (5275015043/10000000000 : ℝ), (-876074971/2500000000 : ℝ)] ![(7989844875177/25000000000000 : ℝ), (21493408435751/50000000000000 : ℝ), (6263450903359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214011449/10000000000 : ℝ)|^33 ≤ (7989844875177/25000000000000 : ℝ)^25
        have hw : |(4214011449/10000000000 : ℝ)|=(4214011449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5275015043/10000000000 : ℝ)|^33 ≤ (21493408435751/50000000000000 : ℝ)^25
        have hw : |(5275015043/10000000000 : ℝ)|=(5275015043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-876074971/2500000000 : ℝ)|^33 ≤ (6263450903359/25000000000000 : ℝ)^25
        have hw : |(-876074971/2500000000 : ℝ)|=(876074971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303077_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1859512799/5000000000 : ℝ)*x 0 + (4655401679/10000000000 : ℝ)*x 1 + (4655322417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1859512799/5000000000 : ℝ)^33 ≤ (27099825927703/100000000000000 : ℝ)^25 := by
    have hnat : (1859512799 : ℕ)^33*100000000000000^25 ≤ 27099825927703^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859512799 5000000000 27099825927703 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4655401679/10000000000 : ℝ)^33 ≤ (18225248309301/50000000000000 : ℝ)^25 := by
    have hnat : (4655401679 : ℕ)^33*50000000000000^25 ≤ 18225248309301^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4655401679 10000000000 18225248309301 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4655322417/10000000000 : ℝ)^33 ≤ (3644967742969/10000000000000 : ℝ)^25 := by
    have hnat : (4655322417 : ℕ)^33*10000000000000^25 ≤ 3644967742969^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4655322417 10000000000 3644967742969 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1859512799/5000000000 : ℝ), (4655401679/10000000000 : ℝ), (4655322417/10000000000 : ℝ)] ![(27099825927703/100000000000000 : ℝ), (18225248309301/50000000000000 : ℝ), (3644967742969/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1859512799/5000000000 : ℝ)|^33 ≤ (27099825927703/100000000000000 : ℝ)^25
        have hw : |(1859512799/5000000000 : ℝ)|=(1859512799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4655401679/10000000000 : ℝ)|^33 ≤ (18225248309301/50000000000000 : ℝ)^25
        have hw : |(4655401679/10000000000 : ℝ)|=(4655401679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4655322417/10000000000 : ℝ)|^33 ≤ (3644967742969/10000000000000 : ℝ)^25
        have hw : |(4655322417/10000000000 : ℝ)|=(4655322417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303077 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-5588422173/10000000000 : ℝ)*X 0 0+(469193519/1250000000 : ℝ)*X 0 1+(362277667/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4526309051/10000000000 : ℝ)*X 2 0+(1366617239/2500000000 : ℝ)*X 2 1+(-586849251/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((132548341/625000000 : ℝ)*X 0 0+(6823481663/10000000000 : ℝ)*X 0 1+(919589377/2500000000 : ℝ)*X 0 2+(132548341/625000000 : ℝ)*X 1 0+(6823481663/10000000000 : ℝ)*X 1 1+(919589377/2500000000 : ℝ)*X 1 2+(132548341/625000000 : ℝ)*X 2 0+(6823481663/10000000000 : ℝ)*X 2 1+(919589377/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5752434173/10000000000 : ℝ)*X 0 0+(3388262117/10000000000 : ℝ)*X 0 1+(3795745311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((47247173/125000000 : ℝ)*X 1 0+(-1942318909/10000000000 : ℝ)*X 1 1+(6860955703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2099074377/5000000000 : ℝ)*X 2 0+(1474902643/2500000000 : ℝ)*X 2 1+(-2770149639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((858735059/5000000000 : ℝ)*X 0 0+(376464271/500000000 : ℝ)*X 0 1+(389688871/1250000000 : ℝ)*X 0 2+(858735059/5000000000 : ℝ)*X 1 0+(376464271/500000000 : ℝ)*X 1 1+(389688871/1250000000 : ℝ)*X 1 2+(858735059/5000000000 : ℝ)*X 2 0+(376464271/500000000 : ℝ)*X 2 1+(389688871/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2876873689/5000000000 : ℝ)*X 0 0+(1895435847/5000000000 : ℝ)*X 0 1+(3391758847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((744835877/2000000000 : ℝ)*X 1 0+(-2286293491/10000000000 : ℝ)*X 1 1+(6669972911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((135141293/312500000 : ℝ)*X 2 0+(5455949503/10000000000 : ℝ)*X 2 1+(-317413783/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2363163219/10000000000 : ℝ)*X 0 0+(3399031827/5000000000 : ℝ)*X 0 1+(700215931/2000000000 : ℝ)*X 0 2+(2363163219/10000000000 : ℝ)*X 1 0+(3399031827/5000000000 : ℝ)*X 1 1+(700215931/2000000000 : ℝ)*X 1 2+(2363163219/10000000000 : ℝ)*X 2 0+(3399031827/5000000000 : ℝ)*X 2 1+(700215931/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-281429457/500000000 : ℝ)*X 0 0+(973627253/2500000000 : ℝ)*X 0 1+(3431526261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3637799813/10000000000 : ℝ)*X 1 0+(-553308539/2500000000 : ℝ)*X 1 1+(1358525647/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2458875243/5000000000 : ℝ)*X 2 0+(2517429/5000000 : ℝ)*X 2 1+(-2998156291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1596570817/10000000000 : ℝ)*X 0 0+(1926300293/2500000000 : ℝ)*X 0 1+(1490586697/5000000000 : ℝ)*X 0 2+(1596570817/10000000000 : ℝ)*X 1 0+(1926300293/2500000000 : ℝ)*X 1 1+(1490586697/5000000000 : ℝ)*X 1 2+(1596570817/10000000000 : ℝ)*X 2 0+(1926300293/2500000000 : ℝ)*X 2 1+(1490586697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((25323/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25323/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6648629884269960021039/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (333842984407/125000000000 : ℝ)*(base49) + (97762847451/100000000000 : ℝ)*(base50) + (1641940214357/1000000000000 : ℝ)*(base60) + (4818603715633/500000000000 : ℝ)*(major_s0_0) + (4818603715633/500000000000 : ℝ)*(major_s0_1) + (4818603715633/500000000000 : ℝ)*(major_s0_2) + (257241509/1000000000000 : ℝ)*(sp_s0_0) + (20645407/200000000000 : ℝ)*(sp_s0_6) + (2573457491693/200000000000 : ℝ)*(sp_s0_7) + (6433567133603/500000000000 : ℝ)*(sp_s0_8) + (12867326555507/1000000000000 : ℝ)*(sp_s0_9) + (3203381251549/500000000000 : ℝ)*(sp_s0_12) + (54536117/250000000000 : ℝ)*(sp_s0_15) + (410432769/1000000000000 : ℝ)*(sp_s0_21) + (6406865730133/1000000000000 : ℝ)*(f.failure) + (6433772349987/500000000000 : ℝ)*(f.sum) + (2631846172238081/5000000000000000000000000000 : ℝ)*base62 + (135043696849623/625000000000000000000000000 : ℝ)*base64 + (340500537692987/1000000000000000000000000000 : ℝ)*base67 + (582635609507013/1000000000000000000000000000 : ℝ)*base68 + (1433673412261919/5000000000000000000000000000 : ℝ)*base70 + (232563324287123/625000000000000000000000000 : ℝ)*base72 + (54502984900377/625000000000000000000000000 : ℝ)*base74 + (290002543892987/1000000000000000000000000000 : ℝ)*base76 + (1584673711667951/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (293/5000000000000000 : ℝ)*base87 + (293/5000000000000000 : ℝ)*base89 + (293/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((393/12500 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(393/12500 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4767494103180498690537/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (314527/200000000000 : ℝ)*(base40) + (1094544125517/1000000000000 : ℝ)*(base49) + (49628721647/40000000000 : ℝ)*(base60) + (962405304843/125000000000 : ℝ)*(major_s0_0) + (962405304843/125000000000 : ℝ)*(major_s0_1) + (962405304843/125000000000 : ℝ)*(major_s0_2) + (19032947/1000000000000 : ℝ)*(sp_s0_2) + (97728871/1000000000000 : ℝ)*(sp_s0_7) + (35001161/1000000000000 : ℝ)*(sp_s0_8) + (10279888103661/1000000000000 : ℝ)*(sp_s0_13) + (10279950831371/1000000000000 : ℝ)*(sp_s0_14) + (2569979426913/250000000000 : ℝ)*(sp_s0_15) + (511849650229/100000000000 : ℝ)*(sp_s0_19) + (49091933/1000000000000 : ℝ)*(sp_s0_22) + (511849650229/100000000000 : ℝ)*(f.failure) + (2569996458133/250000000000 : ℝ)*(f.sum) + (95929138338051/1250000000000000000000000000 : ℝ)*base62 + (6647413184129/78125000000000000000000000 : ℝ)*base64 + (29312335556823/250000000000000000000000000 : ℝ)*base66 + (25516067268177/250000000000000000000000000 : ℝ)*base69 + (547923376536949/1250000000000000000000000000 : ℝ)*base70 + (35024660928617/156250000000000000000000000 : ℝ)*base73 + (3140280879749/19531250000000000000000000 : ℝ)*base74 + (130687530593177/250000000000000000000000000 : ℝ)*base76 + (166413610894821/1250000000000000000000000000 : ℝ)*base79 + (309/500000000000000 : ℝ)*base87 + (309/500000000000000 : ℝ)*base89 + (309/500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13721/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13721/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (71982156608824983699447/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1922733125709/1000000000000 : ℝ)*(base49) + (531661134397/500000000000 : ℝ)*(base50) + (687171125001/1000000000000 : ℝ)*(base60) + (7544028845667/1000000000000 : ℝ)*(major_s0_0) + (7544028845667/1000000000000 : ℝ)*(major_s0_1) + (7544028845667/1000000000000 : ℝ)*(major_s0_2) + (105621883/500000000000 : ℝ)*(sp_s0_2) + (115465931/250000000000 : ℝ)*(sp_s0_12) + (139704907/500000000000 : ℝ)*(sp_s0_13) + (899169771/1000000000000 : ℝ)*(sp_s0_14) + (5036231893037/500000000000 : ℝ)*(sp_s0_20) + (10071844026117/1000000000000 : ℝ)*(sp_s0_21) + (10072531952121/1000000000000 : ℝ)*(sp_s0_22) + (5014847832903/1000000000000 : ℝ)*(sp_s0_25) + (5015309696627/1000000000000 : ℝ)*(f.failure) + (10072743195887/1000000000000 : ℝ)*(f.sum) + (7297210047543981/10000000000000000000000000000 : ℝ)*base63 + (501965384824323/1250000000000000000000000000 : ℝ)*base65 + (822366185772287/2000000000000000000000000000 : ℝ)*base66 + (321522463627713/2000000000000000000000000000 : ℝ)*base69 + (6057849238456019/10000000000000000000000000000 : ℝ)*base71 + (110162651425677/1250000000000000000000000000 : ℝ)*base72 + (808363583300677/1250000000000000000000000000 : ℝ)*base75 + (1366339370172287/2000000000000000000000000000 : ℝ)*base77 + (4993984337266851/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (3333/5000000000000000 : ℝ)*base86 + (3333/5000000000000000 : ℝ)*base88 + (3333/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (25323/100000 : ℝ) ^ (131/32 : ℝ) ≤ (180763262081109299/50000000000000000000 : ℝ) := by
    have hpowers : (25323/100000 : ℝ)^131 ≤ (180763262081109299/50000000000000000000 : ℝ)^32 := by
      have hnat : (25323 : ℕ)^131*50000000000000000000^32 ≤ 180763262081109299^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25323 100000 180763262081109299 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25323/100000 : ℝ)) (X := (180763262081109299/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50180763262081109299/50000000000000000000 : ℝ) ≤ (5004409571843613/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50180763262081109299/50000000000000000000 : ℝ)^32 ≤ (5004409571843613/5000000000000000 : ℝ)^131 := by
      have hnat : (50180763262081109299 : ℕ)^32*5000000000000000^131 ≤ 5004409571843613^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50180763262081109299 50000000000000000000 5004409571843613 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004409571843613/5000000000000000 : ℝ)) (X := (50180763262081109299/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25180763262081109299/25000000000000000000 : ℝ) ≤ (2504403577888051/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25180763262081109299/25000000000000000000 : ℝ)^32 ≤ (2504403577888051/2500000000000000 : ℝ)^131 := by
      have hnat : (25180763262081109299 : ℕ)^32*2500000000000000^131 ≤ 2504403577888051^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25180763262081109299 25000000000000000000 2504403577888051 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504403577888051/2500000000000000 : ℝ)) (X := (25180763262081109299/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4409571843613/1266150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4397583932489/1266150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (25323/100000 : ℝ)) (alpha := (4409571843613/1266150000000000 : ℝ)) (beta := (4397583932489/1266150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (25323/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4409571843613/1266150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4397583932489/1266150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (393/12500 : ℝ) ^ (131/32 : ℝ) ≤ (70643000517249/100000000000000000000 : ℝ) := by
    have hpowers : (393/12500 : ℝ)^131 ≤ (70643000517249/100000000000000000000 : ℝ)^32 := by
      have hnat : (393 : ℕ)^131*100000000000000000000^32 ≤ 70643000517249^32*12500^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        393 12500 70643000517249 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (393/12500 : ℝ)) (X := (70643000517249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100000070643000517249/100000000000000000000 : ℝ) ≤ (10000001725630087/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100000070643000517249/100000000000000000000 : ℝ)^32 ≤ (10000001725630087/10000000000000000 : ℝ)^131 := by
      have hnat : (100000070643000517249 : ℕ)^32*10000000000000000^131 ≤ 10000001725630087^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000070643000517249 100000000000000000000 10000001725630087 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001725630087/10000000000000000 : ℝ)) (X := (100000070643000517249/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50000070643000517249/50000000000000000000 : ℝ) ≤ (2500000862814813/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50000070643000517249/50000000000000000000 : ℝ)^32 ≤ (2500000862814813/2500000000000000 : ℝ)^131 := by
      have hnat : (50000070643000517249 : ℕ)^32*2500000000000000^131 ≤ 2500000862814813^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000070643000517249 50000000000000000000 2500000862814813 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000862814813/2500000000000000 : ℝ)) (X := (50000070643000517249/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(575210029/104800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(345125833/62880000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (393/12500 : ℝ)) (alpha := (575210029/104800000000000 : ℝ)) (beta := (345125833/62880000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (393/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(575210029/104800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(345125833/62880000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13721/100000 : ℝ) ^ (131/32 : ℝ) ≤ (29422052950567923/100000000000000000000 : ℝ) := by
    have hpowers : (13721/100000 : ℝ)^131 ≤ (29422052950567923/100000000000000000000 : ℝ)^32 := by
      have hnat : (13721 : ℕ)^131*100000000000000000000^32 ≤ 29422052950567923^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13721 100000 29422052950567923 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13721/100000 : ℝ)) (X := (29422052950567923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100029422052950567923/100000000000000000000 : ℝ) ≤ (5000359313374277/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100029422052950567923/100000000000000000000 : ℝ)^32 ≤ (5000359313374277/5000000000000000 : ℝ)^131 := by
      have hnat : (100029422052950567923 : ℕ)^32*5000000000000000^131 ≤ 5000359313374277^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029422052950567923 100000000000000000000 5000359313374277 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000359313374277/5000000000000000 : ℝ)) (X := (100029422052950567923/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50029422052950567923/50000000000000000000 : ℝ) ≤ (2000287418755059/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50029422052950567923/50000000000000000000 : ℝ)^32 ≤ (2000287418755059/2000000000000000 : ℝ)^131 := by
      have hnat : (50029422052950567923 : ℕ)^32*2000000000000000^131 ≤ 2000287418755059^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029422052950567923 50000000000000000000 2000287418755059 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000287418755059/2000000000000000 : ℝ)) (X := (50029422052950567923/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(359313374277/686050000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(718467026741/1372100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (13721/100000 : ℝ)) (alpha := (359313374277/686050000000000 : ℝ)) (beta := (718467026741/1372100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (13721/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(359313374277/686050000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(718467026741/1372100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-122366217/250000000 : ℝ)*X 0 0+(4070246581/10000000000 : ℝ)*X 0 1+(407030617/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1053514437/2500000000 : ℝ)*X 1 0+(-1752143541/5000000000 : ℝ)*X 1 1+(2637491593/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4214011449/10000000000 : ℝ)*X 2 0+(5275015043/10000000000 : ℝ)*X 2 1+(-876074971/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1859512799/5000000000 : ℝ)*X 0 0+(4655401679/10000000000 : ℝ)*X 0 1+(4655322417/10000000000 : ℝ)*X 0 2+(1859512799/5000000000 : ℝ)*X 1 0+(4655401679/10000000000 : ℝ)*X 1 1+(4655322417/10000000000 : ℝ)*X 1 2+(1859512799/5000000000 : ℝ)*X 2 0+(4655401679/10000000000 : ℝ)*X 2 1+(4655322417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303077_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-391632671572134224652451992282971/65966451700000000000000000000000 : ℝ) := by norm_num
    linear_combination (41709/1000000000000 : ℝ)*(base19) + (5571/250000000000 : ℝ)*(base23) + (4213/1000000000000 : ℝ)*(base40) + (61031/1000000000000 : ℝ)*(base43) + (531524787889/1000000000000 : ℝ)*(base49) + (116583408307/500000000000 : ℝ)*(base50) + (31801359281/500000000000 : ℝ)*(base59) + (297569234323/1000000000000 : ℝ)*(base60) + (7521/5000 : ℝ)*(major_s1_0) + (1504199938969/1000000000000 : ℝ)*(major_s1_1) + (7521/5000 : ℝ)*(major_s1_2) + (1978948639301/1000000000000 : ℝ)*(sp_s1_0) + (1978948658623/1000000000000 : ℝ)*(sp_s1_1) + (1978948617017/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (494737175083/250000000000 : ℝ)*(f.sum) + (191942219901422023/862776480000000000000000000000 : ℝ)*base63 + (52066298552799/137210000000000000000000000 : ℝ)*base65 + (5852873738299/104800000000000000000000000 : ℝ)*base67 + (2379862716029/34302500000000000000000000 : ℝ)*base69 + (8795245267240899/25178035000000000000000000000 : ℝ)*base70 + (934289486887/1835000000000000000000000 : ℝ)*base73 + (14341391357519/62880000000000000000000000 : ℝ)*base75 + (252151269723/3670000000000000000000000 : ℝ)*base77 + (14720032151575413/38461600000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p003_b033 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=77 := by omega
  rcases hc with rfl
  · exact collision_c303077 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

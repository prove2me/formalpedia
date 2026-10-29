-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b021
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:41.428953+00:00
-- url     : https://prove2.me/submissions/fa5ee579-1269-421f-9f74-245f26c046e5

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
theorem collision_support_c310037_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-925593833/10000000000 : ℝ)*x 0 + (-7264482089/10000000000 : ℝ)*x 1 + (1909397877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925593833/10000000000 : ℝ)^9 ≤ (4689343107853/100000000000000 : ℝ)^7 := by
    have hnat : (925593833 : ℕ)^9*100000000000000^7 ≤ 4689343107853^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925593833 10000000000 4689343107853 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7264482089/10000000000 : ℝ)^9 ≤ (8288173965007/12500000000000 : ℝ)^7 := by
    have hnat : (7264482089 : ℕ)^9*12500000000000^7 ≤ 8288173965007^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7264482089 10000000000 8288173965007 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1909397877/5000000000 : ℝ)^9 ≤ (7251316287093/25000000000000 : ℝ)^7 := by
    have hnat : (1909397877 : ℕ)^9*25000000000000^7 ≤ 7251316287093^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909397877 5000000000 7251316287093 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925593833/10000000000 : ℝ), (-7264482089/10000000000 : ℝ), (1909397877/5000000000 : ℝ)] ![(4689343107853/100000000000000 : ℝ), (8288173965007/12500000000000 : ℝ), (7251316287093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925593833/10000000000 : ℝ)|^9 ≤ (4689343107853/100000000000000 : ℝ)^7
        have hw : |(-925593833/10000000000 : ℝ)|=(925593833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7264482089/10000000000 : ℝ)|^9 ≤ (8288173965007/12500000000000 : ℝ)^7
        have hw : |(-7264482089/10000000000 : ℝ)|=(7264482089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1909397877/5000000000 : ℝ)|^9 ≤ (7251316287093/25000000000000 : ℝ)^7
        have hw : |(1909397877/5000000000 : ℝ)|=(1909397877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4971558703/10000000000 : ℝ)*x 0 + (-385565769/1250000000 : ℝ)*x 1 + (-927648811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4971558703/10000000000 : ℝ)^9 ≤ (814340734631/2000000000000 : ℝ)^7 := by
    have hnat : (4971558703 : ℕ)^9*2000000000000^7 ≤ 814340734631^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971558703 10000000000 814340734631 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385565769/1250000000 : ℝ)^9 ≤ (11020779312139/50000000000000 : ℝ)^7 := by
    have hnat : (385565769 : ℕ)^9*50000000000000^7 ≤ 11020779312139^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385565769 1250000000 11020779312139 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (927648811/2000000000 : ℝ)^9 ≤ (145474236807/390625000000 : ℝ)^7 := by
    have hnat : (927648811 : ℕ)^9*390625000000^7 ≤ 145474236807^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927648811 2000000000 145474236807 390625000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4971558703/10000000000 : ℝ), (-385565769/1250000000 : ℝ), (-927648811/2000000000 : ℝ)] ![(814340734631/2000000000000 : ℝ), (11020779312139/50000000000000 : ℝ), (145474236807/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4971558703/10000000000 : ℝ)|^9 ≤ (814340734631/2000000000000 : ℝ)^7
        have hw : |(4971558703/10000000000 : ℝ)|=(4971558703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385565769/1250000000 : ℝ)|^9 ≤ (11020779312139/50000000000000 : ℝ)^7
        have hw : |(-385565769/1250000000 : ℝ)|=(385565769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-927648811/2000000000 : ℝ)|^9 ≤ (145474236807/390625000000 : ℝ)^7
        have hw : |(-927648811/2000000000 : ℝ)|=(927648811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-262713797/5000000000 : ℝ)*x 0 + (-903553357/1000000000 : ℝ)*x 1 + (103939721/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262713797/5000000000 : ℝ)^9 ≤ (113217909567/5000000000000 : ℝ)^7 := by
    have hnat : (262713797 : ℕ)^9*5000000000000^7 ≤ 113217909567^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262713797 5000000000 113217909567 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903553357/1000000000 : ℝ)^9 ≤ (87774664127557/100000000000000 : ℝ)^7 := by
    have hnat : (903553357 : ℕ)^9*100000000000000^7 ≤ 87774664127557^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903553357 1000000000 87774664127557 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103939721/625000000 : ℝ)^9 ≤ (4980488833141/50000000000000 : ℝ)^7 := by
    have hnat : (103939721 : ℕ)^9*50000000000000^7 ≤ 4980488833141^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103939721 625000000 4980488833141 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262713797/5000000000 : ℝ), (-903553357/1000000000 : ℝ), (103939721/625000000 : ℝ)] ![(113217909567/5000000000000 : ℝ), (87774664127557/100000000000000 : ℝ), (4980488833141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262713797/5000000000 : ℝ)|^9 ≤ (113217909567/5000000000000 : ℝ)^7
        have hw : |(-262713797/5000000000 : ℝ)|=(262713797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-903553357/1000000000 : ℝ)|^9 ≤ (87774664127557/100000000000000 : ℝ)^7
        have hw : |(-903553357/1000000000 : ℝ)|=(903553357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103939721/625000000 : ℝ)|^9 ≤ (4980488833141/50000000000000 : ℝ)^7
        have hw : |(103939721/625000000 : ℝ)|=(103939721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1155703339/2500000000 : ℝ)*x 0 + (124105669/400000000 : ℝ)*x 1 + (4970859993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1155703339/2500000000 : ℝ)^9 ≤ (37082185249941/100000000000000 : ℝ)^7 := by
    have hnat : (1155703339 : ℕ)^9*100000000000000^7 ≤ 37082185249941^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155703339 2500000000 37082185249941 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124105669/400000000 : ℝ)^9 ≤ (5552033816781/25000000000000 : ℝ)^7 := by
    have hnat : (124105669 : ℕ)^9*25000000000000^7 ≤ 5552033816781^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124105669 400000000 5552033816781 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4970859993/10000000000 : ℝ)^9 ≤ (40709679468221/100000000000000 : ℝ)^7 := by
    have hnat : (4970859993 : ℕ)^9*100000000000000^7 ≤ 40709679468221^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4970859993 10000000000 40709679468221 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1155703339/2500000000 : ℝ), (124105669/400000000 : ℝ), (4970859993/10000000000 : ℝ)] ![(37082185249941/100000000000000 : ℝ), (5552033816781/25000000000000 : ℝ), (40709679468221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1155703339/2500000000 : ℝ)|^9 ≤ (37082185249941/100000000000000 : ℝ)^7
        have hw : |(1155703339/2500000000 : ℝ)|=(1155703339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124105669/400000000 : ℝ)|^9 ≤ (5552033816781/25000000000000 : ℝ)^7
        have hw : |(124105669/400000000 : ℝ)|=(124105669/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4970859993/10000000000 : ℝ)|^9 ≤ (40709679468221/100000000000000 : ℝ)^7
        have hw : |(4970859993/10000000000 : ℝ)|=(4970859993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (288925819/625000000 : ℝ)*x 0 + (-1118394563/5000000000 : ℝ)*x 1 + (-5681129071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (288925819/625000000 : ℝ)^9 ≤ (7416436530191/20000000000000 : ℝ)^7 := by
    have hnat : (288925819 : ℕ)^9*20000000000000^7 ≤ 7416436530191^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288925819 625000000 7416436530191 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118394563/5000000000 : ℝ)^9 ≤ (1822693477401/12500000000000 : ℝ)^7 := by
    have hnat : (1118394563 : ℕ)^9*12500000000000^7 ≤ 1822693477401^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118394563 5000000000 1822693477401 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5681129071/10000000000 : ℝ)^9 ≤ (48336269510003/100000000000000 : ℝ)^7 := by
    have hnat : (5681129071 : ℕ)^9*100000000000000^7 ≤ 48336269510003^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681129071 10000000000 48336269510003 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(288925819/625000000 : ℝ), (-1118394563/5000000000 : ℝ), (-5681129071/10000000000 : ℝ)] ![(7416436530191/20000000000000 : ℝ), (1822693477401/12500000000000 : ℝ), (48336269510003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(288925819/625000000 : ℝ)|^9 ≤ (7416436530191/20000000000000 : ℝ)^7
        have hw : |(288925819/625000000 : ℝ)|=(288925819/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118394563/5000000000 : ℝ)|^9 ≤ (1822693477401/12500000000000 : ℝ)^7
        have hw : |(-1118394563/5000000000 : ℝ)|=(1118394563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5681129071/10000000000 : ℝ)|^9 ≤ (48336269510003/100000000000000 : ℝ)^7
        have hw : |(-5681129071/10000000000 : ℝ)|=(5681129071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (672991833/1000000000 : ℝ)*x 0 + (-43638433/2000000000 : ℝ)*x 1 + (1205982349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672991833/1000000000 : ℝ)^9 ≤ (60099344479911/100000000000000 : ℝ)^7 := by
    have hnat : (672991833 : ℕ)^9*100000000000000^7 ≤ 60099344479911^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672991833 1000000000 60099344479911 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43638433/2000000000 : ℝ)^9 ≤ (91439065577/12500000000000 : ℝ)^7 := by
    have hnat : (43638433 : ℕ)^9*12500000000000^7 ≤ 91439065577^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43638433 2000000000 91439065577 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205982349/2500000000 : ℝ)^9 ≤ (19584571488261/50000000000000 : ℝ)^7 := by
    have hnat : (1205982349 : ℕ)^9*50000000000000^7 ≤ 19584571488261^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205982349 2500000000 19584571488261 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672991833/1000000000 : ℝ), (-43638433/2000000000 : ℝ), (1205982349/2500000000 : ℝ)] ![(60099344479911/100000000000000 : ℝ), (91439065577/12500000000000 : ℝ), (19584571488261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672991833/1000000000 : ℝ)|^9 ≤ (60099344479911/100000000000000 : ℝ)^7
        have hw : |(672991833/1000000000 : ℝ)|=(672991833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43638433/2000000000 : ℝ)|^9 ≤ (91439065577/12500000000000 : ℝ)^7
        have hw : |(-43638433/2000000000 : ℝ)|=(43638433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205982349/2500000000 : ℝ)|^9 ≤ (19584571488261/50000000000000 : ℝ)^7
        have hw : |(1205982349/2500000000 : ℝ)|=(1205982349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1468067/2000000000 : ℝ)*x 0 + (-6908270043/10000000000 : ℝ)*x 1 + (1173931223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1468067/2000000000 : ℝ)^9 ≤ (1867394727/20000000000000 : ℝ)^7 := by
    have hnat : (1468067 : ℕ)^9*20000000000000^7 ≤ 1867394727^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468067 2000000000 1867394727 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6908270043/10000000000 : ℝ)^9 ≤ (62154821225059/100000000000000 : ℝ)^7 := by
    have hnat : (6908270043 : ℕ)^9*100000000000000^7 ≤ 62154821225059^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6908270043 10000000000 62154821225059 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1173931223/2500000000 : ℝ)^9 ≤ (37835841783819/100000000000000 : ℝ)^7 := by
    have hnat : (1173931223 : ℕ)^9*100000000000000^7 ≤ 37835841783819^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173931223 2500000000 37835841783819 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1468067/2000000000 : ℝ), (-6908270043/10000000000 : ℝ), (1173931223/2500000000 : ℝ)] ![(1867394727/20000000000000 : ℝ), (62154821225059/100000000000000 : ℝ), (37835841783819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1468067/2000000000 : ℝ)|^9 ≤ (1867394727/20000000000000 : ℝ)^7
        have hw : |(-1468067/2000000000 : ℝ)|=(1468067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6908270043/10000000000 : ℝ)|^9 ≤ (62154821225059/100000000000000 : ℝ)^7
        have hw : |(-6908270043/10000000000 : ℝ)|=(6908270043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1173931223/2500000000 : ℝ)|^9 ≤ (37835841783819/100000000000000 : ℝ)^7
        have hw : |(1173931223/2500000000 : ℝ)|=(1173931223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (872725953/2000000000 : ℝ)*x 0 + (1598929933/5000000000 : ℝ)*x 1 + (1284569949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872725953/2000000000 : ℝ)^9 ≤ (34430814312601/100000000000000 : ℝ)^7 := by
    have hnat : (872725953 : ℕ)^9*100000000000000^7 ≤ 34430814312601^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872725953 2000000000 34430814312601 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1598929933/5000000000 : ℝ)^9 ≤ (4617646571011/20000000000000 : ℝ)^7 := by
    have hnat : (1598929933 : ℕ)^9*20000000000000^7 ≤ 4617646571011^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598929933 5000000000 4617646571011 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284569949/2500000000 : ℝ)^9 ≤ (8496190563967/20000000000000 : ℝ)^7 := by
    have hnat : (1284569949 : ℕ)^9*20000000000000^7 ≤ 8496190563967^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284569949 2500000000 8496190563967 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872725953/2000000000 : ℝ), (1598929933/5000000000 : ℝ), (1284569949/2500000000 : ℝ)] ![(34430814312601/100000000000000 : ℝ), (4617646571011/20000000000000 : ℝ), (8496190563967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872725953/2000000000 : ℝ)|^9 ≤ (34430814312601/100000000000000 : ℝ)^7
        have hw : |(872725953/2000000000 : ℝ)|=(872725953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1598929933/5000000000 : ℝ)|^9 ≤ (4617646571011/20000000000000 : ℝ)^7
        have hw : |(1598929933/5000000000 : ℝ)|=(1598929933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284569949/2500000000 : ℝ)|^9 ≤ (8496190563967/20000000000000 : ℝ)^7
        have hw : |(1284569949/2500000000 : ℝ)|=(1284569949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5986653979/10000000000 : ℝ)*x 0 + (-2431460077/10000000000 : ℝ)*x 1 + (-51605071/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5986653979/10000000000 : ℝ)^9 ≤ (51703802957857/100000000000000 : ℝ)^7 := by
    have hnat : (5986653979 : ℕ)^9*100000000000000^7 ≤ 51703802957857^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5986653979 10000000000 51703802957857 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2431460077/10000000000 : ℝ)^9 ≤ (3246613635037/20000000000000 : ℝ)^7 := by
    have hnat : (2431460077 : ℕ)^9*20000000000000^7 ≤ 3246613635037^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431460077 10000000000 3246613635037 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51605071/125000000 : ℝ)^9 ≤ (6412625769919/20000000000000 : ℝ)^7 := by
    have hnat : (51605071 : ℕ)^9*20000000000000^7 ≤ 6412625769919^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51605071 125000000 6412625769919 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5986653979/10000000000 : ℝ), (-2431460077/10000000000 : ℝ), (-51605071/125000000 : ℝ)] ![(51703802957857/100000000000000 : ℝ), (3246613635037/20000000000000 : ℝ), (6412625769919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5986653979/10000000000 : ℝ)|^9 ≤ (51703802957857/100000000000000 : ℝ)^7
        have hw : |(5986653979/10000000000 : ℝ)|=(5986653979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2431460077/10000000000 : ℝ)|^9 ≤ (3246613635037/20000000000000 : ℝ)^7
        have hw : |(-2431460077/10000000000 : ℝ)|=(2431460077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51605071/125000000 : ℝ)|^9 ≤ (6412625769919/20000000000000 : ℝ)^7
        have hw : |(-51605071/125000000 : ℝ)|=(51605071/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (9200402687/10000000000 : ℝ)*x 0 + (-822178389/10000000000 : ℝ)*x 1 + (1140605057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9200402687/10000000000 : ℝ)^9 ≤ (89839211628809/100000000000000 : ℝ)^7 := by
    have hnat : (9200402687 : ℕ)^9*100000000000000^7 ≤ 89839211628809^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9200402687 10000000000 89839211628809 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (822178389/10000000000 : ℝ)^9 ≤ (4026765686549/100000000000000 : ℝ)^7 := by
    have hnat : (822178389 : ℕ)^9*100000000000000^7 ≤ 4026765686549^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822178389 10000000000 4026765686549 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140605057/10000000000 : ℝ)^9 ≤ (1533505666377/25000000000000 : ℝ)^7 := by
    have hnat : (1140605057 : ℕ)^9*25000000000000^7 ≤ 1533505666377^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140605057 10000000000 1533505666377 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9200402687/10000000000 : ℝ), (-822178389/10000000000 : ℝ), (1140605057/10000000000 : ℝ)] ![(89839211628809/100000000000000 : ℝ), (4026765686549/100000000000000 : ℝ), (1533505666377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9200402687/10000000000 : ℝ)|^9 ≤ (89839211628809/100000000000000 : ℝ)^7
        have hw : |(9200402687/10000000000 : ℝ)|=(9200402687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-822178389/10000000000 : ℝ)|^9 ≤ (4026765686549/100000000000000 : ℝ)^7
        have hw : |(-822178389/10000000000 : ℝ)|=(822178389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140605057/10000000000 : ℝ)|^9 ≤ (1533505666377/25000000000000 : ℝ)^7
        have hw : |(1140605057/10000000000 : ℝ)|=(1140605057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-585909/312500000 : ℝ)*x 0 + (-2068550917/2500000000 : ℝ)*x 1 + (1517428139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (585909/312500000 : ℝ)^9 ≤ (3117680583/10000000000000 : ℝ)^7 := by
    have hnat : (585909 : ℕ)^9*10000000000000^7 ≤ 3117680583^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585909 312500000 3117680583 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068550917/2500000000 : ℝ)^9 ≤ (15676510741341/20000000000000 : ℝ)^7 := by
    have hnat : (2068550917 : ℕ)^9*20000000000000^7 ≤ 15676510741341^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068550917 2500000000 15676510741341 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1517428139/5000000000 : ℝ)^9 ≤ (2698283684747/12500000000000 : ℝ)^7 := by
    have hnat : (1517428139 : ℕ)^9*12500000000000^7 ≤ 2698283684747^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517428139 5000000000 2698283684747 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-585909/312500000 : ℝ), (-2068550917/2500000000 : ℝ), (1517428139/5000000000 : ℝ)] ![(3117680583/10000000000000 : ℝ), (15676510741341/20000000000000 : ℝ), (2698283684747/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-585909/312500000 : ℝ)|^9 ≤ (3117680583/10000000000000 : ℝ)^7
        have hw : |(-585909/312500000 : ℝ)|=(585909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068550917/2500000000 : ℝ)|^9 ≤ (15676510741341/20000000000000 : ℝ)^7
        have hw : |(-2068550917/2500000000 : ℝ)|=(2068550917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1517428139/5000000000 : ℝ)|^9 ≤ (2698283684747/12500000000000 : ℝ)^7
        have hw : |(1517428139/5000000000 : ℝ)|=(1517428139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5975245191/10000000000 : ℝ)*x 0 + (2816409251/10000000000 : ℝ)*x 1 + (949782771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5975245191/10000000000 : ℝ)^9 ≤ (25788576652093/50000000000000 : ℝ)^7 := by
    have hnat : (5975245191 : ℕ)^9*50000000000000^7 ≤ 25788576652093^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5975245191 10000000000 25788576652093 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816409251/10000000000 : ℝ)^9 ≤ (9804737801889/50000000000000 : ℝ)^7 := by
    have hnat : (2816409251 : ℕ)^9*50000000000000^7 ≤ 9804737801889^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816409251 10000000000 9804737801889 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949782771/2500000000 : ℝ)^9 ≤ (900417846277/3125000000000 : ℝ)^7 := by
    have hnat : (949782771 : ℕ)^9*3125000000000^7 ≤ 900417846277^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949782771 2500000000 900417846277 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5975245191/10000000000 : ℝ), (2816409251/10000000000 : ℝ), (949782771/2500000000 : ℝ)] ![(25788576652093/50000000000000 : ℝ), (9804737801889/50000000000000 : ℝ), (900417846277/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5975245191/10000000000 : ℝ)|^9 ≤ (25788576652093/50000000000000 : ℝ)^7
        have hw : |(5975245191/10000000000 : ℝ)|=(5975245191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816409251/10000000000 : ℝ)|^9 ≤ (9804737801889/50000000000000 : ℝ)^7
        have hw : |(2816409251/10000000000 : ℝ)|=(2816409251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(949782771/2500000000 : ℝ)|^9 ≤ (900417846277/3125000000000 : ℝ)^7
        have hw : |(949782771/2500000000 : ℝ)|=(949782771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4383284983/10000000000 : ℝ)*x 0 + (-1627444797/5000000000 : ℝ)*x 1 + (-1267361891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4383284983/10000000000 : ℝ)^9 ≤ (34630340912631/100000000000000 : ℝ)^7 := by
    have hnat : (4383284983 : ℕ)^9*100000000000000^7 ≤ 34630340912631^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383284983 10000000000 34630340912631 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1627444797/5000000000 : ℝ)^9 ≤ (4723793495061/20000000000000 : ℝ)^7 := by
    have hnat : (1627444797 : ℕ)^9*20000000000000^7 ≤ 4723793495061^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627444797 5000000000 4723793495061 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267361891/2500000000 : ℝ)^9 ≤ (10437672899019/25000000000000 : ℝ)^7 := by
    have hnat : (1267361891 : ℕ)^9*25000000000000^7 ≤ 10437672899019^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267361891 2500000000 10437672899019 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4383284983/10000000000 : ℝ), (-1627444797/5000000000 : ℝ), (-1267361891/2500000000 : ℝ)] ![(34630340912631/100000000000000 : ℝ), (4723793495061/20000000000000 : ℝ), (10437672899019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4383284983/10000000000 : ℝ)|^9 ≤ (34630340912631/100000000000000 : ℝ)^7
        have hw : |(4383284983/10000000000 : ℝ)|=(4383284983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1627444797/5000000000 : ℝ)|^9 ≤ (4723793495061/20000000000000 : ℝ)^7
        have hw : |(-1627444797/5000000000 : ℝ)|=(1627444797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1267361891/2500000000 : ℝ)|^9 ≤ (10437672899019/25000000000000 : ℝ)^7
        have hw : |(-1267361891/2500000000 : ℝ)|=(1267361891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s0_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4578228221/5000000000 : ℝ)*x 0 + (-142032427/5000000000 : ℝ)*x 1 + (1627115837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4578228221/5000000000 : ℝ)^9 ≤ (89287860140201/100000000000000 : ℝ)^7 := by
    have hnat : (4578228221 : ℕ)^9*100000000000000^7 ≤ 89287860140201^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578228221 5000000000 89287860140201 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142032427/5000000000 : ℝ)^9 ≤ (1026920422133/100000000000000 : ℝ)^7 := by
    have hnat : (142032427 : ℕ)^9*100000000000000^7 ≤ 1026920422133^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142032427 5000000000 1026920422133 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1627115837/10000000000 : ℝ)^9 ≤ (4842609710439/50000000000000 : ℝ)^7 := by
    have hnat : (1627115837 : ℕ)^9*50000000000000^7 ≤ 4842609710439^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627115837 10000000000 4842609710439 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4578228221/5000000000 : ℝ), (-142032427/5000000000 : ℝ), (1627115837/10000000000 : ℝ)] ![(89287860140201/100000000000000 : ℝ), (1026920422133/100000000000000 : ℝ), (4842609710439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4578228221/5000000000 : ℝ)|^9 ≤ (89287860140201/100000000000000 : ℝ)^7
        have hw : |(4578228221/5000000000 : ℝ)|=(4578228221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142032427/5000000000 : ℝ)|^9 ≤ (1026920422133/100000000000000 : ℝ)^7
        have hw : |(-142032427/5000000000 : ℝ)|=(142032427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1627115837/10000000000 : ℝ)|^9 ≤ (4842609710439/50000000000000 : ℝ)^7
        have hw : |(1627115837/10000000000 : ℝ)|=(1627115837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2270915671/10000000000 : ℝ)*x 0 + (-5814578179/10000000000 : ℝ)*x 1 + (2226046311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2270915671/10000000000 : ℝ)^9 ≤ (14868201490381/100000000000000 : ℝ)^7 := by
    have hnat : (2270915671 : ℕ)^9*100000000000000^7 ≤ 14868201490381^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270915671 10000000000 14868201490381 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5814578179/10000000000 : ℝ)^9 ≤ (49800958768919/100000000000000 : ℝ)^7 := by
    have hnat : (5814578179 : ℕ)^9*100000000000000^7 ≤ 49800958768919^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5814578179 10000000000 49800958768919 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226046311/5000000000 : ℝ)^9 ≤ (17665419865157/50000000000000 : ℝ)^7 := by
    have hnat : (2226046311 : ℕ)^9*50000000000000^7 ≤ 17665419865157^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226046311 5000000000 17665419865157 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2270915671/10000000000 : ℝ), (-5814578179/10000000000 : ℝ), (2226046311/5000000000 : ℝ)] ![(14868201490381/100000000000000 : ℝ), (49800958768919/100000000000000 : ℝ), (17665419865157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2270915671/10000000000 : ℝ)|^9 ≤ (14868201490381/100000000000000 : ℝ)^7
        have hw : |(-2270915671/10000000000 : ℝ)|=(2270915671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5814578179/10000000000 : ℝ)|^9 ≤ (49800958768919/100000000000000 : ℝ)^7
        have hw : |(-5814578179/10000000000 : ℝ)|=(5814578179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2226046311/5000000000 : ℝ)|^9 ≤ (17665419865157/50000000000000 : ℝ)^7
        have hw : |(2226046311/5000000000 : ℝ)|=(2226046311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4868701067/10000000000 : ℝ)*x 0 + (1747344569/5000000000 : ℝ)*x 1 + (2184409021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4868701067/10000000000 : ℝ)^9 ≤ (1981858184537/5000000000000 : ℝ)^7 := by
    have hnat : (4868701067 : ℕ)^9*5000000000000^7 ≤ 1981858184537^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4868701067 10000000000 1981858184537 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1747344569/5000000000 : ℝ)^9 ≤ (25879378961789/100000000000000 : ℝ)^7 := by
    have hnat : (1747344569 : ℕ)^9*100000000000000^7 ≤ 25879378961789^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747344569 5000000000 25879378961789 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184409021/5000000000 : ℝ)^9 ≤ (34483457328603/100000000000000 : ℝ)^7 := by
    have hnat : (2184409021 : ℕ)^9*100000000000000^7 ≤ 34483457328603^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184409021 5000000000 34483457328603 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4868701067/10000000000 : ℝ), (1747344569/5000000000 : ℝ), (2184409021/5000000000 : ℝ)] ![(1981858184537/5000000000000 : ℝ), (25879378961789/100000000000000 : ℝ), (34483457328603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4868701067/10000000000 : ℝ)|^9 ≤ (1981858184537/5000000000000 : ℝ)^7
        have hw : |(4868701067/10000000000 : ℝ)|=(4868701067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1747344569/5000000000 : ℝ)|^9 ≤ (25879378961789/100000000000000 : ℝ)^7
        have hw : |(1747344569/5000000000 : ℝ)|=(1747344569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2184409021/5000000000 : ℝ)|^9 ≤ (34483457328603/100000000000000 : ℝ)^7
        have hw : |(2184409021/5000000000 : ℝ)|=(2184409021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (951126389/2000000000 : ℝ)*x 0 + (-1773845097/5000000000 : ℝ)*x 1 + (-69298067/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951126389/2000000000 : ℝ)^9 ≤ (38457585769919/100000000000000 : ℝ)^7 := by
    have hnat : (951126389 : ℕ)^9*100000000000000^7 ≤ 38457585769919^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951126389 2000000000 38457585769919 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1773845097/5000000000 : ℝ)^9 ≤ (26385099796841/100000000000000 : ℝ)^7 := by
    have hnat : (1773845097 : ℕ)^9*100000000000000^7 ≤ 26385099796841^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773845097 5000000000 26385099796841 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69298067/156250000 : ℝ)^9 ≤ (17578657210393/50000000000000 : ℝ)^7 := by
    have hnat : (69298067 : ℕ)^9*50000000000000^7 ≤ 17578657210393^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69298067 156250000 17578657210393 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(951126389/2000000000 : ℝ), (-1773845097/5000000000 : ℝ), (-69298067/156250000 : ℝ)] ![(38457585769919/100000000000000 : ℝ), (26385099796841/100000000000000 : ℝ), (17578657210393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(951126389/2000000000 : ℝ)|^9 ≤ (38457585769919/100000000000000 : ℝ)^7
        have hw : |(951126389/2000000000 : ℝ)|=(951126389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1773845097/5000000000 : ℝ)|^9 ≤ (26385099796841/100000000000000 : ℝ)^7
        have hw : |(-1773845097/5000000000 : ℝ)|=(1773845097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69298067/156250000 : ℝ)|^9 ≤ (17578657210393/50000000000000 : ℝ)^7
        have hw : |(-69298067/156250000 : ℝ)|=(69298067/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310037_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5921983107/10000000000 : ℝ)*x 0 + (-3784631579/10000000000 : ℝ)*x 1 + (181112991/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5921983107/10000000000 : ℝ)^9 ≤ (25493401562147/50000000000000 : ℝ)^7 := by
    have hnat : (5921983107 : ℕ)^9*50000000000000^7 ≤ 25493401562147^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5921983107 10000000000 25493401562147 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3784631579/10000000000 : ℝ)^9 ≤ (7168015475429/25000000000000 : ℝ)^7 := by
    have hnat : (3784631579 : ℕ)^9*25000000000000^7 ≤ 7168015475429^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3784631579 10000000000 7168015475429 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181112991/625000000 : ℝ)^9 ≤ (1017056748067/5000000000000 : ℝ)^7 := by
    have hnat : (181112991 : ℕ)^9*5000000000000^7 ≤ 1017056748067^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181112991 625000000 1017056748067 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5921983107/10000000000 : ℝ), (-3784631579/10000000000 : ℝ), (181112991/625000000 : ℝ)] ![(25493401562147/50000000000000 : ℝ), (7168015475429/25000000000000 : ℝ), (1017056748067/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5921983107/10000000000 : ℝ)|^9 ≤ (25493401562147/50000000000000 : ℝ)^7
        have hw : |(5921983107/10000000000 : ℝ)|=(5921983107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3784631579/10000000000 : ℝ)|^9 ≤ (7168015475429/25000000000000 : ℝ)^7
        have hw : |(-3784631579/10000000000 : ℝ)|=(3784631579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181112991/625000000 : ℝ)|^9 ≤ (1017056748067/5000000000000 : ℝ)^7
        have hw : |(181112991/625000000 : ℝ)|=(181112991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310037 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-925593833/10000000000 : ℝ)*X 0 0+(-7264482089/10000000000 : ℝ)*X 0 1+(1909397877/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4971558703/10000000000 : ℝ)*X 2 0+(-385565769/1250000000 : ℝ)*X 2 1+(-927648811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-262713797/5000000000 : ℝ)*X 0 0+(-903553357/1000000000 : ℝ)*X 0 1+(103939721/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1155703339/2500000000 : ℝ)*X 1 0+(124105669/400000000 : ℝ)*X 1 1+(4970859993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((288925819/625000000 : ℝ)*X 2 0+(-1118394563/5000000000 : ℝ)*X 2 1+(-5681129071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((672991833/1000000000 : ℝ)*X 0 0+(-43638433/2000000000 : ℝ)*X 0 1+(1205982349/2500000000 : ℝ)*X 0 2+(672991833/1000000000 : ℝ)*X 1 0+(-43638433/2000000000 : ℝ)*X 1 1+(1205982349/2500000000 : ℝ)*X 1 2+(672991833/1000000000 : ℝ)*X 2 0+(-43638433/2000000000 : ℝ)*X 2 1+(1205982349/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1468067/2000000000 : ℝ)*X 0 0+(-6908270043/10000000000 : ℝ)*X 0 1+(1173931223/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((872725953/2000000000 : ℝ)*X 1 0+(1598929933/5000000000 : ℝ)*X 1 1+(1284569949/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5986653979/10000000000 : ℝ)*X 2 0+(-2431460077/10000000000 : ℝ)*X 2 1+(-51605071/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((9200402687/10000000000 : ℝ)*X 0 0+(-822178389/10000000000 : ℝ)*X 0 1+(1140605057/10000000000 : ℝ)*X 0 2+(9200402687/10000000000 : ℝ)*X 1 0+(-822178389/10000000000 : ℝ)*X 1 1+(1140605057/10000000000 : ℝ)*X 1 2+(9200402687/10000000000 : ℝ)*X 2 0+(-822178389/10000000000 : ℝ)*X 2 1+(1140605057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-585909/312500000 : ℝ)*X 0 0+(-2068550917/2500000000 : ℝ)*X 0 1+(1517428139/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5975245191/10000000000 : ℝ)*X 1 0+(2816409251/10000000000 : ℝ)*X 1 1+(949782771/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4383284983/10000000000 : ℝ)*X 2 0+(-1627444797/5000000000 : ℝ)*X 2 1+(-1267361891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4578228221/5000000000 : ℝ)*X 0 0+(-142032427/5000000000 : ℝ)*X 0 1+(1627115837/10000000000 : ℝ)*X 0 2+(4578228221/5000000000 : ℝ)*X 1 0+(-142032427/5000000000 : ℝ)*X 1 1+(1627115837/10000000000 : ℝ)*X 1 2+(4578228221/5000000000 : ℝ)*X 2 0+(-142032427/5000000000 : ℝ)*X 2 1+(1627115837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((30999/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30999/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (449492651480261405787/39062500000000000000000000 : ℝ) := by norm_num
    linear_combination (3817473/1000000000000 : ℝ)*(base3) + (42663831171/125000000000 : ℝ)*(base40) + (475074528283/500000000000 : ℝ)*(base49) + (196726610653/500000000000 : ℝ)*(base59) + (331528344347/125000000000 : ℝ)*(major_s0_0) + (331528344347/125000000000 : ℝ)*(major_s0_1) + (331528344347/125000000000 : ℝ)*(major_s0_2) + (183256559989/50000000000 : ℝ)*(sp_s0_7) + (3665049399907/1000000000000 : ℝ)*(sp_s0_8) + (916278061269/250000000000 : ℝ)*(sp_s0_9) + (819633908257/500000000000 : ℝ)*(sp_s0_13) + (132457457/1000000000000 : ℝ)*(sp_s0_15) + (46840111/1000000000000 : ℝ)*(sp_s0_21) + (13158963/200000000000 : ℝ)*(sp_s0_23) + (1639271633987/1000000000000 : ℝ)*(f.failure) + (3665178039891/1000000000000 : ℝ)*(f.sum) + (228804530866841/625000000000000000000000000 : ℝ)*base62 + (679379827655227/1250000000000000000000000000 : ℝ)*base65 + (75686197655227/1250000000000000000000000000 : ℝ)*base67 + (503768949741841/1250000000000000000000000000 : ℝ)*base68 + (106373253456693/625000000000000000000000000 : ℝ)*base71 + (90748628780227/1250000000000000000000000000 : ℝ)*base72 + (618128143741841/1250000000000000000000000000 : ℝ)*base74 + (177471623116841/1250000000000000000000000000 : ℝ)*base76 + (668367439/1250000000000000000000 : ℝ)*base79 + (58691/100000000000000000 : ℝ)*base87 + (58691/100000000000000000 : ℝ)*base89 + (58691/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-24141/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-24141/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17035835144813569313781/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185481/250000000000 : ℝ)*(base39) + (148561857811/100000000000 : ℝ)*(base40) + (743716001011/1000000000000 : ℝ)*(base49) + (69593/40000000000 : ℝ)*(base53) + (1650687/1000000000000 : ℝ)*(base60) + (4458521376803/1000000000000 : ℝ)*(major_s0_0) + (4458521376803/1000000000000 : ℝ)*(major_s0_1) + (4458519636979/1000000000000 : ℝ)*(major_s0_2) + (6608373/50000000000 : ℝ)*(sp_s0_8) + (6161343887299/1000000000000 : ℝ)*(sp_s0_14) + (6161211719839/1000000000000 : ℝ)*(sp_s0_15) + (1540336406781/250000000000 : ℝ)*(sp_s0_16) + (344452498329/125000000000 : ℝ)*(sp_s0_20) + (74868401/1000000000000 : ℝ)*(sp_s0_27) + (2755694855033/1000000000000 : ℝ)*(f.failure) + (1540336406781/250000000000 : ℝ)*(f.sum) + (1165021051562073/5000000000000000000000000000 : ℝ)*base62 + (132906067175139/10000000000000000000000000000 : ℝ)*base65 + (3203243330811923/10000000000000000000000000000 : ℝ)*base67 + (3782268805367537/10000000000000000000000000000 : ℝ)*base68 + (391700992158147/1000000000000000000000000000 : ℝ)*base70 + (11024180015188077/10000000000000000000000000000 : ℝ)*base73 + (5883177879756609/10000000000000000000000000000 : ℝ)*base74 + (90220792243391/10000000000000000000000000000 : ℝ)*base77 + (8194099659/10000000000000000000000 : ℝ)*base79 + (54169/100000000000000000 : ℝ)*base87 + (54169/100000000000000000 : ℝ)*base89 + (45831/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28917/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28917/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17538491957574502543641/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (820389784071/500000000000 : ℝ)*(base40) + (135812006241/125000000000 : ℝ)*(base49) + (4292089959/20000000000 : ℝ)*(base59) + (4545515746649/1000000000000 : ℝ)*(major_s0_0) + (4545515746649/1000000000000 : ℝ)*(major_s0_1) + (4545515746649/1000000000000 : ℝ)*(major_s0_2) + (1709397/1000000000000 : ℝ)*(sp_s0_0) + (6747167/1000000000000 : ℝ)*(sp_s0_2) + (10989657/1000000000000 : ℝ)*(sp_s0_7) + (817187/40000000000 : ℝ)*(sp_s0_20) + (1570388459231/250000000000 : ℝ)*(sp_s0_21) + (3140783267989/500000000000 : ℝ)*(sp_s0_22) + (6281559788811/1000000000000 : ℝ)*(sp_s0_23) + (561888671681/200000000000 : ℝ)*(sp_s0_27) + (35118297351/12500000000 : ℝ)*(f.failure) + (3140783267989/500000000000 : ℝ)*(f.sum) + (2001859940985453/5000000000000000000000000000 : ℝ)*base63 + (1119985396741609/10000000000000000000000000000 : ℝ)*base65 + (4809294074741609/10000000000000000000000000000 : ℝ)*base67 + (2966327639985453/10000000000000000000000000000 : ℝ)*base69 + (1816509481636469/5000000000000000000000000000 : ℝ)*base70 + (3331152491258391/10000000000000000000000000000 : ℝ)*base73 + (3312139823985453/10000000000000000000000000000 : ℝ)*base75 + (2928823264014547/10000000000000000000000000000 : ℝ)*base76 + (9643822129/10000000000000000000000 : ℝ)*base79 + (907/1250000000000000 : ℝ)*base86 + (907/1250000000000000 : ℝ)*base88 + (907/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (30999/100000 : ℝ) ^ (35/8 : ℝ) ≤ (59517696981687143/10000000000000000000 : ℝ) := by
    have hpowers : (30999/100000 : ℝ)^35 ≤ (59517696981687143/10000000000000000000 : ℝ)^8 := by
      have hnat : (30999 : ℕ)^35*10000000000000000000^8 ≤ 59517696981687143^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30999 100000 59517696981687143 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30999/100000 : ℝ)) (X := (59517696981687143/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10059517696981687143/10000000000000000000 : ℝ) ≤ (10013572923760417/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (10059517696981687143/10000000000000000000 : ℝ)^8 ≤ (10013572923760417/10000000000000000 : ℝ)^35 := by
      have hnat : (10059517696981687143 : ℕ)^8*10000000000000000^35 ≤ 10013572923760417^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10059517696981687143 10000000000000000000 10013572923760417 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013572923760417/10000000000000000 : ℝ)) (X := (10059517696981687143/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5059517696981687143/5000000000000000000 : ℝ) ≤ (156673188103783/156250000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5059517696981687143/5000000000000000000 : ℝ)^8 ≤ (156673188103783/156250000000000 : ℝ)^35 := by
      have hnat : (5059517696981687143 : ℕ)^8*156250000000000^35 ≤ 156673188103783^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5059517696981687143 5000000000000000000 156673188103783 156250000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156673188103783/156250000000000 : ℝ)) (X := (5059517696981687143/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4524307920139/1033300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(900740992113/206660000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (30999/100000 : ℝ)) (alpha := (4524307920139/1033300000000000 : ℝ)) (beta := (900740992113/206660000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (30999/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4524307920139/1033300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(900740992113/206660000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (24141/50000 : ℝ) ^ (35/8 : ℝ) ≤ (1033952255427789559/25000000000000000000 : ℝ) := by
    have hpowers : (24141/50000 : ℝ)^35 ≤ (1033952255427789559/25000000000000000000 : ℝ)^8 := by
      have hnat : (24141 : ℕ)^35*25000000000000000000^8 ≤ 1033952255427789559^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24141 50000 1033952255427789559 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24141/50000 : ℝ)) (X := (1033952255427789559/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (26033952255427789559/25000000000000000000 : ℝ) ≤ (10093060556379211/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (26033952255427789559/25000000000000000000 : ℝ)^8 ≤ (10093060556379211/10000000000000000 : ℝ)^35 := by
      have hnat : (26033952255427789559 : ℕ)^8*10000000000000000^35 ≤ 10093060556379211^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26033952255427789559 25000000000000000000 10093060556379211 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10093060556379211/10000000000000000 : ℝ)) (X := (26033952255427789559/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13533952255427789559/12500000000000000000 : ℝ) ≤ (10183312177486577/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (13533952255427789559/12500000000000000000 : ℝ)^8 ≤ (10183312177486577/10000000000000000 : ℝ)^35 := by
      have hnat : (13533952255427789559 : ℕ)^8*10000000000000000^35 ≤ 10183312177486577^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13533952255427789559 12500000000000000000 10183312177486577 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10183312177486577/10000000000000000 : ℝ)) (X := (13533952255427789559/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(31020185459737/1609400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(45125810553683/2414100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (24141/50000 : ℝ)) (alpha := (31020185459737/1609400000000000 : ℝ)) (beta := (45125810553683/2414100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (24141/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(31020185459737/1609400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(45125810553683/2414100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (28917/50000 : ℝ) ^ (35/8 : ℝ) ≤ (4555348823408617071/50000000000000000000 : ℝ) := by
    have hpowers : (28917/50000 : ℝ)^35 ≤ (4555348823408617071/50000000000000000000 : ℝ)^8 := by
      have hnat : (28917 : ℕ)^35*50000000000000000000^8 ≤ 4555348823408617071^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28917 50000 4555348823408617071 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28917/50000 : ℝ)) (X := (4555348823408617071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (54555348823408617071/50000000000000000000 : ℝ) ≤ (102012969657387/100000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (54555348823408617071/50000000000000000000 : ℝ)^8 ≤ (102012969657387/100000000000000 : ℝ)^35 := by
      have hnat : (54555348823408617071 : ℕ)^8*100000000000000^35 ≤ 102012969657387^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54555348823408617071 50000000000000000000 102012969657387 100000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (102012969657387/100000000000000 : ℝ)) (X := (54555348823408617071/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (29555348823408617071/25000000000000000000 : ℝ) ≤ (10390016734073487/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (29555348823408617071/25000000000000000000 : ℝ)^8 ≤ (10390016734073487/10000000000000000 : ℝ)^35 := by
      have hnat : (29555348823408617071 : ℕ)^8*10000000000000000^35 ≤ 10390016734073487^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29555348823408617071 25000000000000000000 10390016734073487 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10390016734073487/10000000000000000 : ℝ)) (X := (29555348823408617071/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2012969657387/57834000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(62906589444929/1927800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (28917/50000 : ℝ)) (alpha := (2012969657387/57834000000000 : ℝ)) (beta := (62906589444929/1927800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (28917/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2012969657387/57834000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(62906589444929/1927800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2270915671/10000000000 : ℝ)*X 0 0+(-5814578179/10000000000 : ℝ)*X 0 1+(2226046311/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4868701067/10000000000 : ℝ)*X 1 0+(1747344569/5000000000 : ℝ)*X 1 1+(2184409021/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((951126389/2000000000 : ℝ)*X 2 0+(-1773845097/5000000000 : ℝ)*X 2 1+(-69298067/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5921983107/10000000000 : ℝ)*X 0 0+(-3784631579/10000000000 : ℝ)*X 0 1+(181112991/625000000 : ℝ)*X 0 2+(5921983107/10000000000 : ℝ)*X 1 0+(-3784631579/10000000000 : ℝ)*X 1 1+(181112991/625000000 : ℝ)*X 1 2+(5921983107/10000000000 : ℝ)*X 2 0+(-3784631579/10000000000 : ℝ)*X 2 1+(181112991/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310037_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-35624991207183044967754706198076421/5343196573260000000000000000000000 : ℝ) := by norm_num
    linear_combination (14853/500000000000 : ℝ)*(base10) + (79673378931/1000000000000 : ℝ)*(base39) + (22196284419/50000000000 : ℝ)*(base40) + (308449771029/1000000000000 : ℝ)*(base49) + (41/8000000000 : ℝ)*(base53) + (547/62500000000 : ℝ)*(base59) + (161793/100000 : ℝ)*(major_s1_0) + (2022412513/1250000000 : ℝ)*(major_s1_1) + (12943439959/8000000000 : ℝ)*(major_s1_2) + (1111225892099/500000000000 : ℝ)*(sp_s1_0) + (2222451800839/1000000000000 : ℝ)*(sp_s1_1) + (555612954091/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (555612951491/250000000000 : ℝ)*(f.sum) + (291798404700371897/2326950990000000000000000000000 : ℝ)*base63 + (456578919233977/385560000000000000000000000 : ℝ)*base65 + (160779963554190829/60352500000000000000000000 : ℝ)*base66 + (14160096429049/72292500000000000000000000 : ℝ)*base68 + (860856253757779189/3983991480000000000000000000000 : ℝ)*base71 + (39261315759873/51665000000000000000000000 : ℝ)*base73 + (499480238409/4023500000000000000000000 : ℝ)*base75 + (349716773391/12916250000000000000000000 : ℝ)*base77 + (84535099319397521/155905595625000000000000000000 : ℝ)*base79 + (2613/200000000000 : ℝ)*base81 + (13/1250000000 : ℝ)*base85 + (13/1250000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p010_b021 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=37 := by omega
  rcases hc with rfl
  · exact collision_c310037 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b021 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

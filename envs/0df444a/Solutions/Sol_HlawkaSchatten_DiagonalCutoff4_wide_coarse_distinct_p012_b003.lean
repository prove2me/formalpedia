-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:05.789667+00:00
-- url     : https://prove2.me/submissions/70f4f3f7-70ee-4477-bd0f-5bc485b5ac58

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
theorem collision_support_c312007_s0_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-594044873/2500000000 : ℝ)*x 0 + (-6453526477/10000000000 : ℝ)*x 1 + (3565240147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (594044873/2500000000 : ℝ)^37 ≤ (15984829198159/100000000000000 : ℝ)^29 := by
    have hnat : (594044873 : ℕ)^37*100000000000000^29 ≤ 15984829198159^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594044873 2500000000 15984829198159 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6453526477/10000000000 : ℝ)^37 ≤ (5719095249301/10000000000000 : ℝ)^29 := by
    have hnat : (6453526477 : ℕ)^37*10000000000000^29 ≤ 5719095249301^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6453526477 10000000000 5719095249301 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3565240147/10000000000 : ℝ)^37 ≤ (1072968731913/4000000000000 : ℝ)^29 := by
    have hnat : (3565240147 : ℕ)^37*4000000000000^29 ≤ 1072968731913^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3565240147 10000000000 1072968731913 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-594044873/2500000000 : ℝ), (-6453526477/10000000000 : ℝ), (3565240147/10000000000 : ℝ)] ![(15984829198159/100000000000000 : ℝ), (5719095249301/10000000000000 : ℝ), (1072968731913/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-594044873/2500000000 : ℝ)|^37 ≤ (15984829198159/100000000000000 : ℝ)^29
        have hw : |(-594044873/2500000000 : ℝ)|=(594044873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6453526477/10000000000 : ℝ)|^37 ≤ (5719095249301/10000000000000 : ℝ)^29
        have hw : |(-6453526477/10000000000 : ℝ)|=(6453526477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3565240147/10000000000 : ℝ)|^37 ≤ (1072968731913/4000000000000 : ℝ)^29
        have hw : |(3565240147/10000000000 : ℝ)|=(3565240147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1147841809/2000000000 : ℝ)*x 0 + (195890199/625000000 : ℝ)*x 1 + (737447167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147841809/2000000000 : ℝ)^37 ≤ (24620591018887/50000000000000 : ℝ)^29 := by
    have hnat : (1147841809 : ℕ)^37*50000000000000^29 ≤ 24620591018887^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147841809 2000000000 24620591018887 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195890199/625000000 : ℝ)^37 ≤ (2275803764563/10000000000000 : ℝ)^29 := by
    have hnat : (195890199 : ℕ)^37*10000000000000^29 ≤ 2275803764563^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195890199 625000000 2275803764563 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737447167/2000000000 : ℝ)^37 ≤ (28000780303037/100000000000000 : ℝ)^29 := by
    have hnat : (737447167 : ℕ)^37*100000000000000^29 ≤ 28000780303037^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737447167 2000000000 28000780303037 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1147841809/2000000000 : ℝ), (195890199/625000000 : ℝ), (737447167/2000000000 : ℝ)] ![(24620591018887/50000000000000 : ℝ), (2275803764563/10000000000000 : ℝ), (28000780303037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1147841809/2000000000 : ℝ)|^37 ≤ (24620591018887/50000000000000 : ℝ)^29
        have hw : |(1147841809/2000000000 : ℝ)|=(1147841809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195890199/625000000 : ℝ)|^37 ≤ (2275803764563/10000000000000 : ℝ)^29
        have hw : |(195890199/625000000 : ℝ)|=(195890199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(737447167/2000000000 : ℝ)|^37 ≤ (28000780303037/100000000000000 : ℝ)^29
        have hw : |(737447167/2000000000 : ℝ)|=(737447167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-210571477/1250000000 : ℝ)*x 0 + (-7634741517/10000000000 : ℝ)*x 1 + (675251611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210571477/1250000000 : ℝ)^37 ≤ (5153204011591/50000000000000 : ℝ)^29 := by
    have hnat : (210571477 : ℕ)^37*50000000000000^29 ≤ 5153204011591^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210571477 1250000000 5153204011591 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7634741517/10000000000 : ℝ)^37 ≤ (70869887231933/100000000000000 : ℝ)^29 := by
    have hnat : (7634741517 : ℕ)^37*100000000000000^29 ≤ 70869887231933^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7634741517 10000000000 70869887231933 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675251611/2500000000 : ℝ)^37 ≤ (18823704727367/100000000000000 : ℝ)^29 := by
    have hnat : (675251611 : ℕ)^37*100000000000000^29 ≤ 18823704727367^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675251611 2500000000 18823704727367 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210571477/1250000000 : ℝ), (-7634741517/10000000000 : ℝ), (675251611/2500000000 : ℝ)] ![(5153204011591/50000000000000 : ℝ), (70869887231933/100000000000000 : ℝ), (18823704727367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210571477/1250000000 : ℝ)|^37 ≤ (5153204011591/50000000000000 : ℝ)^29
        have hw : |(-210571477/1250000000 : ℝ)|=(210571477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7634741517/10000000000 : ℝ)|^37 ≤ (70869887231933/100000000000000 : ℝ)^29
        have hw : |(-7634741517/10000000000 : ℝ)|=(7634741517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675251611/2500000000 : ℝ)|^37 ≤ (18823704727367/100000000000000 : ℝ)^29
        have hw : |(675251611/2500000000 : ℝ)|=(675251611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4462849497/10000000000 : ℝ)*x 0 + (906907737/2500000000 : ℝ)*x 1 + (1143243983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462849497/10000000000 : ℝ)^37 ≤ (35723462727083/100000000000000 : ℝ)^29 := by
    have hnat : (4462849497 : ℕ)^37*100000000000000^29 ≤ 35723462727083^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462849497 10000000000 35723462727083 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906907737/2500000000 : ℝ)^37 ≤ (1714035578517/6250000000000 : ℝ)^29 := by
    have hnat : (906907737 : ℕ)^37*6250000000000^29 ≤ 1714035578517^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906907737 2500000000 1714035578517 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143243983/2500000000 : ℝ)^37 ≤ (1842598400483/5000000000000 : ℝ)^29 := by
    have hnat : (1143243983 : ℕ)^37*5000000000000^29 ≤ 1842598400483^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143243983 2500000000 1842598400483 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462849497/10000000000 : ℝ), (906907737/2500000000 : ℝ), (1143243983/2500000000 : ℝ)] ![(35723462727083/100000000000000 : ℝ), (1714035578517/6250000000000 : ℝ), (1842598400483/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462849497/10000000000 : ℝ)|^37 ≤ (35723462727083/100000000000000 : ℝ)^29
        have hw : |(4462849497/10000000000 : ℝ)|=(4462849497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906907737/2500000000 : ℝ)|^37 ≤ (1714035578517/6250000000000 : ℝ)^29
        have hw : |(906907737/2500000000 : ℝ)|=(906907737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1143243983/2500000000 : ℝ)|^37 ≤ (1842598400483/5000000000000 : ℝ)^29
        have hw : |(1143243983/2500000000 : ℝ)|=(1143243983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (932419961/2500000000 : ℝ)*x 0 + (-2798428061/10000000000 : ℝ)*x 1 + (-373755559/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932419961/2500000000 : ℝ)^37 ≤ (28412665738891/100000000000000 : ℝ)^29 := by
    have hnat : (932419961 : ℕ)^37*100000000000000^29 ≤ 28412665738891^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932419961 2500000000 28412665738891 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2798428061/10000000000 : ℝ)^37 ≤ (19694217925907/100000000000000 : ℝ)^29 := by
    have hnat : (2798428061 : ℕ)^37*100000000000000^29 ≤ 19694217925907^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2798428061 10000000000 19694217925907 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373755559/625000000 : ℝ)^37 ≤ (25946558158369/50000000000000 : ℝ)^29 := by
    have hnat : (373755559 : ℕ)^37*50000000000000^29 ≤ 25946558158369^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373755559 625000000 25946558158369 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(932419961/2500000000 : ℝ), (-2798428061/10000000000 : ℝ), (-373755559/625000000 : ℝ)] ![(28412665738891/100000000000000 : ℝ), (19694217925907/100000000000000 : ℝ), (25946558158369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(932419961/2500000000 : ℝ)|^37 ≤ (28412665738891/100000000000000 : ℝ)^29
        have hw : |(932419961/2500000000 : ℝ)|=(932419961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2798428061/10000000000 : ℝ)|^37 ≤ (19694217925907/100000000000000 : ℝ)^29
        have hw : |(-2798428061/10000000000 : ℝ)|=(2798428061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373755559/625000000 : ℝ)|^37 ≤ (25946558158369/50000000000000 : ℝ)^29
        have hw : |(-373755559/625000000 : ℝ)|=(373755559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3089563863/10000000000 : ℝ)*x 0 + (-6318403339/10000000000 : ℝ)*x 1 + (3050756561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3089563863/10000000000 : ℝ)^37 ≤ (22344938132437/100000000000000 : ℝ)^29 := by
    have hnat : (3089563863 : ℕ)^37*100000000000000^29 ≤ 22344938132437^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3089563863 10000000000 22344938132437 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6318403339/10000000000 : ℝ)^37 ≤ (55667597160843/100000000000000 : ℝ)^29 := by
    have hnat : (6318403339 : ℕ)^37*100000000000000^29 ≤ 55667597160843^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6318403339 10000000000 55667597160843 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3050756561/10000000000 : ℝ)^37 ≤ (21987464690331/100000000000000 : ℝ)^29 := by
    have hnat : (3050756561 : ℕ)^37*100000000000000^29 ≤ 21987464690331^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3050756561 10000000000 21987464690331 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3089563863/10000000000 : ℝ), (-6318403339/10000000000 : ℝ), (3050756561/10000000000 : ℝ)] ![(22344938132437/100000000000000 : ℝ), (55667597160843/100000000000000 : ℝ), (21987464690331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3089563863/10000000000 : ℝ)|^37 ≤ (22344938132437/100000000000000 : ℝ)^29
        have hw : |(-3089563863/10000000000 : ℝ)|=(3089563863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6318403339/10000000000 : ℝ)|^37 ≤ (55667597160843/100000000000000 : ℝ)^29
        have hw : |(-6318403339/10000000000 : ℝ)|=(6318403339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3050756561/10000000000 : ℝ)|^37 ≤ (21987464690331/100000000000000 : ℝ)^29
        have hw : |(3050756561/10000000000 : ℝ)|=(3050756561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1434446841/2500000000 : ℝ)*x 0 + (3067058737/10000000000 : ℝ)*x 1 + (3752730737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1434446841/2500000000 : ℝ)^37 ≤ (24612809981969/50000000000000 : ℝ)^29 := by
    have hnat : (1434446841 : ℕ)^37*50000000000000^29 ≤ 24612809981969^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434446841 2500000000 24612809981969 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3067058737/10000000000 : ℝ)^37 ≤ (22137480307917/100000000000000 : ℝ)^29 := by
    have hnat : (3067058737 : ℕ)^37*100000000000000^29 ≤ 22137480307917^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3067058737 10000000000 22137480307917 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3752730737/10000000000 : ℝ)^37 ≤ (5727379943597/20000000000000 : ℝ)^29 := by
    have hnat : (3752730737 : ℕ)^37*20000000000000^29 ≤ 5727379943597^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752730737 10000000000 5727379943597 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1434446841/2500000000 : ℝ), (3067058737/10000000000 : ℝ), (3752730737/10000000000 : ℝ)] ![(24612809981969/50000000000000 : ℝ), (22137480307917/100000000000000 : ℝ), (5727379943597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1434446841/2500000000 : ℝ)|^37 ≤ (24612809981969/50000000000000 : ℝ)^29
        have hw : |(1434446841/2500000000 : ℝ)|=(1434446841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3067058737/10000000000 : ℝ)|^37 ≤ (22137480307917/100000000000000 : ℝ)^29
        have hw : |(3067058737/10000000000 : ℝ)|=(3067058737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3752730737/10000000000 : ℝ)|^37 ≤ (5727379943597/20000000000000 : ℝ)^29
        have hw : |(3752730737/10000000000 : ℝ)|=(3752730737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3073080761/10000000000 : ℝ)*x 0 + (-166719459/500000000 : ℝ)*x 1 + (-47624229/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3073080761/10000000000 : ℝ)^37 ≤ (22192951799943/100000000000000 : ℝ)^29 := by
    have hnat : (3073080761 : ℕ)^37*100000000000000^29 ≤ 22192951799943^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073080761 10000000000 22192951799943 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166719459/500000000 : ℝ)^37 ≤ (24628307895019/100000000000000 : ℝ)^29 := by
    have hnat : (166719459 : ℕ)^37*100000000000000^29 ≤ 24628307895019^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166719459 500000000 24628307895019 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47624229/78125000 : ℝ)^37 ≤ (10635748057229/20000000000000 : ℝ)^29 := by
    have hnat : (47624229 : ℕ)^37*20000000000000^29 ≤ 10635748057229^29*78125000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47624229 78125000 10635748057229 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3073080761/10000000000 : ℝ), (-166719459/500000000 : ℝ), (-47624229/78125000 : ℝ)] ![(22192951799943/100000000000000 : ℝ), (24628307895019/100000000000000 : ℝ), (10635748057229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3073080761/10000000000 : ℝ)|^37 ≤ (22192951799943/100000000000000 : ℝ)^29
        have hw : |(3073080761/10000000000 : ℝ)|=(3073080761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-166719459/500000000 : ℝ)|^37 ≤ (24628307895019/100000000000000 : ℝ)^29
        have hw : |(-166719459/500000000 : ℝ)|=(166719459/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47624229/78125000 : ℝ)|^37 ≤ (10635748057229/20000000000000 : ℝ)^29
        have hw : |(-47624229/78125000 : ℝ)|=(47624229/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1592185341/10000000000 : ℝ)*x 0 + (-7514575261/10000000000 : ℝ)*x 1 + (2938377563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1592185341/10000000000 : ℝ)^37 ≤ (1198847503973/12500000000000 : ℝ)^29 := by
    have hnat : (1592185341 : ℕ)^37*12500000000000^29 ≤ 1198847503973^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592185341 10000000000 1198847503973 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7514575261/10000000000 : ℝ)^37 ≤ (4340614305443/6250000000000 : ℝ)^29 := by
    have hnat : (7514575261 : ℕ)^37*6250000000000^29 ≤ 4340614305443^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7514575261 10000000000 4340614305443 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2938377563/10000000000 : ℝ)^37 ≤ (20959391068709/100000000000000 : ℝ)^29 := by
    have hnat : (2938377563 : ℕ)^37*100000000000000^29 ≤ 20959391068709^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938377563 10000000000 20959391068709 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1592185341/10000000000 : ℝ), (-7514575261/10000000000 : ℝ), (2938377563/10000000000 : ℝ)] ![(1198847503973/12500000000000 : ℝ), (4340614305443/6250000000000 : ℝ), (20959391068709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1592185341/10000000000 : ℝ)|^37 ≤ (1198847503973/12500000000000 : ℝ)^29
        have hw : |(-1592185341/10000000000 : ℝ)|=(1592185341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7514575261/10000000000 : ℝ)|^37 ≤ (4340614305443/6250000000000 : ℝ)^29
        have hw : |(-7514575261/10000000000 : ℝ)|=(7514575261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2938377563/10000000000 : ℝ)|^37 ≤ (20959391068709/100000000000000 : ℝ)^29
        have hw : |(2938377563/10000000000 : ℝ)|=(2938377563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6880743857/10000000000 : ℝ)*x 0 + (132581391/500000000 : ℝ)*x 1 + (347786827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6880743857/10000000000 : ℝ)^37 ≤ (62064770544593/100000000000000 : ℝ)^29 := by
    have hnat : (6880743857 : ℕ)^37*100000000000000^29 ≤ 62064770544593^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6880743857 10000000000 62064770544593 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132581391/500000000 : ℝ)^37 ≤ (18385758479343/100000000000000 : ℝ)^29 := by
    have hnat : (132581391 : ℕ)^37*100000000000000^29 ≤ 18385758479343^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132581391 500000000 18385758479343 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347786827/1250000000 : ℝ)^37 ≤ (1954947096239/10000000000000 : ℝ)^29 := by
    have hnat : (347786827 : ℕ)^37*10000000000000^29 ≤ 1954947096239^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347786827 1250000000 1954947096239 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6880743857/10000000000 : ℝ), (132581391/500000000 : ℝ), (347786827/1250000000 : ℝ)] ![(62064770544593/100000000000000 : ℝ), (18385758479343/100000000000000 : ℝ), (1954947096239/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6880743857/10000000000 : ℝ)|^37 ≤ (62064770544593/100000000000000 : ℝ)^29
        have hw : |(6880743857/10000000000 : ℝ)|=(6880743857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132581391/500000000 : ℝ)|^37 ≤ (18385758479343/100000000000000 : ℝ)^29
        have hw : |(132581391/500000000 : ℝ)|=(132581391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(347786827/1250000000 : ℝ)|^37 ≤ (1954947096239/10000000000000 : ℝ)^29
        have hw : |(347786827/1250000000 : ℝ)|=(347786827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s0_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2816388297/10000000000 : ℝ)*x 0 + (-4563299877/10000000000 : ℝ)*x 1 + (-2598821873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2816388297/10000000000 : ℝ)^37 ≤ (19855625551143/100000000000000 : ℝ)^29 := by
    have hnat : (2816388297 : ℕ)^37*100000000000000^29 ≤ 19855625551143^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816388297 10000000000 19855625551143 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4563299877/10000000000 : ℝ)^37 ≤ (18376255317443/50000000000000 : ℝ)^29 := by
    have hnat : (4563299877 : ℕ)^37*50000000000000^29 ≤ 18376255317443^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563299877 10000000000 18376255317443 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598821873/5000000000 : ℝ)^37 ≤ (43391863793181/100000000000000 : ℝ)^29 := by
    have hnat : (2598821873 : ℕ)^37*100000000000000^29 ≤ 43391863793181^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598821873 5000000000 43391863793181 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2816388297/10000000000 : ℝ), (-4563299877/10000000000 : ℝ), (-2598821873/5000000000 : ℝ)] ![(19855625551143/100000000000000 : ℝ), (18376255317443/50000000000000 : ℝ), (43391863793181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2816388297/10000000000 : ℝ)|^37 ≤ (19855625551143/100000000000000 : ℝ)^29
        have hw : |(2816388297/10000000000 : ℝ)|=(2816388297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4563299877/10000000000 : ℝ)|^37 ≤ (18376255317443/50000000000000 : ℝ)^29
        have hw : |(-4563299877/10000000000 : ℝ)|=(4563299877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2598821873/5000000000 : ℝ)|^37 ≤ (43391863793181/100000000000000 : ℝ)^29
        have hw : |(-2598821873/5000000000 : ℝ)|=(2598821873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3395865907/10000000000 : ℝ)*x 0 + (-462575049/1000000000 : ℝ)*x 1 + (4625750671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3395865907/10000000000 : ℝ)^37 ≤ (2520911366303/10000000000000 : ℝ)^29 := by
    have hnat : (3395865907 : ℕ)^37*10000000000000^29 ≤ 2520911366303^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3395865907 10000000000 2520911366303 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462575049/1000000000 : ℝ)^37 ≤ (37395442227919/100000000000000 : ℝ)^29 := by
    have hnat : (462575049 : ℕ)^37*100000000000000^29 ≤ 37395442227919^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462575049 1000000000 37395442227919 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4625750671/10000000000 : ℝ)^37 ≤ (3739544409481/10000000000000 : ℝ)^29 := by
    have hnat : (4625750671 : ℕ)^37*10000000000000^29 ≤ 3739544409481^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4625750671 10000000000 3739544409481 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3395865907/10000000000 : ℝ), (-462575049/1000000000 : ℝ), (4625750671/10000000000 : ℝ)] ![(2520911366303/10000000000000 : ℝ), (37395442227919/100000000000000 : ℝ), (3739544409481/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3395865907/10000000000 : ℝ)|^37 ≤ (2520911366303/10000000000000 : ℝ)^29
        have hw : |(-3395865907/10000000000 : ℝ)|=(3395865907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-462575049/1000000000 : ℝ)|^37 ≤ (37395442227919/100000000000000 : ℝ)^29
        have hw : |(-462575049/1000000000 : ℝ)|=(462575049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4625750671/10000000000 : ℝ)|^37 ≤ (3739544409481/10000000000000 : ℝ)^29
        have hw : |(4625750671/10000000000 : ℝ)|=(4625750671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5350441569/10000000000 : ℝ)*x 0 + (7097863/19531250 : ℝ)*x 1 + (3634105999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350441569/10000000000 : ℝ)^37 ≤ (45025923148239/100000000000000 : ℝ)^29 := by
    have hnat : (5350441569 : ℕ)^37*100000000000000^29 ≤ 45025923148239^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350441569 10000000000 45025923148239 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7097863/19531250 : ℝ)^37 ≤ (27487037731463/100000000000000 : ℝ)^29 := by
    have hnat : (7097863 : ℕ)^37*100000000000000^29 ≤ 27487037731463^29*19531250^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7097863 19531250 27487037731463 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3634105999/10000000000 : ℝ)^37 ≤ (13743519555717/50000000000000 : ℝ)^29 := by
    have hnat : (3634105999 : ℕ)^37*50000000000000^29 ≤ 13743519555717^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3634105999 10000000000 13743519555717 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350441569/10000000000 : ℝ), (7097863/19531250 : ℝ), (3634105999/10000000000 : ℝ)] ![(45025923148239/100000000000000 : ℝ), (27487037731463/100000000000000 : ℝ), (13743519555717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350441569/10000000000 : ℝ)|^37 ≤ (45025923148239/100000000000000 : ℝ)^29
        have hw : |(5350441569/10000000000 : ℝ)|=(5350441569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7097863/19531250 : ℝ)|^37 ≤ (27487037731463/100000000000000 : ℝ)^29
        have hw : |(7097863/19531250 : ℝ)|=(7097863/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3634105999/10000000000 : ℝ)|^37 ≤ (13743519555717/50000000000000 : ℝ)^29
        have hw : |(3634105999/10000000000 : ℝ)|=(3634105999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3395865907/10000000000 : ℝ)*x 0 + (-462575049/1000000000 : ℝ)*x 1 + (-4625750671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3395865907/10000000000 : ℝ)^37 ≤ (2520911366303/10000000000000 : ℝ)^29 := by
    have hnat : (3395865907 : ℕ)^37*10000000000000^29 ≤ 2520911366303^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3395865907 10000000000 2520911366303 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462575049/1000000000 : ℝ)^37 ≤ (37395442227919/100000000000000 : ℝ)^29 := by
    have hnat : (462575049 : ℕ)^37*100000000000000^29 ≤ 37395442227919^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462575049 1000000000 37395442227919 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4625750671/10000000000 : ℝ)^37 ≤ (3739544409481/10000000000000 : ℝ)^29 := by
    have hnat : (4625750671 : ℕ)^37*10000000000000^29 ≤ 3739544409481^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4625750671 10000000000 3739544409481 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3395865907/10000000000 : ℝ), (-462575049/1000000000 : ℝ), (-4625750671/10000000000 : ℝ)] ![(2520911366303/10000000000000 : ℝ), (37395442227919/100000000000000 : ℝ), (3739544409481/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3395865907/10000000000 : ℝ)|^37 ≤ (2520911366303/10000000000000 : ℝ)^29
        have hw : |(3395865907/10000000000 : ℝ)|=(3395865907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-462575049/1000000000 : ℝ)|^37 ≤ (37395442227919/100000000000000 : ℝ)^29
        have hw : |(-462575049/1000000000 : ℝ)|=(462575049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4625750671/10000000000 : ℝ)|^37 ≤ (3739544409481/10000000000000 : ℝ)^29
        have hw : |(-4625750671/10000000000 : ℝ)|=(4625750671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312007_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5350441569/10000000000 : ℝ)*x 0 + (-7097863/19531250 : ℝ)*x 1 + (3634105999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350441569/10000000000 : ℝ)^37 ≤ (45025923148239/100000000000000 : ℝ)^29 := by
    have hnat : (5350441569 : ℕ)^37*100000000000000^29 ≤ 45025923148239^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350441569 10000000000 45025923148239 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7097863/19531250 : ℝ)^37 ≤ (27487037731463/100000000000000 : ℝ)^29 := by
    have hnat : (7097863 : ℕ)^37*100000000000000^29 ≤ 27487037731463^29*19531250^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7097863 19531250 27487037731463 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3634105999/10000000000 : ℝ)^37 ≤ (13743519555717/50000000000000 : ℝ)^29 := by
    have hnat : (3634105999 : ℕ)^37*50000000000000^29 ≤ 13743519555717^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3634105999 10000000000 13743519555717 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350441569/10000000000 : ℝ), (-7097863/19531250 : ℝ), (3634105999/10000000000 : ℝ)] ![(45025923148239/100000000000000 : ℝ), (27487037731463/100000000000000 : ℝ), (13743519555717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350441569/10000000000 : ℝ)|^37 ≤ (45025923148239/100000000000000 : ℝ)^29
        have hw : |(5350441569/10000000000 : ℝ)|=(5350441569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7097863/19531250 : ℝ)|^37 ≤ (27487037731463/100000000000000 : ℝ)^29
        have hw : |(-7097863/19531250 : ℝ)|=(7097863/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3634105999/10000000000 : ℝ)|^37 ≤ (13743519555717/50000000000000 : ℝ)^29
        have hw : |(3634105999/10000000000 : ℝ)|=(3634105999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312007 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (178281/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-594044873/2500000000 : ℝ)*X 0 0+(-6453526477/10000000000 : ℝ)*X 0 1+(3565240147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1147841809/2000000000 : ℝ)*X 1 0+(195890199/625000000 : ℝ)*X 1 1+(737447167/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-210571477/1250000000 : ℝ)*X 0 0+(-7634741517/10000000000 : ℝ)*X 0 1+(675251611/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4462849497/10000000000 : ℝ)*X 1 0+(906907737/2500000000 : ℝ)*X 1 1+(1143243983/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((932419961/2500000000 : ℝ)*X 2 0+(-2798428061/10000000000 : ℝ)*X 2 1+(-373755559/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-3089563863/10000000000 : ℝ)*X 0 0+(-6318403339/10000000000 : ℝ)*X 0 1+(3050756561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1434446841/2500000000 : ℝ)*X 1 0+(3067058737/10000000000 : ℝ)*X 1 1+(3752730737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3073080761/10000000000 : ℝ)*X 2 0+(-166719459/500000000 : ℝ)*X 2 1+(-47624229/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1592185341/10000000000 : ℝ)*X 0 0+(-7514575261/10000000000 : ℝ)*X 0 1+(2938377563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((6880743857/10000000000 : ℝ)*X 1 0+(132581391/500000000 : ℝ)*X 1 1+(347786827/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2816388297/10000000000 : ℝ)*X 2 0+(-4563299877/10000000000 : ℝ)*X 2 1+(-2598821873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1641/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1641/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9561667441316205285639/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2582105998009/1000000000000 : ℝ)*(base3) + (205409311051/200000000000 : ℝ)*(base7) + (316607438963/1000000000000 : ℝ)*(base40) + (1001277761421/500000000000 : ℝ)*(base49) + (101942980739/200000000000 : ℝ)*(base50) + (519119273537/200000000000 : ℝ)*(major_s0_0) + (519119273537/200000000000 : ℝ)*(major_s0_1) + (519119273537/200000000000 : ℝ)*(major_s0_2) + (3025714460183/1000000000000 : ℝ)*(sp_s0_7) + (28039456837/5000000000 : ℝ)*(sp_s0_8) + (1512874990613/500000000000 : ℝ)*(sp_s0_9) + (355921/200000000000 : ℝ)*(sp_s0_14) + (37167769/1000000000000 : ℝ)*(sp_s0_15) + (72688813/1000000000000 : ℝ)*(sp_s0_20) + (311011888551/200000000000 : ℝ)*(f.failure) + (756446787249/250000000000 : ℝ)*(f.sum) + (449292561/10000000000000000000000 : ℝ)*base63 + (149489977204787/2000000000000000000000000000 : ℝ)*base65 + (779479810604787/2000000000000000000000000000 : ℝ)*base66 + (158448136032071/1000000000000000000000000000 : ℝ)*base69 + (297862675468929/2000000000000000000000000000 : ℝ)*base71 + (143991720595213/2000000000000000000000000000 : ℝ)*base72 + (376760866667929/1000000000000000000000000000 : ℝ)*base75 + (174148741367929/1000000000000000000000000000 : ℝ)*base76 + (324331929/312500000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (13063/20000000000000000 : ℝ)*base87 + (13063/20000000000000000 : ℝ)*base89 + (13063/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-849/10000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-849/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8834829537625137/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (1628835748019/1000000000000 : ℝ)*(base3) + (97515687059/500000000000 : ℝ)*(base7) + (36539/15625000000 : ℝ)*(base13) + (830525547989/1000000000000 : ℝ)*(base40) + (9140302981/8000000000 : ℝ)*(base49) + (2393205894609/1000000000000 : ℝ)*(major_s0_0) + (2393205894609/1000000000000 : ℝ)*(major_s0_1) + (2393205894609/1000000000000 : ℝ)*(major_s0_2) + (1711221/1000000000000 : ℝ)*(sp_s0_0) + (3551721/125000000000 : ℝ)*(sp_s0_9) + (3236701481911/1000000000000 : ℝ)*(sp_s0_13) + (1216385218401/250000000000 : ℝ)*(sp_s0_14) + (161833855893/50000000000 : ℝ)*(sp_s0_15) + (406043/1000000000000 : ℝ)*(sp_s0_21) + (1433804373901/1000000000000 : ℝ)*(f.failure) + (809176382907/250000000000 : ℝ)*(f.sum) + (39189523/400000000000000000000 : ℝ)*base62 + (1865212507125859/10000000000000000000000000000 : ℝ)*base65 + (1338870819125859/10000000000000000000000000000 : ℝ)*base66 + (3526664588022953/5000000000000000000000000000 : ℝ)*base68 + (2175642615920047/10000000000000000000000000000 : ℝ)*base70 + (5692317374874141/10000000000000000000000000000 : ℝ)*base72 + (1837061091477047/5000000000000000000000000000 : ℝ)*base74 + (1517818589477047/5000000000000000000000000000 : ℝ)*base77 + (23646979/78125000000000000000 : ℝ)*base79 + (37613/100000000000000000 : ℝ)*base87 + (37613/100000000000000000 : ℝ)*base89 + (37613/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70473/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(70473/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12423411663059913906531/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3094614915153/1000000000000 : ℝ)*(base3) + (1170217322637/1000000000000 : ℝ)*(base7) + (470572441689/500000000000 : ℝ)*(base40) + (33024075247/12500000000 : ℝ)*(base49) + (802862339369/500000000000 : ℝ)*(base50) + (642413950719/200000000000 : ℝ)*(major_s0_0) + (642413950719/200000000000 : ℝ)*(major_s0_1) + (642413950719/200000000000 : ℝ)*(major_s0_2) + (28293543/500000000000 : ℝ)*(sp_s0_0) + (6030073/250000000000 : ℝ)*(sp_s0_1) + (85157981/250000000000 : ℝ)*(sp_s0_7) + (950978876549/250000000000 : ℝ)*(sp_s0_20) + (6898903520067/1000000000000 : ℝ)*(sp_s0_21) + (1902156362603/500000000000 : ℝ)*(sp_s0_22) + (384879518503/200000000000 : ℝ)*(f.failure) + (1902156362603/500000000000 : ℝ)*(f.sum) + (17158217/2500000000000000000000 : ℝ)*base62 + (1111135572819469/2000000000000000000000000000 : ℝ)*base65 + (1509027244819469/2000000000000000000000000000 : ℝ)*base66 + (801241346910823/1000000000000000000000000000 : ℝ)*base68 + (234429679997823/2000000000000000000000000000 : ℝ)*base71 + (2001785422780531/2000000000000000000000000000 : ℝ)*base72 + (504382027189177/1000000000000000000000000000 : ℝ)*base74 + (876310575189177/1000000000000000000000000000 : ℝ)*base77 + (1204384581/2500000000000000000000 : ℝ)*base78 + (8761/20000000000000000 : ℝ)*base86 + (8761/20000000000000000 : ℝ)*base88 + (8761/20000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (1641/3125 : ℝ) ^ (9/2 : ℝ) ≤ (220406048511690873/4000000000000000000 : ℝ) := by
    have hpowers : (1641/3125 : ℝ)^9 ≤ (220406048511690873/4000000000000000000 : ℝ)^2 := by
      have hnat : (1641 : ℕ)^9*4000000000000000000^2 ≤ 220406048511690873^2*3125^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1641 3125 220406048511690873 4000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1641/3125 : ℝ)) (X := (220406048511690873/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (4220406048511690873/4000000000000000000 : ℝ) ≤ (10119906476861253/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (4220406048511690873/4000000000000000000 : ℝ)^2 ≤ (10119906476861253/10000000000000000 : ℝ)^9 := by
      have hnat : (4220406048511690873 : ℕ)^2*10000000000000000^9 ≤ 10119906476861253^9*4000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4220406048511690873 4000000000000000000 10119906476861253 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10119906476861253/10000000000000000 : ℝ)) (X := (4220406048511690873/4000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2220406048511690873/2000000000000000000 : ℝ) ≤ (5117518577465967/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2220406048511690873/2000000000000000000 : ℝ)^2 ≤ (5117518577465967/5000000000000000 : ℝ)^9 := by
      have hnat : (2220406048511690873 : ℕ)^2*5000000000000000^9 ≤ 5117518577465967^9*2000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2220406048511690873 2000000000000000000 5117518577465967 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5117518577465967/5000000000000000 : ℝ)) (X := (2220406048511690873/2000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(119906476861253/5251200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(38376892690227/1750400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1641/3125 : ℝ)) (alpha := (119906476861253/5251200000000000 : ℝ)) (beta := (38376892690227/1750400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1641/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(119906476861253/5251200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(38376892690227/1750400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (849/10000 : ℝ) ^ (9/2 : ℝ) ≤ (302771227634537/20000000000000000000 : ℝ) := by
    have hpowers : (849/10000 : ℝ)^9 ≤ (302771227634537/20000000000000000000 : ℝ)^2 := by
      have hnat : (849 : ℕ)^9*20000000000000000000^2 ≤ 302771227634537^2*10000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        849 10000 302771227634537 20000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (849/10000 : ℝ)) (X := (302771227634537/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20000302771227634537/20000000000000000000 : ℝ) ≤ (1250004205131183/1250000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (20000302771227634537/20000000000000000000 : ℝ)^2 ≤ (1250004205131183/1250000000000000 : ℝ)^9 := by
      have hnat : (20000302771227634537 : ℕ)^2*1250000000000000^9 ≤ 1250004205131183^9*20000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000302771227634537 20000000000000000000 1250004205131183 1250000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250004205131183/1250000000000000 : ℝ)) (X := (20000302771227634537/20000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10000302771227634537/10000000000000000000 : ℝ) ≤ (10000067281702831/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (10000302771227634537/10000000000000000000 : ℝ)^2 ≤ (10000067281702831/10000000000000000 : ℝ)^9 := by
      have hnat : (10000302771227634537 : ℕ)^2*10000000000000000^9 ≤ 10000067281702831^9*10000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000302771227634537 10000000000000000000 10000067281702831 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000067281702831/10000000000000000 : ℝ)) (X := (10000302771227634537/10000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(4205131183/106125000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(33640653367/849000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (849/10000 : ℝ)) (alpha := (4205131183/106125000000000 : ℝ)) (beta := (33640653367/849000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (849/10000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(4205131183/106125000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(33640653367/849000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (70473/100000 : ℝ) ^ (9/2 : ℝ) ≤ (4141259201057824169/20000000000000000000 : ℝ) := by
    have hpowers : (70473/100000 : ℝ)^9 ≤ (4141259201057824169/20000000000000000000 : ℝ)^2 := by
      have hnat : (70473 : ℕ)^9*20000000000000000000^2 ≤ 4141259201057824169^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70473 100000 4141259201057824169 20000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70473/100000 : ℝ)) (X := (4141259201057824169/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (24141259201057824169/20000000000000000000 : ℝ) ≤ (10427067985477047/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (24141259201057824169/20000000000000000000 : ℝ)^2 ≤ (10427067985477047/10000000000000000 : ℝ)^9 := by
      have hnat : (24141259201057824169 : ℕ)^2*10000000000000000^9 ≤ 10427067985477047^9*20000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24141259201057824169 20000000000000000000 10427067985477047 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10427067985477047/10000000000000000 : ℝ)) (X := (24141259201057824169/20000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (14141259201057824169/10000000000000000000 : ℝ) ≤ (1080044864325147/1000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (14141259201057824169/10000000000000000000 : ℝ)^2 ≤ (1080044864325147/1000000000000000 : ℝ)^9 := by
      have hnat : (14141259201057824169 : ℕ)^2*1000000000000000^9 ≤ 1080044864325147^9*10000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14141259201057824169 10000000000000000000 1080044864325147 1000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1080044864325147/1000000000000000 : ℝ)) (X := (14141259201057824169/10000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(427067985477047/7047300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(9573863019857/180700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (70473/100000 : ℝ)) (alpha := (427067985477047/7047300000000000 : ℝ)) (beta := (9573863019857/180700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (70473/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(427067985477047/7047300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(9573863019857/180700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3395865907/10000000000 : ℝ)*X 0 0+(-462575049/1000000000 : ℝ)*X 0 1+(4625750671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5350441569/10000000000 : ℝ)*X 1 0+(7097863/19531250 : ℝ)*X 1 1+(3634105999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3395865907/10000000000 : ℝ)*X 2 0+(-462575049/1000000000 : ℝ)*X 2 1+(-4625750671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5350441569/10000000000 : ℝ)*X 0 0+(-7097863/19531250 : ℝ)*X 0 1+(3634105999/10000000000 : ℝ)*X 0 2+(5350441569/10000000000 : ℝ)*X 1 0+(-7097863/19531250 : ℝ)*X 1 1+(3634105999/10000000000 : ℝ)*X 1 2+(5350441569/10000000000 : ℝ)*X 2 0+(-7097863/19531250 : ℝ)*X 2 1+(3634105999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312007_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-125929255347974978165975848316839/18182151455000000000000000000000 : ℝ) := by norm_num
    linear_combination (835543152813/1000000000000 : ℝ)*(base3) + (195807/1000000000000 : ℝ)*(base10) + (1623/25000000000 : ℝ)*(base13) + (91633/500000000000 : ℝ)*(base27) + (25166138747/50000000000 : ℝ)*(base40) + (669225816499/500000000000 : ℝ)*(base49) + (49817617897/62500000000 : ℝ)*(base50) + (453001807323/1000000000000 : ℝ)*(base59) + (166913/100000 : ℝ)*(major_s1_0) + (166913/100000 : ℝ)*(major_s1_1) + (166913/100000 : ℝ)*(major_s1_2) + (1154330218087/500000000000 : ℝ)*(sp_s1_0) + (1572101924857/500000000000 : ℝ)*(sp_s1_1) + (2308660696901/1000000000000 : ℝ)*(sp_s1_2) + (164456663921/1000000000000 : ℝ)*(sp_s1_6) + (2308660696901/1000000000000 : ℝ)*(f.sum) + (42926310044913143/66479530000000000000000000000 : ℝ)*base62 + (560436332187/4517500000000000000000000 : ℝ)*base64 + (5003044426783/8490000000000000000000000 : ℝ)*base67 + (22807838957599/140946000000000000000000000 : ℝ)*base68 + (217351756215427/14826435000000000000000000000 : ℝ)*base71 + (326117596419/1094000000000000000000000 : ℝ)*base73 + (341549633209/530625000000000000000000 : ℝ)*base74 + (1089217722661/4102500000000000000000000 : ℝ)*base76 + (1952854629652013/2322015000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c312008_s0_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4226880459/10000000000 : ℝ)*x 0 + (-2146190987/5000000000 : ℝ)*x 1 + (-4161688087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4226880459/10000000000 : ℝ)^37 ≤ (2083210121591/6250000000000 : ℝ)^29 := by
    have hnat : (4226880459 : ℕ)^37*6250000000000^29 ≤ 2083210121591^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226880459 10000000000 2083210121591 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146190987/5000000000 : ℝ)^37 ≤ (16995884732661/50000000000000 : ℝ)^29 := by
    have hnat : (2146190987 : ℕ)^37*50000000000000^29 ≤ 16995884732661^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146190987 5000000000 16995884732661 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4161688087/10000000000 : ℝ)^37 ≤ (4084608571667/12500000000000 : ℝ)^29 := by
    have hnat : (4161688087 : ℕ)^37*12500000000000^29 ≤ 4084608571667^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161688087 10000000000 4084608571667 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4226880459/10000000000 : ℝ), (-2146190987/5000000000 : ℝ), (-4161688087/10000000000 : ℝ)] ![(2083210121591/6250000000000 : ℝ), (16995884732661/50000000000000 : ℝ), (4084608571667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4226880459/10000000000 : ℝ)|^37 ≤ (2083210121591/6250000000000 : ℝ)^29
        have hw : |(-4226880459/10000000000 : ℝ)|=(4226880459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146190987/5000000000 : ℝ)|^37 ≤ (16995884732661/50000000000000 : ℝ)^29
        have hw : |(-2146190987/5000000000 : ℝ)|=(2146190987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4161688087/10000000000 : ℝ)|^37 ≤ (4084608571667/12500000000000 : ℝ)^29
        have hw : |(-4161688087/10000000000 : ℝ)|=(4161688087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312008_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1037967453/2500000000 : ℝ)*x 0 + (4217167917/10000000000 : ℝ)*x 1 + (-4311769981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037967453/2500000000 : ℝ)^37 ≤ (32578542567891/100000000000000 : ℝ)^29 := by
    have hnat : (1037967453 : ℕ)^37*100000000000000^29 ≤ 32578542567891^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037967453 2500000000 32578542567891 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4217167917/10000000000 : ℝ)^37 ≤ (33233676021839/100000000000000 : ℝ)^29 := by
    have hnat : (4217167917 : ℕ)^37*100000000000000^29 ≤ 33233676021839^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217167917 10000000000 33233676021839 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4311769981/10000000000 : ℝ)^37 ≤ (34187781391643/100000000000000 : ℝ)^29 := by
    have hnat : (4311769981 : ℕ)^37*100000000000000^29 ≤ 34187781391643^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311769981 10000000000 34187781391643 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037967453/2500000000 : ℝ), (4217167917/10000000000 : ℝ), (-4311769981/10000000000 : ℝ)] ![(32578542567891/100000000000000 : ℝ), (33233676021839/100000000000000 : ℝ), (34187781391643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037967453/2500000000 : ℝ)|^37 ≤ (32578542567891/100000000000000 : ℝ)^29
        have hw : |(1037967453/2500000000 : ℝ)|=(1037967453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4217167917/10000000000 : ℝ)|^37 ≤ (33233676021839/100000000000000 : ℝ)^29
        have hw : |(4217167917/10000000000 : ℝ)|=(4217167917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4311769981/10000000000 : ℝ)|^37 ≤ (34187781391643/100000000000000 : ℝ)^29
        have hw : |(-4311769981/10000000000 : ℝ)|=(4311769981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312008_s0_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1075537737/2500000000 : ℝ)*x 0 + (-2071431229/5000000000 : ℝ)*x 1 + (4235797657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075537737/2500000000 : ℝ)^37 ≤ (34090502918299/100000000000000 : ℝ)^29 := by
    have hnat : (1075537737 : ℕ)^37*100000000000000^29 ≤ 34090502918299^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075537737 2500000000 34090502918299 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071431229/5000000000 : ℝ)^37 ≤ (32488393998801/100000000000000 : ℝ)^29 := by
    have hnat : (2071431229 : ℕ)^37*100000000000000^29 ≤ 32488393998801^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071431229 5000000000 32488393998801 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235797657/10000000000 : ℝ)^37 ≤ (33421103072727/100000000000000 : ℝ)^29 := by
    have hnat : (4235797657 : ℕ)^37*100000000000000^29 ≤ 33421103072727^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235797657 10000000000 33421103072727 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075537737/2500000000 : ℝ), (-2071431229/5000000000 : ℝ), (4235797657/10000000000 : ℝ)] ![(34090502918299/100000000000000 : ℝ), (32488393998801/100000000000000 : ℝ), (33421103072727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075537737/2500000000 : ℝ)|^37 ≤ (34090502918299/100000000000000 : ℝ)^29
        have hw : |(1075537737/2500000000 : ℝ)|=(1075537737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071431229/5000000000 : ℝ)|^37 ≤ (32488393998801/100000000000000 : ℝ)^29
        have hw : |(-2071431229/5000000000 : ℝ)|=(2071431229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235797657/10000000000 : ℝ)|^37 ≤ (33421103072727/100000000000000 : ℝ)^29
        have hw : |(4235797657/10000000000 : ℝ)|=(4235797657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312008 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-4226880459/10000000000 : ℝ)*X 0 0+(-2146190987/5000000000 : ℝ)*X 0 1+(-4161688087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312008_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1037967453/2500000000 : ℝ)*X 1 0+(4217167917/10000000000 : ℝ)*X 1 1+(-4311769981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312008_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1075537737/2500000000 : ℝ)*X 2 0+(-2071431229/5000000000 : ℝ)*X 2 1+(4235797657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312008_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-68975506654049662850193/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (499999949841/500000000000 : ℝ)*(base1) + (50159/500000000000 : ℝ)*(base5) + (51743/1000000000000 : ℝ)*(base18) + (35329/1000000000000 : ℝ)*(base21) + (932840255761/1000000000000 : ℝ)*(base39) + (109662808447/250000000000 : ℝ)*(base40) + (257277358233/500000000000 : ℝ)*(base49) + (1608111399/4000000000 : ℝ)*(base50) + (17463213047/40000000000 : ℝ)*(base60) + (166913/100000 : ℝ)*(major_s0_0) + (166913/100000 : ℝ)*(major_s0_1) + (166913/100000 : ℝ)*(major_s0_2) + (1649591727407/500000000000 : ℝ)*(sp_s0_0) + (2299183503389/1000000000000 : ℝ)*(sp_s0_1) + (2299183620121/1000000000000 : ℝ)*(sp_s0_2) + (574795888783/250000000000 : ℝ)*(f.sum) + (2868034233/5000000000000000000000 : ℝ)*base63 + (1931929397/5000000000000000000000 : ℝ)*base64 + (215473903/625000000000000000000 : ℝ)*base67 + (248512597/625000000000000000000 : ℝ)*base69 + (2562453237/10000000000000000000000 : ℝ)*base71 + (377052761/10000000000000000000000 : ℝ)*base72 + (220810607/625000000000000000000 : ℝ)*base75 + (2329661499/5000000000000000000000 : ℝ)*base77 + (1732106763/10000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p012_b003 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 7 ≤ c.val) (hhi : c.val < 9)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=7 ∨ c=8 := by omega
  rcases hc with rfl|rfl
  · exact collision_c312007 p hpa (by linarith only [hpb]) X hX
  · exact collision_c312008 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 7 ≤ c.val) (hhi : c.val < 9)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b003 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b018
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:38.718086+00:00
-- url     : https://prove2.me/submissions/37c9c94a-ff68-4ca6-a92d-ae6ec1e6fcd5

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310031_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310031_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310031_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310031_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310031 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c310031_s0 p hpa hpb X hX
  have h1 := collision_c310031_s1 p hpa hpb X hX h0
  have h2 := collision_c310031_s2 p hpa hpb X hX h1
  exact collision_c310031_s3 p hpa hpb X hX h2

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
theorem collision_support_c310030_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1747288599/2500000000 : ℝ)*x 0 + (-221110913/2000000000 : ℝ)*x 1 + (-2011538189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1747288599/2500000000 : ℝ)^9 ≤ (63092034199743/100000000000000 : ℝ)^7 := by
    have hnat : (1747288599 : ℕ)^9*100000000000000^7 ≤ 63092034199743^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747288599 2500000000 63092034199743 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221110913/2000000000 : ℝ)^9 ≤ (5892741323743/100000000000000 : ℝ)^7 := by
    have hnat : (221110913 : ℕ)^9*100000000000000^7 ≤ 5892741323743^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221110913 2000000000 5892741323743 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011538189/5000000000 : ℝ)^9 ≤ (31015224456769/100000000000000 : ℝ)^7 := by
    have hnat : (2011538189 : ℕ)^9*100000000000000^7 ≤ 31015224456769^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011538189 5000000000 31015224456769 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1747288599/2500000000 : ℝ), (-221110913/2000000000 : ℝ), (-2011538189/5000000000 : ℝ)] ![(63092034199743/100000000000000 : ℝ), (5892741323743/100000000000000 : ℝ), (31015224456769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1747288599/2500000000 : ℝ)|^9 ≤ (63092034199743/100000000000000 : ℝ)^7
        have hw : |(1747288599/2500000000 : ℝ)|=(1747288599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221110913/2000000000 : ℝ)|^9 ≤ (5892741323743/100000000000000 : ℝ)^7
        have hw : |(-221110913/2000000000 : ℝ)|=(221110913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011538189/5000000000 : ℝ)|^9 ≤ (31015224456769/100000000000000 : ℝ)^7
        have hw : |(-2011538189/5000000000 : ℝ)|=(2011538189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (671338931/2500000000 : ℝ)*x 0 + (1101500841/2000000000 : ℝ)*x 1 + (1107620513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671338931/2500000000 : ℝ)^9 ≤ (1844418577991/10000000000000 : ℝ)^7 := by
    have hnat : (671338931 : ℕ)^9*10000000000000^7 ≤ 1844418577991^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671338931 2500000000 1844418577991 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101500841/2000000000 : ℝ)^9 ≤ (46445317259443/100000000000000 : ℝ)^7 := by
    have hnat : (1101500841 : ℕ)^9*100000000000000^7 ≤ 46445317259443^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101500841 2000000000 46445317259443 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107620513/2500000000 : ℝ)^9 ≤ (4388812116983/12500000000000 : ℝ)^7 := by
    have hnat : (1107620513 : ℕ)^9*12500000000000^7 ≤ 4388812116983^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107620513 2500000000 4388812116983 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671338931/2500000000 : ℝ), (1101500841/2000000000 : ℝ), (1107620513/2500000000 : ℝ)] ![(1844418577991/10000000000000 : ℝ), (46445317259443/100000000000000 : ℝ), (4388812116983/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671338931/2500000000 : ℝ)|^9 ≤ (1844418577991/10000000000000 : ℝ)^7
        have hw : |(671338931/2500000000 : ℝ)|=(671338931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101500841/2000000000 : ℝ)|^9 ≤ (46445317259443/100000000000000 : ℝ)^7
        have hw : |(1101500841/2000000000 : ℝ)|=(1101500841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1107620513/2500000000 : ℝ)|^9 ≤ (4388812116983/12500000000000 : ℝ)^7
        have hw : |(1107620513/2500000000 : ℝ)|=(1107620513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2720400381/10000000000 : ℝ)*x 0 + (1828153037/5000000000 : ℝ)*x 1 + (-3088080463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2720400381/10000000000 : ℝ)^9 ≤ (9377117399889/50000000000000 : ℝ)^7 := by
    have hnat : (2720400381 : ℕ)^9*50000000000000^7 ≤ 9377117399889^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720400381 10000000000 9377117399889 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1828153037/5000000000 : ℝ)^9 ≤ (13714107859559/50000000000000 : ℝ)^7 := by
    have hnat : (1828153037 : ℕ)^9*50000000000000^7 ≤ 13714107859559^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828153037 5000000000 13714107859559 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3088080463/5000000000 : ℝ)^9 ≤ (6727193684067/12500000000000 : ℝ)^7 := by
    have hnat : (3088080463 : ℕ)^9*12500000000000^7 ≤ 6727193684067^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088080463 5000000000 6727193684067 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2720400381/10000000000 : ℝ), (1828153037/5000000000 : ℝ), (-3088080463/5000000000 : ℝ)] ![(9377117399889/50000000000000 : ℝ), (13714107859559/50000000000000 : ℝ), (6727193684067/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2720400381/10000000000 : ℝ)|^9 ≤ (9377117399889/50000000000000 : ℝ)^7
        have hw : |(-2720400381/10000000000 : ℝ)|=(2720400381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1828153037/5000000000 : ℝ)|^9 ≤ (13714107859559/50000000000000 : ℝ)^7
        have hw : |(1828153037/5000000000 : ℝ)|=(1828153037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3088080463/5000000000 : ℝ)|^9 ≤ (6727193684067/12500000000000 : ℝ)^7
        have hw : |(-3088080463/5000000000 : ℝ)|=(3088080463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1849096113/2500000000 : ℝ)*x 0 + (-273320549/10000000000 : ℝ)*x 1 + (-4038225471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849096113/2500000000 : ℝ)^9 ≤ (33928641802889/50000000000000 : ℝ)^7 := by
    have hnat : (1849096113 : ℕ)^9*50000000000000^7 ≤ 33928641802889^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849096113 2500000000 33928641802889 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273320549/10000000000 : ℝ)^9 ≤ (610783421/62500000000 : ℝ)^7 := by
    have hnat : (273320549 : ℕ)^9*62500000000^7 ≤ 610783421^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273320549 10000000000 610783421 62500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038225471/10000000000 : ℝ)^9 ≤ (15582731454807/50000000000000 : ℝ)^7 := by
    have hnat : (4038225471 : ℕ)^9*50000000000000^7 ≤ 15582731454807^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038225471 10000000000 15582731454807 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1849096113/2500000000 : ℝ), (-273320549/10000000000 : ℝ), (-4038225471/10000000000 : ℝ)] ![(33928641802889/50000000000000 : ℝ), (610783421/62500000000 : ℝ), (15582731454807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1849096113/2500000000 : ℝ)|^9 ≤ (33928641802889/50000000000000 : ℝ)^7
        have hw : |(1849096113/2500000000 : ℝ)|=(1849096113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273320549/10000000000 : ℝ)|^9 ≤ (610783421/62500000000 : ℝ)^7
        have hw : |(-273320549/10000000000 : ℝ)|=(273320549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4038225471/10000000000 : ℝ)|^9 ≤ (15582731454807/50000000000000 : ℝ)^7
        have hw : |(-4038225471/10000000000 : ℝ)|=(4038225471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (99034367/625000000 : ℝ)*x 0 + (7048160107/10000000000 : ℝ)*x 1 + (3597424511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99034367/625000000 : ℝ)^9 ≤ (9360684378269/100000000000000 : ℝ)^7 := by
    have hnat : (99034367 : ℕ)^9*100000000000000^7 ≤ 9360684378269^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99034367 625000000 9360684378269 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7048160107/10000000000 : ℝ)^9 ≤ (31888848696999/50000000000000 : ℝ)^7 := by
    have hnat : (7048160107 : ℕ)^9*50000000000000^7 ≤ 31888848696999^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7048160107 10000000000 31888848696999 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3597424511/10000000000 : ℝ)^9 ≤ (13430809104533/50000000000000 : ℝ)^7 := by
    have hnat : (3597424511 : ℕ)^9*50000000000000^7 ≤ 13430809104533^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3597424511 10000000000 13430809104533 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(99034367/625000000 : ℝ), (7048160107/10000000000 : ℝ), (3597424511/10000000000 : ℝ)] ![(9360684378269/100000000000000 : ℝ), (31888848696999/50000000000000 : ℝ), (13430809104533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(99034367/625000000 : ℝ)|^9 ≤ (9360684378269/100000000000000 : ℝ)^7
        have hw : |(99034367/625000000 : ℝ)|=(99034367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7048160107/10000000000 : ℝ)|^9 ≤ (31888848696999/50000000000000 : ℝ)^7
        have hw : |(7048160107/10000000000 : ℝ)|=(7048160107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3597424511/10000000000 : ℝ)|^9 ≤ (13430809104533/50000000000000 : ℝ)^7
        have hw : |(3597424511/10000000000 : ℝ)|=(3597424511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2705862587/10000000000 : ℝ)*x 0 + (3906903449/5000000000 : ℝ)*x 1 + (-369331911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705862587/10000000000 : ℝ)^9 ≤ (2328184482201/12500000000000 : ℝ)^7 := by
    have hnat : (2705862587 : ℕ)^9*12500000000000^7 ≤ 2328184482201^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705862587 10000000000 2328184482201 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3906903449/5000000000 : ℝ)^9 ≤ (9102527986181/12500000000000 : ℝ)^7 := by
    have hnat : (3906903449 : ℕ)^9*12500000000000^7 ≤ 9102527986181^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3906903449 5000000000 9102527986181 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369331911/2500000000 : ℝ)^9 ≤ (342172009221/4000000000000 : ℝ)^7 := by
    have hnat : (369331911 : ℕ)^9*4000000000000^7 ≤ 342172009221^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369331911 2500000000 342172009221 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705862587/10000000000 : ℝ), (3906903449/5000000000 : ℝ), (-369331911/2500000000 : ℝ)] ![(2328184482201/12500000000000 : ℝ), (9102527986181/12500000000000 : ℝ), (342172009221/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705862587/10000000000 : ℝ)|^9 ≤ (2328184482201/12500000000000 : ℝ)^7
        have hw : |(2705862587/10000000000 : ℝ)|=(2705862587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3906903449/5000000000 : ℝ)|^9 ≤ (9102527986181/12500000000000 : ℝ)^7
        have hw : |(3906903449/5000000000 : ℝ)|=(3906903449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-369331911/2500000000 : ℝ)|^9 ≤ (342172009221/4000000000000 : ℝ)^7
        have hw : |(-369331911/2500000000 : ℝ)|=(369331911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1883582063/5000000000 : ℝ)*x 0 + (4561204269/10000000000 : ℝ)*x 1 + (-2212270217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1883582063/5000000000 : ℝ)^9 ≤ (5700406610699/20000000000000 : ℝ)^7 := by
    have hnat : (1883582063 : ℕ)^9*20000000000000^7 ≤ 5700406610699^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883582063 5000000000 5700406610699 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4561204269/10000000000 : ℝ)^9 ≤ (7289599478027/20000000000000 : ℝ)^7 := by
    have hnat : (4561204269 : ℕ)^9*20000000000000^7 ≤ 7289599478027^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561204269 10000000000 7289599478027 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212270217/5000000000 : ℝ)^9 ≤ (7009993909009/20000000000000 : ℝ)^7 := by
    have hnat : (2212270217 : ℕ)^9*20000000000000^7 ≤ 7009993909009^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212270217 5000000000 7009993909009 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1883582063/5000000000 : ℝ), (4561204269/10000000000 : ℝ), (-2212270217/5000000000 : ℝ)] ![(5700406610699/20000000000000 : ℝ), (7289599478027/20000000000000 : ℝ), (7009993909009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1883582063/5000000000 : ℝ)|^9 ≤ (5700406610699/20000000000000 : ℝ)^7
        have hw : |(-1883582063/5000000000 : ℝ)|=(1883582063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4561204269/10000000000 : ℝ)|^9 ≤ (7289599478027/20000000000000 : ℝ)^7
        have hw : |(4561204269/10000000000 : ℝ)|=(4561204269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2212270217/5000000000 : ℝ)|^9 ≤ (7009993909009/20000000000000 : ℝ)^7
        have hw : |(-2212270217/5000000000 : ℝ)|=(2212270217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3686451037/5000000000 : ℝ)*x 0 + (-1163024051/10000000000 : ℝ)*x 1 + (-1760497521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3686451037/5000000000 : ℝ)^9 ≤ (67580419681883/100000000000000 : ℝ)^7 := by
    have hnat : (3686451037 : ℕ)^9*100000000000000^7 ≤ 67580419681883^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686451037 5000000000 67580419681883 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163024051/10000000000 : ℝ)^9 ≤ (3144734910643/50000000000000 : ℝ)^7 := by
    have hnat : (1163024051 : ℕ)^9*50000000000000^7 ≤ 3144734910643^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163024051 10000000000 3144734910643 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1760497521/5000000000 : ℝ)^9 ≤ (13065055240217/50000000000000 : ℝ)^7 := by
    have hnat : (1760497521 : ℕ)^9*50000000000000^7 ≤ 13065055240217^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760497521 5000000000 13065055240217 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3686451037/5000000000 : ℝ), (-1163024051/10000000000 : ℝ), (-1760497521/5000000000 : ℝ)] ![(67580419681883/100000000000000 : ℝ), (3144734910643/50000000000000 : ℝ), (13065055240217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3686451037/5000000000 : ℝ)|^9 ≤ (67580419681883/100000000000000 : ℝ)^7
        have hw : |(3686451037/5000000000 : ℝ)|=(3686451037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1163024051/10000000000 : ℝ)|^9 ≤ (3144734910643/50000000000000 : ℝ)^7
        have hw : |(-1163024051/10000000000 : ℝ)|=(1163024051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1760497521/5000000000 : ℝ)|^9 ≤ (13065055240217/50000000000000 : ℝ)^7
        have hw : |(-1760497521/5000000000 : ℝ)|=(1760497521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (388826319/2000000000 : ℝ)*x 0 + (1315711921/2500000000 : ℝ)*x 1 + (1320491951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388826319/2000000000 : ℝ)^9 ≤ (12175993784973/100000000000000 : ℝ)^7 := by
    have hnat : (388826319 : ℕ)^9*100000000000000^7 ≤ 12175993784973^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388826319 2000000000 12175993784973 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315711921/2500000000 : ℝ)^9 ≤ (43809631606959/100000000000000 : ℝ)^7 := by
    have hnat : (1315711921 : ℕ)^9*100000000000000^7 ≤ 43809631606959^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315711921 2500000000 43809631606959 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320491951/2500000000 : ℝ)^9 ≤ (22007187296151/50000000000000 : ℝ)^7 := by
    have hnat : (1320491951 : ℕ)^9*50000000000000^7 ≤ 22007187296151^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320491951 2500000000 22007187296151 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(388826319/2000000000 : ℝ), (1315711921/2500000000 : ℝ), (1320491951/2500000000 : ℝ)] ![(12175993784973/100000000000000 : ℝ), (43809631606959/100000000000000 : ℝ), (22007187296151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(388826319/2000000000 : ℝ)|^9 ≤ (12175993784973/100000000000000 : ℝ)^7
        have hw : |(388826319/2000000000 : ℝ)|=(388826319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315711921/2500000000 : ℝ)|^9 ≤ (43809631606959/100000000000000 : ℝ)^7
        have hw : |(1315711921/2500000000 : ℝ)|=(1315711921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320491951/2500000000 : ℝ)|^9 ≤ (22007187296151/50000000000000 : ℝ)^7
        have hw : |(1320491951/2500000000 : ℝ)|=(1320491951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3104165351/10000000000 : ℝ)*x 0 + (6586718411/10000000000 : ℝ)*x 1 + (-2783755217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3104165351/10000000000 : ℝ)^9 ≤ (4444431607177/20000000000000 : ℝ)^7 := by
    have hnat : (3104165351 : ℕ)^9*20000000000000^7 ≤ 4444431607177^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104165351 10000000000 4444431607177 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6586718411/10000000000 : ℝ)^9 ≤ (14615049029367/25000000000000 : ℝ)^7 := by
    have hnat : (6586718411 : ℕ)^9*25000000000000^7 ≤ 14615049029367^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6586718411 10000000000 14615049029367 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2783755217/10000000000 : ℝ)^9 ≤ (19317645826417/100000000000000 : ℝ)^7 := by
    have hnat : (2783755217 : ℕ)^9*100000000000000^7 ≤ 19317645826417^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783755217 10000000000 19317645826417 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3104165351/10000000000 : ℝ), (6586718411/10000000000 : ℝ), (-2783755217/10000000000 : ℝ)] ![(4444431607177/20000000000000 : ℝ), (14615049029367/25000000000000 : ℝ), (19317645826417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3104165351/10000000000 : ℝ)|^9 ≤ (4444431607177/20000000000000 : ℝ)^7
        have hw : |(3104165351/10000000000 : ℝ)|=(3104165351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6586718411/10000000000 : ℝ)|^9 ≤ (14615049029367/25000000000000 : ℝ)^7
        have hw : |(6586718411/10000000000 : ℝ)|=(6586718411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2783755217/10000000000 : ℝ)|^9 ≤ (19317645826417/100000000000000 : ℝ)^7
        have hw : |(-2783755217/10000000000 : ℝ)|=(2783755217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-388353689/2000000000 : ℝ)*x 0 + (1371142891/2500000000 : ℝ)*x 1 + (-2529789059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388353689/2000000000 : ℝ)^9 ≤ (379905254803/3125000000000 : ℝ)^7 := by
    have hnat : (388353689 : ℕ)^9*3125000000000^7 ≤ 379905254803^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388353689 2000000000 379905254803 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371142891/2500000000 : ℝ)^9 ≤ (46196816930291/100000000000000 : ℝ)^7 := by
    have hnat : (1371142891 : ℕ)^9*100000000000000^7 ≤ 46196816930291^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371142891 2500000000 46196816930291 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529789059/5000000000 : ℝ)^9 ≤ (41646214901521/100000000000000 : ℝ)^7 := by
    have hnat : (2529789059 : ℕ)^9*100000000000000^7 ≤ 41646214901521^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529789059 5000000000 41646214901521 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388353689/2000000000 : ℝ), (1371142891/2500000000 : ℝ), (-2529789059/5000000000 : ℝ)] ![(379905254803/3125000000000 : ℝ), (46196816930291/100000000000000 : ℝ), (41646214901521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388353689/2000000000 : ℝ)|^9 ≤ (379905254803/3125000000000 : ℝ)^7
        have hw : |(-388353689/2000000000 : ℝ)|=(388353689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371142891/2500000000 : ℝ)|^9 ≤ (46196816930291/100000000000000 : ℝ)^7
        have hw : |(1371142891/2500000000 : ℝ)|=(1371142891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2529789059/5000000000 : ℝ)|^9 ≤ (41646214901521/100000000000000 : ℝ)^7
        have hw : |(-2529789059/5000000000 : ℝ)|=(2529789059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4224136423/5000000000 : ℝ)*x 0 + (-509422729/10000000000 : ℝ)*x 1 + (-511317267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224136423/5000000000 : ℝ)^9 ≤ (80509009442959/100000000000000 : ℝ)^7 := by
    have hnat : (4224136423 : ℕ)^9*100000000000000^7 ≤ 80509009442959^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224136423 5000000000 80509009442959 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509422729/10000000000 : ℝ)^9 ≤ (272008287483/12500000000000 : ℝ)^7 := by
    have hnat : (509422729 : ℕ)^9*12500000000000^7 ≤ 272008287483^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509422729 10000000000 272008287483 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511317267/2000000000 : ℝ)^9 ≤ (17314924238933/100000000000000 : ℝ)^7 := by
    have hnat : (511317267 : ℕ)^9*100000000000000^7 ≤ 17314924238933^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511317267 2000000000 17314924238933 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224136423/5000000000 : ℝ), (-509422729/10000000000 : ℝ), (-511317267/2000000000 : ℝ)] ![(80509009442959/100000000000000 : ℝ), (272008287483/12500000000000 : ℝ), (17314924238933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224136423/5000000000 : ℝ)|^9 ≤ (80509009442959/100000000000000 : ℝ)^7
        have hw : |(4224136423/5000000000 : ℝ)|=(4224136423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509422729/10000000000 : ℝ)|^9 ≤ (272008287483/12500000000000 : ℝ)^7
        have hw : |(-509422729/10000000000 : ℝ)|=(509422729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511317267/2000000000 : ℝ)|^9 ≤ (17314924238933/100000000000000 : ℝ)^7
        have hw : |(-511317267/2000000000 : ℝ)|=(511317267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (905892427/5000000000 : ℝ)*x 0 + (2951758211/5000000000 : ℝ)*x 1 + (922048/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905892427/5000000000 : ℝ)^9 ≤ (11120827108393/100000000000000 : ℝ)^7 := by
    have hnat : (905892427 : ℕ)^9*100000000000000^7 ≤ 11120827108393^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905892427 5000000000 11120827108393 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2951758211/5000000000 : ℝ)^9 ≤ (25391236976313/50000000000000 : ℝ)^7 := by
    have hnat : (2951758211 : ℕ)^9*50000000000000^7 ≤ 25391236976313^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2951758211 5000000000 25391236976313 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922048/1953125 : ℝ)^9 ≤ (7619339785121/20000000000000 : ℝ)^7 := by
    have hnat : (922048 : ℕ)^9*20000000000000^7 ≤ 7619339785121^7*1953125^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922048 1953125 7619339785121 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(905892427/5000000000 : ℝ), (2951758211/5000000000 : ℝ), (922048/1953125 : ℝ)] ![(11120827108393/100000000000000 : ℝ), (25391236976313/50000000000000 : ℝ), (7619339785121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(905892427/5000000000 : ℝ)|^9 ≤ (11120827108393/100000000000000 : ℝ)^7
        have hw : |(905892427/5000000000 : ℝ)|=(905892427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2951758211/5000000000 : ℝ)|^9 ≤ (25391236976313/50000000000000 : ℝ)^7
        have hw : |(2951758211/5000000000 : ℝ)|=(2951758211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(922048/1953125 : ℝ)|^9 ≤ (7619339785121/20000000000000 : ℝ)^7
        have hw : |(922048/1953125 : ℝ)|=(922048/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1269256263/2500000000 : ℝ)*x 0 + (5757431673/10000000000 : ℝ)*x 1 + (-1536391297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1269256263/2500000000 : ℝ)^9 ≤ (20915472684521/50000000000000 : ℝ)^7 := by
    have hnat : (1269256263 : ℕ)^9*50000000000000^7 ≤ 20915472684521^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269256263 2500000000 20915472684521 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5757431673/10000000000 : ℝ)^9 ≤ (6146568789221/12500000000000 : ℝ)^7 := by
    have hnat : (5757431673 : ℕ)^9*12500000000000^7 ≤ 6146568789221^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5757431673 10000000000 6146568789221 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1536391297/10000000000 : ℝ)^9 ≤ (140570379807/1562500000000 : ℝ)^7 := by
    have hnat : (1536391297 : ℕ)^9*1562500000000^7 ≤ 140570379807^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536391297 10000000000 140570379807 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1269256263/2500000000 : ℝ), (5757431673/10000000000 : ℝ), (-1536391297/10000000000 : ℝ)] ![(20915472684521/50000000000000 : ℝ), (6146568789221/12500000000000 : ℝ), (140570379807/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1269256263/2500000000 : ℝ)|^9 ≤ (20915472684521/50000000000000 : ℝ)^7
        have hw : |(1269256263/2500000000 : ℝ)|=(1269256263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5757431673/10000000000 : ℝ)|^9 ≤ (6146568789221/12500000000000 : ℝ)^7
        have hw : |(5757431673/10000000000 : ℝ)|=(5757431673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1536391297/10000000000 : ℝ)|^9 ≤ (140570379807/1562500000000 : ℝ)^7
        have hw : |(-1536391297/10000000000 : ℝ)|=(1536391297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-895369361/2500000000 : ℝ)*x 0 + (4653508963/10000000000 : ℝ)*x 1 + (-2253513041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895369361/2500000000 : ℝ)^9 ≤ (5341723716853/20000000000000 : ℝ)^7 := by
    have hnat : (895369361 : ℕ)^9*20000000000000^7 ≤ 5341723716853^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895369361 2500000000 5341723716853 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4653508963/10000000000 : ℝ)^9 ≤ (7479812457911/20000000000000 : ℝ)^7 := by
    have hnat : (4653508963 : ℕ)^9*20000000000000^7 ≤ 7479812457911^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4653508963 10000000000 7479812457911 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253513041/5000000000 : ℝ)^9 ≤ (3589231910759/10000000000000 : ℝ)^7 := by
    have hnat : (2253513041 : ℕ)^9*10000000000000^7 ≤ 3589231910759^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253513041 5000000000 3589231910759 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-895369361/2500000000 : ℝ), (4653508963/10000000000 : ℝ), (-2253513041/5000000000 : ℝ)] ![(5341723716853/20000000000000 : ℝ), (7479812457911/20000000000000 : ℝ), (3589231910759/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-895369361/2500000000 : ℝ)|^9 ≤ (5341723716853/20000000000000 : ℝ)^7
        have hw : |(-895369361/2500000000 : ℝ)|=(895369361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4653508963/10000000000 : ℝ)|^9 ≤ (7479812457911/20000000000000 : ℝ)^7
        have hw : |(4653508963/10000000000 : ℝ)|=(4653508963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253513041/5000000000 : ℝ)|^9 ≤ (3589231910759/10000000000000 : ℝ)^7
        have hw : |(-2253513041/5000000000 : ℝ)|=(2253513041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1424055823/2500000000 : ℝ)*x 0 + (-516214413/2000000000 : ℝ)*x 1 + (-4318150041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1424055823/2500000000 : ℝ)^9 ≤ (48501449848401/100000000000000 : ℝ)^7 := by
    have hnat : (1424055823 : ℕ)^9*100000000000000^7 ≤ 48501449848401^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424055823 2500000000 48501449848401 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516214413/2000000000 : ℝ)^9 ≤ (1752843025301/10000000000000 : ℝ)^7 := by
    have hnat : (516214413 : ℕ)^9*10000000000000^7 ≤ 1752843025301^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516214413 2000000000 1752843025301 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4318150041/10000000000 : ℝ)^9 ≤ (339701198821/1000000000000 : ℝ)^7 := by
    have hnat : (4318150041 : ℕ)^9*1000000000000^7 ≤ 339701198821^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318150041 10000000000 339701198821 1000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1424055823/2500000000 : ℝ), (-516214413/2000000000 : ℝ), (-4318150041/10000000000 : ℝ)] ![(48501449848401/100000000000000 : ℝ), (1752843025301/10000000000000 : ℝ), (339701198821/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1424055823/2500000000 : ℝ)|^9 ≤ (48501449848401/100000000000000 : ℝ)^7
        have hw : |(1424055823/2500000000 : ℝ)|=(1424055823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516214413/2000000000 : ℝ)|^9 ≤ (1752843025301/10000000000000 : ℝ)^7
        have hw : |(-516214413/2000000000 : ℝ)|=(516214413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4318150041/10000000000 : ℝ)|^9 ≤ (339701198821/1000000000000 : ℝ)^7
        have hw : |(-4318150041/10000000000 : ℝ)|=(4318150041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (217172521/625000000 : ℝ)*x 0 + (1220753523/2500000000 : ℝ)*x 1 + (2186365223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217172521/625000000 : ℝ)^9 ≤ (25689788478017/100000000000000 : ℝ)^7 := by
    have hnat : (217172521 : ℕ)^9*100000000000000^7 ≤ 25689788478017^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217172521 625000000 25689788478017 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220753523/2500000000 : ℝ)^9 ≤ (7957409007381/20000000000000 : ℝ)^7 := by
    have hnat : (1220753523 : ℕ)^9*20000000000000^7 ≤ 7957409007381^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220753523 2500000000 7957409007381 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186365223/5000000000 : ℝ)^9 ≤ (8630791618801/25000000000000 : ℝ)^7 := by
    have hnat : (2186365223 : ℕ)^9*25000000000000^7 ≤ 8630791618801^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186365223 5000000000 8630791618801 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217172521/625000000 : ℝ), (1220753523/2500000000 : ℝ), (2186365223/5000000000 : ℝ)] ![(25689788478017/100000000000000 : ℝ), (7957409007381/20000000000000 : ℝ), (8630791618801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217172521/625000000 : ℝ)|^9 ≤ (25689788478017/100000000000000 : ℝ)^7
        have hw : |(217172521/625000000 : ℝ)|=(217172521/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1220753523/2500000000 : ℝ)|^9 ≤ (7957409007381/20000000000000 : ℝ)^7
        have hw : |(1220753523/2500000000 : ℝ)|=(1220753523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2186365223/5000000000 : ℝ)|^9 ≤ (8630791618801/25000000000000 : ℝ)^7
        have hw : |(2186365223/5000000000 : ℝ)|=(2186365223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310030_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4082520761/10000000000 : ℝ)*x 0 + (5490211151/10000000000 : ℝ)*x 1 + (-3094846583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4082520761/10000000000 : ℝ)^9 ≤ (31605676329069/100000000000000 : ℝ)^7 := by
    have hnat : (4082520761 : ℕ)^9*100000000000000^7 ≤ 31605676329069^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082520761 10000000000 31605676329069 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490211151/10000000000 : ℝ)^9 ≤ (46257900567703/100000000000000 : ℝ)^7 := by
    have hnat : (5490211151 : ℕ)^9*100000000000000^7 ≤ 46257900567703^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490211151 10000000000 46257900567703 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3094846583/10000000000 : ℝ)^9 ≤ (2213642307993/10000000000000 : ℝ)^7 := by
    have hnat : (3094846583 : ℕ)^9*10000000000000^7 ≤ 2213642307993^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3094846583 10000000000 2213642307993 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4082520761/10000000000 : ℝ), (5490211151/10000000000 : ℝ), (-3094846583/10000000000 : ℝ)] ![(31605676329069/100000000000000 : ℝ), (46257900567703/100000000000000 : ℝ), (2213642307993/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4082520761/10000000000 : ℝ)|^9 ≤ (31605676329069/100000000000000 : ℝ)^7
        have hw : |(4082520761/10000000000 : ℝ)|=(4082520761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490211151/10000000000 : ℝ)|^9 ≤ (46257900567703/100000000000000 : ℝ)^7
        have hw : |(5490211151/10000000000 : ℝ)|=(5490211151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3094846583/10000000000 : ℝ)|^9 ≤ (2213642307993/10000000000000 : ℝ)^7
        have hw : |(-3094846583/10000000000 : ℝ)|=(3094846583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310030 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]]) : False := by
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
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((1747288599/2500000000 : ℝ)*X 1 0+(-221110913/2000000000 : ℝ)*X 1 1+(-2011538189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((671338931/2500000000 : ℝ)*X 2 0+(1101500841/2000000000 : ℝ)*X 2 1+(1107620513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2720400381/10000000000 : ℝ)*X 0 0+(1828153037/5000000000 : ℝ)*X 0 1+(-3088080463/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1849096113/2500000000 : ℝ)*X 1 0+(-273320549/10000000000 : ℝ)*X 1 1+(-4038225471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((99034367/625000000 : ℝ)*X 2 0+(7048160107/10000000000 : ℝ)*X 2 1+(3597424511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((2705862587/10000000000 : ℝ)*X 0 0+(3906903449/5000000000 : ℝ)*X 0 1+(-369331911/2500000000 : ℝ)*X 0 2+(2705862587/10000000000 : ℝ)*X 1 0+(3906903449/5000000000 : ℝ)*X 1 1+(-369331911/2500000000 : ℝ)*X 1 2+(2705862587/10000000000 : ℝ)*X 2 0+(3906903449/5000000000 : ℝ)*X 2 1+(-369331911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1883582063/5000000000 : ℝ)*X 0 0+(4561204269/10000000000 : ℝ)*X 0 1+(-2212270217/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3686451037/5000000000 : ℝ)*X 1 0+(-1163024051/10000000000 : ℝ)*X 1 1+(-1760497521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((388826319/2000000000 : ℝ)*X 2 0+(1315711921/2500000000 : ℝ)*X 2 1+(1320491951/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((3104165351/10000000000 : ℝ)*X 0 0+(6586718411/10000000000 : ℝ)*X 0 1+(-2783755217/10000000000 : ℝ)*X 0 2+(3104165351/10000000000 : ℝ)*X 1 0+(6586718411/10000000000 : ℝ)*X 1 1+(-2783755217/10000000000 : ℝ)*X 1 2+(3104165351/10000000000 : ℝ)*X 2 0+(6586718411/10000000000 : ℝ)*X 2 1+(-2783755217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-388353689/2000000000 : ℝ)*X 0 0+(1371142891/2500000000 : ℝ)*X 0 1+(-2529789059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((4224136423/5000000000 : ℝ)*X 1 0+(-509422729/10000000000 : ℝ)*X 1 1+(-511317267/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((905892427/5000000000 : ℝ)*X 2 0+(2951758211/5000000000 : ℝ)*X 2 1+(922048/1953125 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1269256263/2500000000 : ℝ)*X 0 0+(5757431673/10000000000 : ℝ)*X 0 1+(-1536391297/10000000000 : ℝ)*X 0 2+(1269256263/2500000000 : ℝ)*X 1 0+(5757431673/10000000000 : ℝ)*X 1 1+(-1536391297/10000000000 : ℝ)*X 1 2+(1269256263/2500000000 : ℝ)*X 2 0+(5757431673/10000000000 : ℝ)*X 2 1+(-1536391297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((37809/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37809/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (49748584440050492525829/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (830272740253/1000000000000 : ℝ)*(base39) + (966291925283/1000000000000 : ℝ)*(base49) + (585831023569/500000000000 : ℝ)*(base50) + (440107802001/1000000000000 : ℝ)*(base60) + (3505351838023/1000000000000 : ℝ)*(major_s0_0) + (3505351838023/1000000000000 : ℝ)*(major_s0_1) + (3505351838023/1000000000000 : ℝ)*(major_s0_2) + (75338593/1000000000000 : ℝ)*(sp_s0_1) + (1211029268779/250000000000 : ℝ)*(sp_s0_7) + (302753700021/62500000000 : ℝ)*(sp_s0_8) + (4844081526221/1000000000000 : ℝ)*(sp_s0_9) + (1083282910269/500000000000 : ℝ)*(sp_s0_12) + (8731907/500000000000 : ℝ)*(sp_s0_20) + (13253177/250000000000 : ℝ)*(sp_s0_22) + (1083282910269/500000000000 : ℝ)*(f.failure) + (484413453893/100000000000 : ℝ)*(f.sum) + (19807831/500000000000000000000 : ℝ)*base63 + (909136491658057/10000000000000000000000000000 : ℝ)*base65 + (1519739235658057/10000000000000000000000000000 : ℝ)*base67 + (8656734865671731/10000000000000000000000000000 : ℝ)*base69 + (337241236917553/2500000000000000000000000000 : ℝ)*base70 + (7920585822341943/10000000000000000000000000000 : ℝ)*base72 + (4210342478328269/10000000000000000000000000000 : ℝ)*base75 + (6951299824671731/10000000000000000000000000000 : ℝ)*base77 + (2331803026158057/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (2317/50000000000000000 : ℝ)*base87 + (2317/50000000000000000 : ℝ)*base89 + (2317/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(10137/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(10137/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4080707582481927714309/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76233/5000000000 : ℝ)*(base3) + (618772424483/1000000000000 : ℝ)*(base39) + (279302153817/1000000000000 : ℝ)*(base49) + (10621756181/100000000000 : ℝ)*(base60) + (271885389763/100000000000 : ℝ)*(major_s0_0) + (271885389763/100000000000 : ℝ)*(major_s0_1) + (271885389763/100000000000 : ℝ)*(major_s0_2) + (58963513/1000000000000 : ℝ)*(sp_s0_1) + (35460421/1000000000000 : ℝ)*(sp_s0_2) + (14534613/125000000000 : ℝ)*(sp_s0_8) + (3757250234857/1000000000000 : ℝ)*(sp_s0_13) + (46963628013/12500000000 : ℝ)*(sp_s0_14) + (939303693609/250000000000 : ℝ)*(sp_s0_15) + (336087374571/200000000000 : ℝ)*(sp_s0_19) + (336090423891/200000000000 : ℝ)*(f.failure) + (3757250234857/1000000000000 : ℝ)*(f.sum) + (918307123/10000000000000000000000 : ℝ)*base62 + (606411949696717/1000000000000000000000000000 : ℝ)*base65 + (557560009203283/1000000000000000000000000000 : ℝ)*base66 + (185011273320511/1000000000000000000000000000 : ℝ)*base69 + (81114769129307/250000000000000000000000000 : ℝ)*base71 + (620736665203283/1000000000000000000000000000 : ℝ)*base72 + (331352111679489/1000000000000000000000000000 : ℝ)*base75 + (492111662020511/1000000000000000000000000000 : ℝ)*base77 + (243983651553283/500000000000000000000000000 : ℝ)*base78 + (3437/20000000000000000 : ℝ)*base86 + (3437/20000000000000000 : ℝ)*base88 + (3437/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-32323/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-32323/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1956531424561901637363/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1590181/1000000000000 : ℝ)*(base11) + (545656060009/500000000000 : ℝ)*(base39) + (413648550651/500000000000 : ℝ)*(base49) + (853172193437/1000000000000 : ℝ)*(base50) + (645969668741/200000000000 : ℝ)*(major_s0_0) + (645969668741/200000000000 : ℝ)*(major_s0_1) + (645969668741/200000000000 : ℝ)*(major_s0_2) + (27044711/1000000000000 : ℝ)*(sp_s0_2) + (201309/12500000000 : ℝ)*(sp_s0_9) + (250017/250000000000 : ℝ)*(sp_s0_14) + (4463409439583/1000000000000 : ℝ)*(sp_s0_20) + (4463410029697/1000000000000 : ℝ)*(sp_s0_21) + (2231683940167/500000000000 : ℝ)*(sp_s0_22) + (1996284353281/1000000000000 : ℝ)*(sp_s0_25) + (1996284353281/1000000000000 : ℝ)*(f.failure) + (1115852757441/250000000000 : ℝ)*(f.sum) + (4147962823/10000000000000000000000 : ℝ)*base63 + (1981957021520619/2000000000000000000000000000 : ℝ)*base65 + (529977543279381/2000000000000000000000000000 : ℝ)*base66 + (156064080762377/2000000000000000000000000000 : ℝ)*base69 + (202339310520749/500000000000000000000000000 : ℝ)*base71 + (335135831879381/2000000000000000000000000000 : ℝ)*base72 + (1066161367637623/2000000000000000000000000000 : ℝ)*base75 + (528227170762377/2000000000000000000000000000 : ℝ)*base77 + (240372320979381/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (107167/100000000000000000 : ℝ)*base86 + (107167/100000000000000000 : ℝ)*base88 + (107167/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (37809/100000 : ℝ) ^ (35/8 : ℝ) ≤ (1418988776857574473/100000000000000000000 : ℝ) := by
    have hpowers : (37809/100000 : ℝ)^35 ≤ (1418988776857574473/100000000000000000000 : ℝ)^8 := by
      have hnat : (37809 : ℕ)^35*100000000000000000000^8 ≤ 1418988776857574473^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37809 100000 1418988776857574473 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37809/100000 : ℝ)) (X := (1418988776857574473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (101418988776857574473/100000000000000000000 : ℝ) ≤ (1254032247851153/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (101418988776857574473/100000000000000000000 : ℝ)^8 ≤ (1254032247851153/1250000000000000 : ℝ)^35 := by
      have hnat : (101418988776857574473 : ℕ)^8*1250000000000000^35 ≤ 1254032247851153^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101418988776857574473 100000000000000000000 1254032247851153 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254032247851153/1250000000000000 : ℝ)) (X := (101418988776857574473/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (51418988776857574473/50000000000000000000 : ℝ) ≤ (10064169651252513/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (51418988776857574473/50000000000000000000 : ℝ)^8 ≤ (10064169651252513/10000000000000000 : ℝ)^35 := by
      have hnat : (51418988776857574473 : ℕ)^8*10000000000000000^35 ≤ 10064169651252513^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51418988776857574473 50000000000000000000 10064169651252513 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10064169651252513/10000000000000000 : ℝ)) (X := (51418988776857574473/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(448027539017/52512500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(31911668443289/3780900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (37809/100000 : ℝ)) (alpha := (448027539017/52512500000000 : ℝ)) (beta := (31911668443289/3780900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37809/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(448027539017/52512500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(31911668443289/3780900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (10137/100000 : ℝ) ^ (35/8 : ℝ) ≤ (4475626415391613/100000000000000000000 : ℝ) := by
    have hpowers : (10137/100000 : ℝ)^35 ≤ (4475626415391613/100000000000000000000 : ℝ)^8 := by
      have hnat : (10137 : ℕ)^35*100000000000000000000^8 ≤ 4475626415391613^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10137 100000 4475626415391613 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10137/100000 : ℝ)) (X := (4475626415391613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100004475626415391613/100000000000000000000 : ℝ) ≤ (500005114913319/500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100004475626415391613/100000000000000000000 : ℝ)^8 ≤ (500005114913319/500000000000000 : ℝ)^35 := by
      have hnat : (100004475626415391613 : ℕ)^8*500000000000000^35 ≤ 500005114913319^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100004475626415391613 100000000000000000000 500005114913319 500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500005114913319/500000000000000 : ℝ)) (X := (100004475626415391613/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50004475626415391613/50000000000000000000 : ℝ) ≤ (5000102296500501/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50004475626415391613/50000000000000000000 : ℝ)^8 ≤ (5000102296500501/5000000000000000 : ℝ)^35 := by
      have hnat : (50004475626415391613 : ℕ)^8*5000000000000000^35 ≤ 5000102296500501^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004475626415391613 50000000000000000000 5000102296500501 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000102296500501/5000000000000000 : ℝ)) (X := (50004475626415391613/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(5114913319/50685000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(17049122437/168950000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (10137/100000 : ℝ)) (alpha := (5114913319/50685000000000 : ℝ)) (beta := (17049122437/168950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (10137/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(5114913319/50685000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(17049122437/168950000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (32323/100000 : ℝ) ^ (35/8 : ℝ) ≤ (357341557966391519/50000000000000000000 : ℝ) := by
    have hpowers : (32323/100000 : ℝ)^35 ≤ (357341557966391519/50000000000000000000 : ℝ)^8 := by
      have hnat : (32323 : ℕ)^35*50000000000000000000^8 ≤ 357341557966391519^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32323 100000 357341557966391519 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32323/100000 : ℝ)) (X := (357341557966391519/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50357341557966391519/50000000000000000000 : ℝ) ≤ (5008145385926363/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50357341557966391519/50000000000000000000 : ℝ)^8 ≤ (5008145385926363/5000000000000000 : ℝ)^35 := by
      have hnat : (50357341557966391519 : ℕ)^8*5000000000000000^35 ≤ 5008145385926363^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50357341557966391519 50000000000000000000 5008145385926363 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008145385926363/5000000000000000 : ℝ)) (X := (50357341557966391519/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25357341557966391519/25000000000000000000 : ℝ) ≤ (10032492608237149/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25357341557966391519/25000000000000000000 : ℝ)^8 ≤ (10032492608237149/10000000000000000 : ℝ)^35 := by
      have hnat : (25357341557966391519 : ℕ)^8*10000000000000000^35 ≤ 10032492608237149^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25357341557966391519 25000000000000000000 10032492608237149 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032492608237149/10000000000000000 : ℝ)) (X := (25357341557966391519/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(8145385926363/1616150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16201836384423/3232300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (32323/100000 : ℝ)) (alpha := (8145385926363/1616150000000000 : ℝ)) (beta := (16201836384423/3232300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (32323/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(8145385926363/1616150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16201836384423/3232300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-895369361/2500000000 : ℝ)*X 0 0+(4653508963/10000000000 : ℝ)*X 0 1+(-2253513041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1424055823/2500000000 : ℝ)*X 1 0+(-516214413/2000000000 : ℝ)*X 1 1+(-4318150041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((217172521/625000000 : ℝ)*X 2 0+(1220753523/2500000000 : ℝ)*X 2 1+(2186365223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4082520761/10000000000 : ℝ)*X 0 0+(5490211151/10000000000 : ℝ)*X 0 1+(-3094846583/10000000000 : ℝ)*X 0 2+(4082520761/10000000000 : ℝ)*X 1 0+(5490211151/10000000000 : ℝ)*X 1 1+(-3094846583/10000000000 : ℝ)*X 1 2+(4082520761/10000000000 : ℝ)*X 2 0+(5490211151/10000000000 : ℝ)*X 2 1+(-3094846583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310030_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-30521013349238570498743257661257801/4588307708170000000000000000000000 : ℝ) := by norm_num
    linear_combination (406527/1000000000000 : ℝ)*(base11) + (111/80000000 : ℝ)*(base15) + (707923/1000000000000 : ℝ)*(base29) + (337325605971/1000000000000 : ℝ)*(base39) + (46749572239/62500000000 : ℝ)*(base49) + (109763771099/250000000000 : ℝ)*(base50) + (45193979469/1000000000000 : ℝ)*(base60) + (160727/500000000000 : ℝ)*(ratio_s0_2) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (110865158771/50000000000 : ℝ)*(sp_s1_0) + (2217302194447/1000000000000 : ℝ)*(sp_s1_1) + (2217303581947/1000000000000 : ℝ)*(sp_s1_2) + (999999292077/1000000000000 : ℝ)*(sp_s1_6) + (2217303581947/1000000000000 : ℝ)*(f.sum) + (493517706022300211/1092194170000000000000000000000 : ℝ)*base63 + (82613763467899/323230000000000000000000000 : ℝ)*base65 + (21004564851449/33790000000000000000000000 : ℝ)*base67 + (42372638378917/323230000000000000000000000 : ℝ)*base69 + (3689180728421239/339472307500000000000000000000 : ℝ)*base70 + (4277277919591/21005000000000000000000000 : ℝ)*base72 + (18150047577969/33790000000000000000000000 : ℝ)*base75 + (3675101701951/42010000000000000000000000 : ℝ)*base76 + (59884991860205691/141951790000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p010_b018 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=30 ∨ c=31 := by omega
  rcases hc with rfl|rfl
  · exact collision_c310030 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310031 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b018 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

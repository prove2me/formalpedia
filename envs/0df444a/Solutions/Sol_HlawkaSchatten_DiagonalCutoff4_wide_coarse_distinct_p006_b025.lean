-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p006_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:49.454324+00:00
-- url     : https://prove2.me/submissions/68bab905-0b35-46ca-b9d8-d9cda2225dee

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s5
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s7
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304047
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304048
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304049
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304050
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304051
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304052
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c306053 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c306053_s0 p hpa hpb X hX
  have h1 := collision_c306053_s1 p hpa hpb X hX h0
  have h2 := collision_c306053_s2 p hpa hpb X hX h1
  have h3 := collision_c306053_s3 p hpa hpb X hX h2
  have h4 := collision_c306053_s4 p hpa hpb X hX h3
  have h5 := collision_c306053_s5 p hpa hpb X hX h4
  have h6 := collision_c306053_s6 p hpa hpb X hX h5
  exact collision_c306053_s7 p hpa hpb X hX h6

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
theorem collision_support_c306046_s0_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-64105973/500000000 : ℝ)*x 0 + (-2779115763/5000000000 : ℝ)*x 1 + (-1389557881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64105973/500000000 : ℝ)^69 ≤ (6896422907417/100000000000000 : ℝ)^53 := by
    have hnat : (64105973 : ℕ)^69*100000000000000^53 ≤ 6896422907417^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64105973 500000000 6896422907417 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779115763/5000000000 : ℝ)^69 ≤ (46551788549411/100000000000000 : ℝ)^53 := by
    have hnat : (2779115763 : ℕ)^69*100000000000000^53 ≤ 46551788549411^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779115763 5000000000 46551788549411 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389557881/2500000000 : ℝ)^69 ≤ (11637947131901/25000000000000 : ℝ)^53 := by
    have hnat : (1389557881 : ℕ)^69*25000000000000^53 ≤ 11637947131901^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389557881 2500000000 11637947131901 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-64105973/500000000 : ℝ), (-2779115763/5000000000 : ℝ), (-1389557881/2500000000 : ℝ)] ![(6896422907417/100000000000000 : ℝ), (46551788549411/100000000000000 : ℝ), (11637947131901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-64105973/500000000 : ℝ)|^69 ≤ (6896422907417/100000000000000 : ℝ)^53
        have hw : |(-64105973/500000000 : ℝ)|=(64105973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2779115763/5000000000 : ℝ)|^69 ≤ (46551788549411/100000000000000 : ℝ)^53
        have hw : |(-2779115763/5000000000 : ℝ)|=(2779115763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1389557881/2500000000 : ℝ)|^69 ≤ (11637947131901/25000000000000 : ℝ)^53
        have hw : |(-1389557881/2500000000 : ℝ)|=(1389557881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (941851927/2000000000 : ℝ)*x 0 + (-2045825637/5000000000 : ℝ)*x 1 + (163666051/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941851927/2000000000 : ℝ)^69 ≤ (7503283409497/20000000000000 : ℝ)^53 := by
    have hnat : (941851927 : ℕ)^69*20000000000000^53 ≤ 7503283409497^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941851927 2000000000 7503283409497 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045825637/5000000000 : ℝ)^69 ≤ (15620895731817/50000000000000 : ℝ)^53 := by
    have hnat : (2045825637 : ℕ)^69*50000000000000^53 ≤ 15620895731817^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045825637 5000000000 15620895731817 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163666051/400000000 : ℝ)^69 ≤ (15620895736787/50000000000000 : ℝ)^53 := by
    have hnat : (163666051 : ℕ)^69*50000000000000^53 ≤ 15620895736787^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163666051 400000000 15620895736787 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(941851927/2000000000 : ℝ), (-2045825637/5000000000 : ℝ), (163666051/400000000 : ℝ)] ![(7503283409497/20000000000000 : ℝ), (15620895731817/50000000000000 : ℝ), (15620895736787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(941851927/2000000000 : ℝ)|^69 ≤ (7503283409497/20000000000000 : ℝ)^53
        have hw : |(941851927/2000000000 : ℝ)|=(941851927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045825637/5000000000 : ℝ)|^69 ≤ (15620895731817/50000000000000 : ℝ)^53
        have hw : |(-2045825637/5000000000 : ℝ)|=(2045825637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163666051/400000000 : ℝ)|^69 ≤ (15620895736787/50000000000000 : ℝ)^53
        have hw : |(163666051/400000000 : ℝ)|=(163666051/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^69 ≤ (1 : ℝ)^53 := by
    have hnat : (1 : ℕ)^69*1^53 ≤ 1^53*1^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^69 ≤ (0 : ℝ)^53 := by
    have hnat : (0 : ℕ)^69*1^53 ≤ 0^53*1^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^69 ≤ (0 : ℝ)^53 := by
    have hnat : (0 : ℕ)^69*1^53 ≤ 0^53*1^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^69 ≤ (1 : ℝ)^53
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^69 ≤ (0 : ℝ)^53
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^69 ≤ (0 : ℝ)^53
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-628259303/5000000000 : ℝ)*x 0 + (-2995486223/5000000000 : ℝ)*x 1 + (-40092643/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (628259303/5000000000 : ℝ)^69 ≤ (6717689397333/100000000000000 : ℝ)^53 := by
    have hnat : (628259303 : ℕ)^69*100000000000000^53 ≤ 6717689397333^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628259303 5000000000 6717689397333 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2995486223/5000000000 : ℝ)^69 ≤ (25662366716627/50000000000000 : ℝ)^53 := by
    have hnat : (2995486223 : ℕ)^69*50000000000000^53 ≤ 25662366716627^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995486223 5000000000 25662366716627 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40092643/78125000 : ℝ)^69 ≤ (41957577159877/100000000000000 : ℝ)^53 := by
    have hnat : (40092643 : ℕ)^69*100000000000000^53 ≤ 41957577159877^53*78125000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40092643 78125000 41957577159877 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-628259303/5000000000 : ℝ), (-2995486223/5000000000 : ℝ), (-40092643/78125000 : ℝ)] ![(6717689397333/100000000000000 : ℝ), (25662366716627/50000000000000 : ℝ), (41957577159877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-628259303/5000000000 : ℝ)|^69 ≤ (6717689397333/100000000000000 : ℝ)^53
        have hw : |(-628259303/5000000000 : ℝ)|=(628259303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2995486223/5000000000 : ℝ)|^69 ≤ (25662366716627/50000000000000 : ℝ)^53
        have hw : |(-2995486223/5000000000 : ℝ)|=(2995486223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40092643/78125000 : ℝ)|^69 ≤ (41957577159877/100000000000000 : ℝ)^53
        have hw : |(-40092643/78125000 : ℝ)|=(40092643/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (897379783/2000000000 : ℝ)*x 0 + (5105599433/10000000000 : ℝ)*x 1 + (-811047659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897379783/2000000000 : ℝ)^69 ≤ (2201676380327/6250000000000 : ℝ)^53 := by
    have hnat : (897379783 : ℕ)^69*6250000000000^53 ≤ 2201676380327^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897379783 2000000000 2201676380327 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5105599433/10000000000 : ℝ)^69 ≤ (41678291229591/100000000000000 : ℝ)^53 := by
    have hnat : (5105599433 : ℕ)^69*100000000000000^53 ≤ 41678291229591^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5105599433 10000000000 41678291229591 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (811047659/2500000000 : ℝ)^69 ≤ (23094886674467/100000000000000 : ℝ)^53 := by
    have hnat : (811047659 : ℕ)^69*100000000000000^53 ≤ 23094886674467^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811047659 2500000000 23094886674467 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897379783/2000000000 : ℝ), (5105599433/10000000000 : ℝ), (-811047659/2500000000 : ℝ)] ![(2201676380327/6250000000000 : ℝ), (41678291229591/100000000000000 : ℝ), (23094886674467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897379783/2000000000 : ℝ)|^69 ≤ (2201676380327/6250000000000 : ℝ)^53
        have hw : |(897379783/2000000000 : ℝ)|=(897379783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5105599433/10000000000 : ℝ)|^69 ≤ (41678291229591/100000000000000 : ℝ)^53
        have hw : |(5105599433/10000000000 : ℝ)|=(5105599433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-811047659/2500000000 : ℝ)|^69 ≤ (23094886674467/100000000000000 : ℝ)^53
        have hw : |(-811047659/2500000000 : ℝ)|=(811047659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4486898997/10000000000 : ℝ)*x 0 + (-636339761/2000000000 : ℝ)*x 1 + (2579925003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486898997/10000000000 : ℝ)^69 ≤ (4403352865421/12500000000000 : ℝ)^53 := by
    have hnat : (4486898997 : ℕ)^69*12500000000000^53 ≤ 4403352865421^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486898997 10000000000 4403352865421 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636339761/2000000000 : ℝ)^69 ≤ (11258704211503/50000000000000 : ℝ)^53 := by
    have hnat : (636339761 : ℕ)^69*50000000000000^53 ≤ 11258704211503^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636339761 2000000000 11258704211503 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579925003/5000000000 : ℝ)^69 ≤ (42255768643893/100000000000000 : ℝ)^53 := by
    have hnat : (2579925003 : ℕ)^69*100000000000000^53 ≤ 42255768643893^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579925003 5000000000 42255768643893 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4486898997/10000000000 : ℝ), (-636339761/2000000000 : ℝ), (2579925003/5000000000 : ℝ)] ![(4403352865421/12500000000000 : ℝ), (11258704211503/50000000000000 : ℝ), (42255768643893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4486898997/10000000000 : ℝ)|^69 ≤ (4403352865421/12500000000000 : ℝ)^53
        have hw : |(4486898997/10000000000 : ℝ)|=(4486898997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-636339761/2000000000 : ℝ)|^69 ≤ (11258704211503/50000000000000 : ℝ)^53
        have hw : |(-636339761/2000000000 : ℝ)|=(636339761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2579925003/5000000000 : ℝ)|^69 ≤ (42255768643893/100000000000000 : ℝ)^53
        have hw : |(2579925003/5000000000 : ℝ)|=(2579925003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8169410559/10000000000 : ℝ)*x 0 + (-4341131/40000000 : ℝ)*x 1 + (-2632175927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8169410559/10000000000 : ℝ)^69 ≤ (38428396717911/50000000000000 : ℝ)^53 := by
    have hnat : (8169410559 : ℕ)^69*50000000000000^53 ≤ 38428396717911^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8169410559 10000000000 38428396717911 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4341131/40000000 : ℝ)^69 ≤ (5551189331771/100000000000000 : ℝ)^53 := by
    have hnat : (4341131 : ℕ)^69*100000000000000^53 ≤ 5551189331771^53*40000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341131 40000000 5551189331771 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632175927/10000000000 : ℝ)^69 ≤ (17592017214023/100000000000000 : ℝ)^53 := by
    have hnat : (2632175927 : ℕ)^69*100000000000000^53 ≤ 17592017214023^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632175927 10000000000 17592017214023 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8169410559/10000000000 : ℝ), (-4341131/40000000 : ℝ), (-2632175927/10000000000 : ℝ)] ![(38428396717911/50000000000000 : ℝ), (5551189331771/100000000000000 : ℝ), (17592017214023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8169410559/10000000000 : ℝ)|^69 ≤ (38428396717911/50000000000000 : ℝ)^53
        have hw : |(8169410559/10000000000 : ℝ)|=(8169410559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4341131/40000000 : ℝ)|^69 ≤ (5551189331771/100000000000000 : ℝ)^53
        have hw : |(-4341131/40000000 : ℝ)|=(4341131/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2632175927/10000000000 : ℝ)|^69 ≤ (17592017214023/100000000000000 : ℝ)^53
        have hw : |(-2632175927/10000000000 : ℝ)|=(2632175927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-279988723/10000000000 : ℝ)*x 0 + (-5440688011/10000000000 : ℝ)*x 1 + (-6209414811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279988723/10000000000 : ℝ)^69 ≤ (951377285379/100000000000000 : ℝ)^53 := by
    have hnat : (279988723 : ℕ)^69*100000000000000^53 ≤ 951377285379^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279988723 10000000000 951377285379 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440688011/10000000000 : ℝ)^69 ≤ (11318560892859/25000000000000 : ℝ)^53 := by
    have hnat : (5440688011 : ℕ)^69*25000000000000^53 ≤ 11318560892859^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440688011 10000000000 11318560892859 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6209414811/10000000000 : ℝ)^69 ≤ (53774379127057/100000000000000 : ℝ)^53 := by
    have hnat : (6209414811 : ℕ)^69*100000000000000^53 ≤ 53774379127057^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6209414811 10000000000 53774379127057 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-279988723/10000000000 : ℝ), (-5440688011/10000000000 : ℝ), (-6209414811/10000000000 : ℝ)] ![(951377285379/100000000000000 : ℝ), (11318560892859/25000000000000 : ℝ), (53774379127057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-279988723/10000000000 : ℝ)|^69 ≤ (951377285379/100000000000000 : ℝ)^53
        have hw : |(-279988723/10000000000 : ℝ)|=(279988723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5440688011/10000000000 : ℝ)|^69 ≤ (11318560892859/25000000000000 : ℝ)^53
        have hw : |(-5440688011/10000000000 : ℝ)|=(5440688011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6209414811/10000000000 : ℝ)|^69 ≤ (53774379127057/100000000000000 : ℝ)^53
        have hw : |(-6209414811/10000000000 : ℝ)|=(6209414811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4119297987/10000000000 : ℝ)*x 0 + (4164095373/10000000000 : ℝ)*x 1 + (-115320411/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119297987/10000000000 : ℝ)^69 ≤ (31516894929031/100000000000000 : ℝ)^53 := by
    have hnat : (4119297987 : ℕ)^69*100000000000000^53 ≤ 31516894929031^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119297987 10000000000 31516894929031 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4164095373/10000000000 : ℝ)^69 ≤ (1278553701993/4000000000000 : ℝ)^53 := by
    have hnat : (4164095373 : ℕ)^69*4000000000000^53 ≤ 1278553701993^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164095373 10000000000 1278553701993 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115320411/250000000 : ℝ)^69 ≤ (114122695361/312500000000 : ℝ)^53 := by
    have hnat : (115320411 : ℕ)^69*312500000000^53 ≤ 114122695361^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115320411 250000000 114122695361 312500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119297987/10000000000 : ℝ), (4164095373/10000000000 : ℝ), (-115320411/250000000 : ℝ)] ![(31516894929031/100000000000000 : ℝ), (1278553701993/4000000000000 : ℝ), (114122695361/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119297987/10000000000 : ℝ)|^69 ≤ (31516894929031/100000000000000 : ℝ)^53
        have hw : |(4119297987/10000000000 : ℝ)|=(4119297987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4164095373/10000000000 : ℝ)|^69 ≤ (1278553701993/4000000000000 : ℝ)^53
        have hw : |(4164095373/10000000000 : ℝ)|=(4164095373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115320411/250000000 : ℝ)|^69 ≤ (114122695361/312500000000 : ℝ)^53
        have hw : |(-115320411/250000000 : ℝ)|=(115320411/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (361720519/625000000 : ℝ)*x 0 + (-414629861/1250000000 : ℝ)*x 1 + (146979261/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361720519/625000000 : ℝ)^69 ≤ (49067388037559/100000000000000 : ℝ)^53 := by
    have hnat : (361720519 : ℕ)^69*100000000000000^53 ≤ 49067388037559^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361720519 625000000 49067388037559 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414629861/1250000000 : ℝ)^69 ≤ (23772315627567/100000000000000 : ℝ)^53 := by
    have hnat : (414629861 : ℕ)^69*100000000000000^53 ≤ 23772315627567^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414629861 1250000000 23772315627567 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146979261/400000000 : ℝ)^69 ≤ (13580148159287/50000000000000 : ℝ)^53 := by
    have hnat : (146979261 : ℕ)^69*50000000000000^53 ≤ 13580148159287^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146979261 400000000 13580148159287 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(361720519/625000000 : ℝ), (-414629861/1250000000 : ℝ), (146979261/400000000 : ℝ)] ![(49067388037559/100000000000000 : ℝ), (23772315627567/100000000000000 : ℝ), (13580148159287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(361720519/625000000 : ℝ)|^69 ≤ (49067388037559/100000000000000 : ℝ)^53
        have hw : |(361720519/625000000 : ℝ)|=(361720519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414629861/1250000000 : ℝ)|^69 ≤ (23772315627567/100000000000000 : ℝ)^53
        have hw : |(-414629861/1250000000 : ℝ)|=(414629861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146979261/400000000 : ℝ)|^69 ≤ (13580148159287/50000000000000 : ℝ)^53
        have hw : |(146979261/400000000 : ℝ)|=(146979261/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_19 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (480536221/500000000 : ℝ)*x 0 + (-69012573/1250000000 : ℝ)*x 1 + (-157527023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480536221/500000000 : ℝ)^69 ≤ (18992425072671/20000000000000 : ℝ)^53 := by
    have hnat : (480536221 : ℕ)^69*20000000000000^53 ≤ 18992425072671^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480536221 500000000 18992425072671 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69012573/1250000000 : ℝ)^69 ≤ (1151383820257/50000000000000 : ℝ)^53 := by
    have hnat : (69012573 : ℕ)^69*50000000000000^53 ≤ 1151383820257^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69012573 1250000000 1151383820257 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157527023/2500000000 : ℝ)^69 ≤ (2735106990103/100000000000000 : ℝ)^53 := by
    have hnat : (157527023 : ℕ)^69*100000000000000^53 ≤ 2735106990103^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157527023 2500000000 2735106990103 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(480536221/500000000 : ℝ), (-69012573/1250000000 : ℝ), (-157527023/2500000000 : ℝ)] ![(18992425072671/20000000000000 : ℝ), (1151383820257/50000000000000 : ℝ), (2735106990103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(480536221/500000000 : ℝ)|^69 ≤ (18992425072671/20000000000000 : ℝ)^53
        have hw : |(480536221/500000000 : ℝ)|=(480536221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69012573/1250000000 : ℝ)|^69 ≤ (1151383820257/50000000000000 : ℝ)^53
        have hw : |(-69012573/1250000000 : ℝ)|=(69012573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157527023/2500000000 : ℝ)|^69 ≤ (2735106990103/100000000000000 : ℝ)^53
        have hw : |(-157527023/2500000000 : ℝ)|=(157527023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-139994959/5000000000 : ℝ)*x 0 + (-6209416191/10000000000 : ℝ)*x 1 + (-5440686087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139994959/5000000000 : ℝ)^69 ≤ (951382571701/100000000000000 : ℝ)^53 := by
    have hnat : (139994959 : ℕ)^69*100000000000000^53 ≤ 951382571701^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139994959 5000000000 951382571701 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6209416191/10000000000 : ℝ)^69 ≤ (53774394685891/100000000000000 : ℝ)^53 := by
    have hnat : (6209416191 : ℕ)^69*100000000000000^53 ≤ 53774394685891^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6209416191 10000000000 53774394685891 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440686087/10000000000 : ℝ)^69 ≤ (2829638920481/6250000000000 : ℝ)^53 := by
    have hnat : (5440686087 : ℕ)^69*6250000000000^53 ≤ 2829638920481^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440686087 10000000000 2829638920481 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-139994959/5000000000 : ℝ), (-6209416191/10000000000 : ℝ), (-5440686087/10000000000 : ℝ)] ![(951382571701/100000000000000 : ℝ), (53774394685891/100000000000000 : ℝ), (2829638920481/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-139994959/5000000000 : ℝ)|^69 ≤ (951382571701/100000000000000 : ℝ)^53
        have hw : |(-139994959/5000000000 : ℝ)|=(139994959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6209416191/10000000000 : ℝ)|^69 ≤ (53774394685891/100000000000000 : ℝ)^53
        have hw : |(-6209416191/10000000000 : ℝ)|=(6209416191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5440686087/10000000000 : ℝ)|^69 ≤ (2829638920481/6250000000000 : ℝ)^53
        have hw : |(-5440686087/10000000000 : ℝ)|=(5440686087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (723441227/1250000000 : ℝ)*x 0 + (1837240189/5000000000 : ℝ)*x 1 + (-1658519141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (723441227/1250000000 : ℝ)^69 ≤ (49067404726349/100000000000000 : ℝ)^53 := by
    have hnat : (723441227 : ℕ)^69*100000000000000^53 ≤ 49067404726349^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723441227 1250000000 49067404726349 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1837240189/5000000000 : ℝ)^69 ≤ (6790071320241/25000000000000 : ℝ)^53 := by
    have hnat : (1837240189 : ℕ)^69*25000000000000^53 ≤ 6790071320241^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837240189 5000000000 6790071320241 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1658519141/5000000000 : ℝ)^69 ≤ (1485769373339/6250000000000 : ℝ)^53 := by
    have hnat : (1658519141 : ℕ)^69*6250000000000^53 ≤ 1485769373339^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658519141 5000000000 1485769373339 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(723441227/1250000000 : ℝ), (1837240189/5000000000 : ℝ), (-1658519141/5000000000 : ℝ)] ![(49067404726349/100000000000000 : ℝ), (6790071320241/25000000000000 : ℝ), (1485769373339/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(723441227/1250000000 : ℝ)|^69 ≤ (49067404726349/100000000000000 : ℝ)^53
        have hw : |(723441227/1250000000 : ℝ)|=(723441227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1837240189/5000000000 : ℝ)|^69 ≤ (6790071320241/25000000000000 : ℝ)^53
        have hw : |(1837240189/5000000000 : ℝ)|=(1837240189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1658519141/5000000000 : ℝ)|^69 ≤ (1485769373339/6250000000000 : ℝ)^53
        have hw : |(-1658519141/5000000000 : ℝ)|=(1658519141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4119298777/10000000000 : ℝ)*x 0 + (-2306407877/5000000000 : ℝ)*x 1 + (1041023823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119298777/10000000000 : ℝ)^69 ≤ (31516902798049/100000000000000 : ℝ)^53 := by
    have hnat : (4119298777 : ℕ)^69*100000000000000^53 ≤ 31516902798049^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119298777 10000000000 31516902798049 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2306407877/5000000000 : ℝ)^69 ≤ (36519255444971/100000000000000 : ℝ)^53 := by
    have hnat : (2306407877 : ℕ)^69*100000000000000^53 ≤ 36519255444971^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306407877 5000000000 36519255444971 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041023823/2500000000 : ℝ)^69 ≤ (31963841740363/100000000000000 : ℝ)^53 := by
    have hnat : (1041023823 : ℕ)^69*100000000000000^53 ≤ 31963841740363^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041023823 2500000000 31963841740363 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119298777/10000000000 : ℝ), (-2306407877/5000000000 : ℝ), (1041023823/2500000000 : ℝ)] ![(31516902798049/100000000000000 : ℝ), (36519255444971/100000000000000 : ℝ), (31963841740363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119298777/10000000000 : ℝ)|^69 ≤ (31516902798049/100000000000000 : ℝ)^53
        have hw : |(4119298777/10000000000 : ℝ)|=(4119298777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2306407877/5000000000 : ℝ)|^69 ≤ (36519255444971/100000000000000 : ℝ)^53
        have hw : |(-2306407877/5000000000 : ℝ)|=(2306407877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041023823/2500000000 : ℝ)|^69 ≤ (31963841740363/100000000000000 : ℝ)^53
        have hw : |(1041023823/2500000000 : ℝ)|=(1041023823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s0_25 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (192214497/200000000 : ℝ)*x 0 + (-315053863/5000000000 : ℝ)*x 1 + (-110419989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192214497/200000000 : ℝ)^69 ≤ (47481065447383/50000000000000 : ℝ)^53 := by
    have hnat : (192214497 : ℕ)^69*50000000000000^53 ≤ 47481065447383^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192214497 200000000 47481065447383 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315053863/5000000000 : ℝ)^69 ≤ (2735104921803/100000000000000 : ℝ)^53 := by
    have hnat : (315053863 : ℕ)^69*100000000000000^53 ≤ 2735104921803^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315053863 5000000000 2735104921803 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110419989/2000000000 : ℝ)^69 ≤ (2302764170703/100000000000000 : ℝ)^53 := by
    have hnat : (110419989 : ℕ)^69*100000000000000^53 ≤ 2302764170703^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110419989 2000000000 2302764170703 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(192214497/200000000 : ℝ), (-315053863/5000000000 : ℝ), (-110419989/2000000000 : ℝ)] ![(47481065447383/50000000000000 : ℝ), (2735104921803/100000000000000 : ℝ), (2302764170703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(192214497/200000000 : ℝ)|^69 ≤ (47481065447383/50000000000000 : ℝ)^53
        have hw : |(192214497/200000000 : ℝ)|=(192214497/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-315053863/5000000000 : ℝ)|^69 ≤ (2735104921803/100000000000000 : ℝ)^53
        have hw : |(-315053863/5000000000 : ℝ)|=(315053863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110419989/2000000000 : ℝ)|^69 ≤ (2302764170703/100000000000000 : ℝ)^53
        have hw : |(-110419989/2000000000 : ℝ)|=(110419989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s1_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2702249059/10000000000 : ℝ)*x 0 + (-2516005003/5000000000 : ℝ)*x 1 + (-2516005003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702249059/10000000000 : ℝ)^69 ≤ (4551041323913/25000000000000 : ℝ)^53 := by
    have hnat : (2702249059 : ℕ)^69*25000000000000^53 ≤ 4551041323913^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702249059 10000000000 4551041323913 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516005003/5000000000 : ℝ)^69 ≤ (40897917349571/100000000000000 : ℝ)^53 := by
    have hnat : (2516005003 : ℕ)^69*100000000000000^53 ≤ 40897917349571^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516005003 5000000000 40897917349571 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2516005003/5000000000 : ℝ)^69 ≤ (40897917349571/100000000000000 : ℝ)^53 := by
    have hnat : (2516005003 : ℕ)^69*100000000000000^53 ≤ 40897917349571^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516005003 5000000000 40897917349571 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2702249059/10000000000 : ℝ), (-2516005003/5000000000 : ℝ), (-2516005003/5000000000 : ℝ)] ![(4551041323913/25000000000000 : ℝ), (40897917349571/100000000000000 : ℝ), (40897917349571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2702249059/10000000000 : ℝ)|^69 ≤ (4551041323913/25000000000000 : ℝ)^53
        have hw : |(-2702249059/10000000000 : ℝ)|=(2702249059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2516005003/5000000000 : ℝ)|^69 ≤ (40897917349571/100000000000000 : ℝ)^53
        have hw : |(-2516005003/5000000000 : ℝ)|=(2516005003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2516005003/5000000000 : ℝ)|^69 ≤ (40897917349571/100000000000000 : ℝ)^53
        have hw : |(-2516005003/5000000000 : ℝ)|=(2516005003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s1_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2286690597/5000000000 : ℝ)*x 0 + (2081021501/5000000000 : ℝ)*x 1 + (-2081021501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2286690597/5000000000 : ℝ)^69 ≤ (18056666002571/50000000000000 : ℝ)^53 := by
    have hnat : (2286690597 : ℕ)^69*50000000000000^53 ≤ 18056666002571^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286690597 5000000000 18056666002571 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081021501/5000000000 : ℝ)^69 ≤ (1996458374591/6250000000000 : ℝ)^53 := by
    have hnat : (2081021501 : ℕ)^69*6250000000000^53 ≤ 1996458374591^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081021501 5000000000 1996458374591 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081021501/5000000000 : ℝ)^69 ≤ (1996458374591/6250000000000 : ℝ)^53 := by
    have hnat : (2081021501 : ℕ)^69*6250000000000^53 ≤ 1996458374591^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081021501 5000000000 1996458374591 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2286690597/5000000000 : ℝ), (2081021501/5000000000 : ℝ), (-2081021501/5000000000 : ℝ)] ![(18056666002571/50000000000000 : ℝ), (1996458374591/6250000000000 : ℝ), (1996458374591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2286690597/5000000000 : ℝ)|^69 ≤ (18056666002571/50000000000000 : ℝ)^53
        have hw : |(2286690597/5000000000 : ℝ)|=(2286690597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2081021501/5000000000 : ℝ)|^69 ≤ (1996458374591/6250000000000 : ℝ)^53
        have hw : |(2081021501/5000000000 : ℝ)|=(2081021501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081021501/5000000000 : ℝ)|^69 ≤ (1996458374591/6250000000000 : ℝ)^53
        have hw : |(-2081021501/5000000000 : ℝ)|=(2081021501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2286690597/5000000000 : ℝ)*x 0 + (-2081021501/5000000000 : ℝ)*x 1 + (2081021501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2286690597/5000000000 : ℝ)^69 ≤ (18056666002571/50000000000000 : ℝ)^53 := by
    have hnat : (2286690597 : ℕ)^69*50000000000000^53 ≤ 18056666002571^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286690597 5000000000 18056666002571 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081021501/5000000000 : ℝ)^69 ≤ (1996458374591/6250000000000 : ℝ)^53 := by
    have hnat : (2081021501 : ℕ)^69*6250000000000^53 ≤ 1996458374591^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081021501 5000000000 1996458374591 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081021501/5000000000 : ℝ)^69 ≤ (1996458374591/6250000000000 : ℝ)^53 := by
    have hnat : (2081021501 : ℕ)^69*6250000000000^53 ≤ 1996458374591^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081021501 5000000000 1996458374591 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2286690597/5000000000 : ℝ), (-2081021501/5000000000 : ℝ), (2081021501/5000000000 : ℝ)] ![(18056666002571/50000000000000 : ℝ), (1996458374591/6250000000000 : ℝ), (1996458374591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2286690597/5000000000 : ℝ)|^69 ≤ (18056666002571/50000000000000 : ℝ)^53
        have hw : |(2286690597/5000000000 : ℝ)|=(2286690597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2081021501/5000000000 : ℝ)|^69 ≤ (1996458374591/6250000000000 : ℝ)^53
        have hw : |(-2081021501/5000000000 : ℝ)|=(2081021501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081021501/5000000000 : ℝ)|^69 ≤ (1996458374591/6250000000000 : ℝ)^53
        have hw : |(2081021501/5000000000 : ℝ)|=(2081021501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306046_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6306705129/10000000000 : ℝ)*x 0 + (-1593326603/5000000000 : ℝ)*x 1 + (-1593326603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6306705129/10000000000 : ℝ)^69 ≤ (54873865275741/100000000000000 : ℝ)^53 := by
    have hnat : (6306705129 : ℕ)^69*100000000000000^53 ≤ 54873865275741^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6306705129 10000000000 54873865275741 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1593326603/5000000000 : ℝ)^69 ≤ (5640766838647/25000000000000 : ℝ)^53 := by
    have hnat : (1593326603 : ℕ)^69*25000000000000^53 ≤ 5640766838647^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593326603 5000000000 5640766838647 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593326603/5000000000 : ℝ)^69 ≤ (5640766838647/25000000000000 : ℝ)^53 := by
    have hnat : (1593326603 : ℕ)^69*25000000000000^53 ≤ 5640766838647^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593326603 5000000000 5640766838647 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6306705129/10000000000 : ℝ), (-1593326603/5000000000 : ℝ), (-1593326603/5000000000 : ℝ)] ![(54873865275741/100000000000000 : ℝ), (5640766838647/25000000000000 : ℝ), (5640766838647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6306705129/10000000000 : ℝ)|^69 ≤ (54873865275741/100000000000000 : ℝ)^53
        have hw : |(6306705129/10000000000 : ℝ)|=(6306705129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1593326603/5000000000 : ℝ)|^69 ≤ (5640766838647/25000000000000 : ℝ)^53
        have hw : |(-1593326603/5000000000 : ℝ)|=(1593326603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1593326603/5000000000 : ℝ)|^69 ≤ (5640766838647/25000000000000 : ℝ)^53
        have hw : |(-1593326603/5000000000 : ℝ)|=(1593326603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306046 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-64105973/500000000 : ℝ)*X 0 0+(-2779115763/5000000000 : ℝ)*X 0 1+(-1389557881/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((941851927/2000000000 : ℝ)*X 2 0+(-2045825637/5000000000 : ℝ)*X 2 1+(163666051/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-628259303/5000000000 : ℝ)*X 0 0+(-2995486223/5000000000 : ℝ)*X 0 1+(-40092643/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((897379783/2000000000 : ℝ)*X 1 0+(5105599433/10000000000 : ℝ)*X 1 1+(-811047659/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4486898997/10000000000 : ℝ)*X 2 0+(-636339761/2000000000 : ℝ)*X 2 1+(2579925003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((8169410559/10000000000 : ℝ)*X 0 0+(-4341131/40000000 : ℝ)*X 0 1+(-2632175927/10000000000 : ℝ)*X 0 2+(8169410559/10000000000 : ℝ)*X 1 0+(-4341131/40000000 : ℝ)*X 1 1+(-2632175927/10000000000 : ℝ)*X 1 2+(8169410559/10000000000 : ℝ)*X 2 0+(-4341131/40000000 : ℝ)*X 2 1+(-2632175927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-279988723/10000000000 : ℝ)*X 0 0+(-5440688011/10000000000 : ℝ)*X 0 1+(-6209414811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4119297987/10000000000 : ℝ)*X 1 0+(4164095373/10000000000 : ℝ)*X 1 1+(-115320411/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((361720519/625000000 : ℝ)*X 2 0+(-414629861/1250000000 : ℝ)*X 2 1+(146979261/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((480536221/500000000 : ℝ)*X 0 0+(-69012573/1250000000 : ℝ)*X 0 1+(-157527023/2500000000 : ℝ)*X 0 2+(480536221/500000000 : ℝ)*X 1 0+(-69012573/1250000000 : ℝ)*X 1 1+(-157527023/2500000000 : ℝ)*X 1 2+(480536221/500000000 : ℝ)*X 2 0+(-69012573/1250000000 : ℝ)*X 2 1+(-157527023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-139994959/5000000000 : ℝ)*X 0 0+(-6209416191/10000000000 : ℝ)*X 0 1+(-5440686087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((723441227/1250000000 : ℝ)*X 1 0+(1837240189/5000000000 : ℝ)*X 1 1+(-1658519141/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4119298777/10000000000 : ℝ)*X 2 0+(-2306407877/5000000000 : ℝ)*X 2 1+(1041023823/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((192214497/200000000 : ℝ)*X 0 0+(-315053863/5000000000 : ℝ)*X 0 1+(-110419989/2000000000 : ℝ)*X 0 2+(192214497/200000000 : ℝ)*X 1 0+(-315053863/5000000000 : ℝ)*X 1 1+(-110419989/2000000000 : ℝ)*X 1 2+(192214497/200000000 : ℝ)*X 2 0+(-315053863/5000000000 : ℝ)*X 2 1+(-110419989/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2741/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2741/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2160753702058020908559/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (737229/250000000000 : ℝ)*(base1) + (37711/62500000000 : ℝ)*(base3) + (169507261823/200000000000 : ℝ)*(base39) + (246819399/5000000000 : ℝ)*(base49) + (125153005459/40000000000 : ℝ)*(major_s0_0) + (125153005459/40000000000 : ℝ)*(major_s0_1) + (125153005459/40000000000 : ℝ)*(major_s0_2) + (4228366186227/1000000000000 : ℝ)*(sp_s0_7) + (2114160710623/500000000000 : ℝ)*(sp_s0_8) + (2114163619637/500000000000 : ℝ)*(sp_s0_9) + (405850032991/200000000000 : ℝ)*(sp_s0_13) + (18034143/250000000000 : ℝ)*(sp_s0_15) + (2971713/100000000000 : ℝ)*(sp_s0_20) + (2053599/31250000000 : ℝ)*(sp_s0_22) + (2029253717247/1000000000000 : ℝ)*(f.failure) + (4228392954441/1000000000000 : ℝ)*(f.sum) + (9362537536423/40000000000000000000000000 : ℝ)*base63 + (7200098064379/100000000000000000000000000 : ℝ)*base64 + (3628015254379/100000000000000000000000000 : ℝ)*base66 + (10661929316423/80000000000000000000000000 : ℝ)*base69 + (40370723555401/400000000000000000000000000 : ℝ)*base70 + (17917452925621/100000000000000000000000000 : ℝ)*base73 + (2924703163577/80000000000000000000000000 : ℝ)*base74 + (20348641244423/80000000000000000000000000 : ℝ)*base77 + (4018323359379/50000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (27029/50000000000000000 : ℝ)*base86 + (27029/50000000000000000 : ℝ)*base88 + (27029/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1933/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1933/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5247935787014490377547/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10262791/1000000000000 : ℝ)*(base12) + (71541035479/250000000000 : ℝ)*(base39) + (454829/200000000000 : ℝ)*(base59) + (626731685841/62500000000 : ℝ)*(major_s0_0) + (2217791804927/500000000000 : ℝ)*(major_s0_1) + (2217791804927/500000000000 : ℝ)*(major_s0_2) + (40624377/1000000000000 : ℝ)*(sp_s0_0) + (5592123363601/1000000000000 : ℝ)*(sp_s0_3) + (12800081/1000000000000 : ℝ)*(sp_s0_9) + (187323136927/31250000000 : ℝ)*(sp_s0_14) + (5994386114593/1000000000000 : ℝ)*(sp_s0_15) + (374648654297/62500000000 : ℝ)*(sp_s0_16) + (2876774551421/1000000000000 : ℝ)*(sp_s0_19) + (5154239/1000000000000 : ℝ)*(sp_s0_21) + (2876774551421/1000000000000 : ℝ)*(f.failure) + (187324727151/31250000000 : ℝ)*(f.sum) + (42260943719619/500000000000000000000000000 : ℝ)*base63 + (87658459434313/1250000000000000000000000000 : ℝ)*base65 + (266935373684313/1250000000000000000000000000 : ℝ)*base67 + (979086896619619/1000000000000000000000000000 : ℝ)*base69 + (151112442086083/1250000000000000000000000000 : ℝ)*base71 + (108872874655329/156250000000000000000000000 : ℝ)*base73 + (439840791619619/1000000000000000000000000000 : ℝ)*base75 + (84510410540177/125000000000000000000000000 : ℝ)*base77 + (22802964485389/250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (50847/50000000000000000 : ℝ)*base86 + (847/50000000000000000 : ℝ)*base88 + (847/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1933/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1933/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (501301218659341826553/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3826449/1000000000000 : ℝ)*(base10) + (406324326159/500000000000 : ℝ)*(base39) + (924877/500000000000 : ℝ)*(base49) + (8272693615021/1000000000000 : ℝ)*(major_s0_0) + (4435583995649/1000000000000 : ℝ)*(major_s0_1) + (4435583995649/1000000000000 : ℝ)*(major_s0_2) + (3173513/500000000000 : ℝ)*(sp_s0_2) + (3837109619371/1000000000000 : ℝ)*(sp_s0_3) + (6948769/200000000000 : ℝ)*(sp_s0_7) + (20180083/1000000000000 : ℝ)*(sp_s0_8) + (149858823709/25000000000 : ℝ)*(sp_s0_20) + (5994371338571/1000000000000 : ℝ)*(sp_s0_21) + (1498596292907/250000000000 : ℝ)*(sp_s0_22) + (575354960327/200000000000 : ℝ)*(sp_s0_25) + (575354960327/200000000000 : ℝ)*(f.failure) + (2997195759327/500000000000 : ℝ)*(f.sum) + (80996491905853/1000000000000000000000000000 : ℝ)*base63 + (760460191608231/2500000000000000000000000000 : ℝ)*base65 + (1675983350358231/2500000000000000000000000000 : ℝ)*base67 + (1541243485705853/2000000000000000000000000000 : ℝ)*base69 + (755067917136391/10000000000000000000000000000 : ℝ)*base70 + (741302437891499/2500000000000000000000000000 : ℝ)*base73 + (1643453168705853/2000000000000000000000000000 : ℝ)*base75 + (695201273886137/2000000000000000000000000000 : ℝ)*base77 + (68937888549973/250000000000000000000000000 : ℝ)*base79 + (10589/10000000000000000 : ℝ)*base86 + (589/10000000000000000 : ℝ)*base88 + (589/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (2741/20000 : ℝ) ^ (67/16 : ℝ) ≤ (3038022545506037/12500000000000000000 : ℝ) := by
    have hpowers : (2741/20000 : ℝ)^67 ≤ (3038022545506037/12500000000000000000 : ℝ)^16 := by
      have hnat : (2741 : ℕ)^67*12500000000000000000^16 ≤ 3038022545506037^16*20000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2741 20000 3038022545506037 12500000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2741/20000 : ℝ)) (X := (3038022545506037/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12503038022545506037/12500000000000000000 : ℝ) ≤ (10000580344657293/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (12503038022545506037/12500000000000000000 : ℝ)^16 ≤ (10000580344657293/10000000000000000 : ℝ)^67 := by
      have hnat : (12503038022545506037 : ℕ)^16*10000000000000000^67 ≤ 10000580344657293^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503038022545506037 12500000000000000000 10000580344657293 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000580344657293/10000000000000000 : ℝ)) (X := (12503038022545506037/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6253038022545506037/6250000000000000000 : ℝ) ≤ (5000580290992847/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (6253038022545506037/6250000000000000000 : ℝ)^16 ≤ (5000580290992847/5000000000000000 : ℝ)^67 := by
      have hnat : (6253038022545506037 : ℕ)^16*5000000000000000^67 ≤ 5000580290992847^67*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253038022545506037 6250000000000000000 5000580290992847 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000580290992847/5000000000000000 : ℝ)) (X := (6253038022545506037/6250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(580344657293/1370500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(580237328401/1370500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (2741/20000 : ℝ)) (alpha := (580344657293/1370500000000000 : ℝ)) (beta := (580237328401/1370500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2741/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(580344657293/1370500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(580237328401/1370500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1933/4000 : ℝ) ^ (67/16 : ℝ) ≤ (475849563272434233/10000000000000000000 : ℝ) := by
    have hpowers : (1933/4000 : ℝ)^67 ≤ (475849563272434233/10000000000000000000 : ℝ)^16 := by
      have hnat : (1933 : ℕ)^67*10000000000000000000^16 ≤ 475849563272434233^16*4000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1933 4000 475849563272434233 10000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1933/4000 : ℝ)) (X := (475849563272434233/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10475849563272434233/10000000000000000000 : ℝ) ≤ (157994271304917/156250000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (10475849563272434233/10000000000000000000 : ℝ)^16 ≤ (157994271304917/156250000000000 : ℝ)^67 := by
      have hnat : (10475849563272434233 : ℕ)^16*156250000000000^67 ≤ 157994271304917^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10475849563272434233 10000000000000000000 157994271304917 156250000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157994271304917/156250000000000 : ℝ)) (X := (10475849563272434233/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5475849563272434233/5000000000000000000 : ℝ) ≤ (10219471077177329/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (5475849563272434233/5000000000000000000 : ℝ)^16 ≤ (10219471077177329/10000000000000000 : ℝ)^67 := by
      have hnat : (5475849563272434233 : ℕ)^16*10000000000000000^67 ≤ 10219471077177329^67*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5475849563272434233 5000000000000000000 10219471077177329 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10219471077177329/10000000000000000 : ℝ)) (X := (5475849563272434233/5000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1744271304917/75507812500000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(107837713662641/4832500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1933/4000 : ℝ)) (alpha := (1744271304917/75507812500000 : ℝ)) (beta := (107837713662641/4832500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1933/4000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1744271304917/75507812500000 : ℝ)*((1 : ℝ)*pair X 1 0)+(107837713662641/4832500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1933/4000 : ℝ) ^ (67/16 : ℝ) ≤ (475849563272434233/10000000000000000000 : ℝ) := by
    have hpowers : (1933/4000 : ℝ)^67 ≤ (475849563272434233/10000000000000000000 : ℝ)^16 := by
      have hnat : (1933 : ℕ)^67*10000000000000000000^16 ≤ 475849563272434233^16*4000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1933 4000 475849563272434233 10000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1933/4000 : ℝ)) (X := (475849563272434233/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10475849563272434233/10000000000000000000 : ℝ) ≤ (157994271304917/156250000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (10475849563272434233/10000000000000000000 : ℝ)^16 ≤ (157994271304917/156250000000000 : ℝ)^67 := by
      have hnat : (10475849563272434233 : ℕ)^16*156250000000000^67 ≤ 157994271304917^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10475849563272434233 10000000000000000000 157994271304917 156250000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157994271304917/156250000000000 : ℝ)) (X := (10475849563272434233/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5475849563272434233/5000000000000000000 : ℝ) ≤ (10219471077177329/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (5475849563272434233/5000000000000000000 : ℝ)^16 ≤ (10219471077177329/10000000000000000 : ℝ)^67 := by
      have hnat : (5475849563272434233 : ℕ)^16*10000000000000000^67 ≤ 10219471077177329^67*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5475849563272434233 5000000000000000000 10219471077177329 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10219471077177329/10000000000000000 : ℝ)) (X := (5475849563272434233/5000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1744271304917/75507812500000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(107837713662641/4832500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1933/4000 : ℝ)) (alpha := (1744271304917/75507812500000 : ℝ)) (beta := (107837713662641/4832500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1933/4000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1744271304917/75507812500000 : ℝ)*((1 : ℝ)*pair X 2 0)+(107837713662641/4832500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2702249059/10000000000 : ℝ)*X 0 0+(-2516005003/5000000000 : ℝ)*X 0 1+(-2516005003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2286690597/5000000000 : ℝ)*X 1 0+(2081021501/5000000000 : ℝ)*X 1 1+(-2081021501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2286690597/5000000000 : ℝ)*X 2 0+(-2081021501/5000000000 : ℝ)*X 2 1+(2081021501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6306705129/10000000000 : ℝ)*X 0 0+(-1593326603/5000000000 : ℝ)*X 0 1+(-1593326603/5000000000 : ℝ)*X 0 2+(6306705129/10000000000 : ℝ)*X 1 0+(-1593326603/5000000000 : ℝ)*X 1 1+(-1593326603/5000000000 : ℝ)*X 1 2+(6306705129/10000000000 : ℝ)*X 2 0+(-1593326603/5000000000 : ℝ)*X 2 1+(-1593326603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306046_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-156279/25000 : ℝ) < ((-77093/50000 : ℝ)*P 0+(-77093/50000 : ℝ)*P 1+(-77093/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-156279/25000 : ℝ) < (-120054184976870737936202391/19330000000000000000000000 : ℝ) := by norm_num
    linear_combination (4903/1000000000000 : ℝ)*(base10) + (721784206447/1000000000000 : ℝ)*(base39) + (90223010997/250000000000 : ℝ)*(base40) + (147032698291/1000000000000 : ℝ)*(base49) + (1523/250000000000 : ℝ)*(base53) + (73516346807/500000000000 : ℝ)*(base59) + (77093/50000 : ℝ)*(major_s1_0) + (77093/50000 : ℝ)*(major_s1_1) + (385464998477/250000000000 : ℝ)*(major_s1_2) + (2070256658221/1000000000000 : ℝ)*(sp_s1_0) + (2070256658401/1000000000000 : ℝ)*(sp_s1_1) + (2070256664493/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2070256664493/1000000000000 : ℝ)*(f.sum) + (6391849692687316273/2416250000000000000000000000 : ℝ)*base62 + (386183398242407467/302031250000000000000000000 : ℝ)*base64 + (45650915959508579/9665000000000000000000000 : ℝ)*base67 + (248148389330051/1208125000000000000000000000 : ℝ)*base69 + (55393647786846289/413933828125000000000000000000 : ℝ)*base71 + (107138808641/13705000000000000000000000 : ℝ)*base73 + (25565567364836493/9665000000000000000000000 : ℝ)*base74 + (17525298710595187/13705000000000000000000000 : ℝ)*base76 + (4307392992983529/26491765000000000000000000000 : ℝ)*base78 + (4723/1000000000000 : ℝ)*base81 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem rawFrame_weaken_k {p k k' A : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (hX : RawFrame p k A X) (hk : k' ≤ k) : RawFrame p k' A X := by
  have f := raw_linear_data hp X hX
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  refine ⟨hX.sum,hX.row_total,hX.total_one,hX.total_cap,?_⟩
  have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
  linarith only [hh,hX.linear_failure]
theorem orderedChart_weaken {p k k' A A' d d' : ℝ}
    {X : Fin 3 → Fin 3 → ℝ} {orders : Fin 3 → Fin 3 → Fin 3}
    {signs : Fin 3 → Fin 3 → Bool} (hp : 1 ≤ p)
    (hX : OrderedChart p k A d X orders signs)
    (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    OrderedChart p k' A' d' X orders signs := by
  have hr := rawFrame_weaken_k hp hX.raw hk
  refine ⟨⟨hr.sum,hr.row_total,hr.total_one,hr.total_cap.trans hA,hr.linear_failure⟩,
    hX.permutation,?_,hX.ordered⟩
  intro i
  exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (hX.main i)
end HlawkaSchatten.DiagonalCutoff4

namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p006_b025 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=46 ∨ c=47 ∨ c=48 ∨ c=49 ∨ c=50 ∨ c=51 ∨ c=52 ∨ c=53 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c306046 p hpa (by linarith only [hpb]) X hX
  · exact collision_c304047 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c304048 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c304049 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c304050 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c304051 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c304052 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c306053 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p006_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

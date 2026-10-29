-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p006_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:55:48.311317+00:00
-- url     : https://prove2.me/submissions/e59083c9-4402-488b-87ce-85a143754db7

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306080_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306080_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306080_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306080_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c306080 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c306080_s0 p hpa hpb X hX
  have h1 := collision_c306080_s1 p hpa hpb X hX h0
  have h2 := collision_c306080_s2 p hpa hpb X hX h1
  exact collision_c306080_s3 p hpa hpb X hX h2

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
theorem collision_support_c306079_s0_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4060256199/5000000000 : ℝ)*x 0 + (-1537344571/10000000000 : ℝ)*x 1 + (-1193087487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4060256199/5000000000 : ℝ)^135 ≤ (380594803587/500000000000 : ℝ)^103 := by
    have hnat : (4060256199 : ℕ)^135*500000000000^103 ≤ 380594803587^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060256199 5000000000 380594803587 500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537344571/10000000000 : ℝ)^135 ≤ (1074057740967/12500000000000 : ℝ)^103 := by
    have hnat : (1537344571 : ℕ)^135*12500000000000^103 ≤ 1074057740967^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537344571 10000000000 1074057740967 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193087487/5000000000 : ℝ)^135 ≤ (1911072167753/12500000000000 : ℝ)^103 := by
    have hnat : (1193087487 : ℕ)^135*12500000000000^103 ≤ 1911072167753^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193087487 5000000000 1911072167753 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4060256199/5000000000 : ℝ), (-1537344571/10000000000 : ℝ), (-1193087487/5000000000 : ℝ)] ![(380594803587/500000000000 : ℝ), (1074057740967/12500000000000 : ℝ), (1911072167753/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4060256199/5000000000 : ℝ)|^135 ≤ (380594803587/500000000000 : ℝ)^103
        have hw : |(4060256199/5000000000 : ℝ)|=(4060256199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1537344571/10000000000 : ℝ)|^135 ≤ (1074057740967/12500000000000 : ℝ)^103
        have hw : |(-1537344571/10000000000 : ℝ)|=(1537344571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1193087487/5000000000 : ℝ)|^135 ≤ (1911072167753/12500000000000 : ℝ)^103
        have hw : |(-1193087487/5000000000 : ℝ)|=(1193087487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (201994079/625000000 : ℝ)*x 0 + (1509360757/2500000000 : ℝ)*x 1 + (884833553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201994079/625000000 : ℝ)^135 ≤ (22753982361341/100000000000000 : ℝ)^103 := by
    have hnat : (201994079 : ℕ)^135*100000000000000^103 ≤ 22753982361341^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201994079 625000000 22753982361341 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1509360757/2500000000 : ℝ)^135 ≤ (51614123291647/100000000000000 : ℝ)^103 := by
    have hnat : (1509360757 : ℕ)^135*100000000000000^103 ≤ 51614123291647^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509360757 2500000000 51614123291647 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884833553/2500000000 : ℝ)^135 ≤ (2563189432613/10000000000000 : ℝ)^103 := by
    have hnat : (884833553 : ℕ)^135*10000000000000^103 ≤ 2563189432613^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884833553 2500000000 2563189432613 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(201994079/625000000 : ℝ), (1509360757/2500000000 : ℝ), (884833553/2500000000 : ℝ)] ![(22753982361341/100000000000000 : ℝ), (51614123291647/100000000000000 : ℝ), (2563189432613/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(201994079/625000000 : ℝ)|^135 ≤ (22753982361341/100000000000000 : ℝ)^103
        have hw : |(201994079/625000000 : ℝ)|=(201994079/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1509360757/2500000000 : ℝ)|^135 ≤ (51614123291647/100000000000000 : ℝ)^103
        have hw : |(1509360757/2500000000 : ℝ)|=(1509360757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884833553/2500000000 : ℝ)|^135 ≤ (2563189432613/10000000000000 : ℝ)^103
        have hw : |(884833553/2500000000 : ℝ)|=(884833553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-342015271/2000000000 : ℝ)*x 0 + (147442237/500000000 : ℝ)*x 1 + (-7612769601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342015271/2000000000 : ℝ)^135 ≤ (9879365571137/100000000000000 : ℝ)^103 := by
    have hnat : (342015271 : ℕ)^135*100000000000000^103 ≤ 9879365571137^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342015271 2000000000 9879365571137 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147442237/500000000 : ℝ)^135 ≤ (1008912660407/5000000000000 : ℝ)^103 := by
    have hnat : (147442237 : ℕ)^135*5000000000000^103 ≤ 1008912660407^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147442237 500000000 1008912660407 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7612769601/10000000000 : ℝ)^135 ≤ (13988476241223/20000000000000 : ℝ)^103 := by
    have hnat : (7612769601 : ℕ)^135*20000000000000^103 ≤ 13988476241223^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7612769601 10000000000 13988476241223 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-342015271/2000000000 : ℝ), (147442237/500000000 : ℝ), (-7612769601/10000000000 : ℝ)] ![(9879365571137/100000000000000 : ℝ), (1008912660407/5000000000000 : ℝ), (13988476241223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-342015271/2000000000 : ℝ)|^135 ≤ (9879365571137/100000000000000 : ℝ)^103
        have hw : |(-342015271/2000000000 : ℝ)|=(342015271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147442237/500000000 : ℝ)|^135 ≤ (1008912660407/5000000000000 : ℝ)^103
        have hw : |(147442237/500000000 : ℝ)|=(147442237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7612769601/10000000000 : ℝ)|^135 ≤ (13988476241223/20000000000000 : ℝ)^103
        have hw : |(-7612769601/10000000000 : ℝ)|=(7612769601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1614041481/2000000000 : ℝ)*x 0 + (-3014597/100000000 : ℝ)*x 1 + (-413823873/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1614041481/2000000000 : ℝ)^135 ≤ (3020060625559/4000000000000 : ℝ)^103 := by
    have hnat : (1614041481 : ℕ)^135*4000000000000^103 ≤ 3020060625559^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614041481 2000000000 3020060625559 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3014597/100000000 : ℝ)^135 ≤ (13000701/1280000000 : ℝ)^103 := by
    have hnat : (3014597 : ℕ)^135*1280000000^103 ≤ 13000701^103*100000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014597 100000000 13000701 1280000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413823873/1250000000 : ℝ)^135 ≤ (23482804571889/100000000000000 : ℝ)^103 := by
    have hnat : (413823873 : ℕ)^135*100000000000000^103 ≤ 23482804571889^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413823873 1250000000 23482804571889 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1614041481/2000000000 : ℝ), (-3014597/100000000 : ℝ), (-413823873/1250000000 : ℝ)] ![(3020060625559/4000000000000 : ℝ), (13000701/1280000000 : ℝ), (23482804571889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1614041481/2000000000 : ℝ)|^135 ≤ (3020060625559/4000000000000 : ℝ)^103
        have hw : |(1614041481/2000000000 : ℝ)|=(1614041481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3014597/100000000 : ℝ)|^135 ≤ (13000701/1280000000 : ℝ)^103
        have hw : |(-3014597/100000000 : ℝ)|=(3014597/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413823873/1250000000 : ℝ)|^135 ≤ (23482804571889/100000000000000 : ℝ)^103
        have hw : |(-413823873/1250000000 : ℝ)|=(413823873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (731264333/5000000000 : ℝ)*x 0 + (7904552749/10000000000 : ℝ)*x 1 + (11027711/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (731264333/5000000000 : ℝ)^135 ≤ (8048581431171/100000000000000 : ℝ)^103 := by
    have hnat : (731264333 : ℕ)^135*100000000000000^103 ≤ 8048581431171^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731264333 5000000000 8048581431171 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7904552749/10000000000 : ℝ)^135 ≤ (36738368511787/50000000000000 : ℝ)^103 := by
    have hnat : (7904552749 : ℕ)^135*50000000000000^103 ≤ 36738368511787^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7904552749 10000000000 36738368511787 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11027711/40000000 : ℝ)^135 ≤ (1847468153053/10000000000000 : ℝ)^103 := by
    have hnat : (11027711 : ℕ)^135*10000000000000^103 ≤ 1847468153053^103*40000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11027711 40000000 1847468153053 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(731264333/5000000000 : ℝ), (7904552749/10000000000 : ℝ), (11027711/40000000 : ℝ)] ![(8048581431171/100000000000000 : ℝ), (36738368511787/50000000000000 : ℝ), (1847468153053/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(731264333/5000000000 : ℝ)|^135 ≤ (8048581431171/100000000000000 : ℝ)^103
        have hw : |(731264333/5000000000 : ℝ)|=(731264333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7904552749/10000000000 : ℝ)|^135 ≤ (36738368511787/50000000000000 : ℝ)^103
        have hw : |(7904552749/10000000000 : ℝ)|=(7904552749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11027711/40000000 : ℝ)|^135 ≤ (1847468153053/10000000000000 : ℝ)^103
        have hw : |(11027711/40000000 : ℝ)|=(11027711/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1203213673/5000000000 : ℝ)*x 0 + (949200123/1250000000 : ℝ)*x 1 + (-466261727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1203213673/5000000000 : ℝ)^135 ≤ (15458874862801/100000000000000 : ℝ)^103 := by
    have hnat : (1203213673 : ℕ)^135*100000000000000^103 ≤ 15458874862801^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203213673 5000000000 15458874862801 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949200123/1250000000 : ℝ)^135 ≤ (17427911342573/25000000000000 : ℝ)^103 := by
    have hnat : (949200123 : ℕ)^135*25000000000000^103 ≤ 17427911342573^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949200123 1250000000 17427911342573 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466261727/2000000000 : ℝ)^135 ≤ (2965895948701/20000000000000 : ℝ)^103 := by
    have hnat : (466261727 : ℕ)^135*20000000000000^103 ≤ 2965895948701^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466261727 2000000000 2965895948701 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1203213673/5000000000 : ℝ), (949200123/1250000000 : ℝ), (-466261727/2000000000 : ℝ)] ![(15458874862801/100000000000000 : ℝ), (17427911342573/25000000000000 : ℝ), (2965895948701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1203213673/5000000000 : ℝ)|^135 ≤ (15458874862801/100000000000000 : ℝ)^103
        have hw : |(1203213673/5000000000 : ℝ)|=(1203213673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(949200123/1250000000 : ℝ)|^135 ≤ (17427911342573/25000000000000 : ℝ)^103
        have hw : |(949200123/1250000000 : ℝ)|=(949200123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-466261727/2000000000 : ℝ)|^135 ≤ (2965895948701/20000000000000 : ℝ)^103
        have hw : |(-466261727/2000000000 : ℝ)|=(466261727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-77607147/2500000000 : ℝ)*x 0 + (179529593/500000000 : ℝ)*x 1 + (-785100349/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77607147/2500000000 : ℝ)^135 ≤ (1055467728461/100000000000000 : ℝ)^103 := by
    have hnat : (77607147 : ℕ)^135*100000000000000^103 ≤ 1055467728461^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77607147 2500000000 1055467728461 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179529593/500000000 : ℝ)^135 ≤ (26119520544013/100000000000000 : ℝ)^103 := by
    have hnat : (179529593 : ℕ)^135*100000000000000^103 ≤ 26119520544013^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179529593 500000000 26119520544013 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (785100349/1000000000 : ℝ)^135 ≤ (36412505857859/50000000000000 : ℝ)^103 := by
    have hnat : (785100349 : ℕ)^135*50000000000000^103 ≤ 36412505857859^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785100349 1000000000 36412505857859 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77607147/2500000000 : ℝ), (179529593/500000000 : ℝ), (-785100349/1000000000 : ℝ)] ![(1055467728461/100000000000000 : ℝ), (26119520544013/100000000000000 : ℝ), (36412505857859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77607147/2500000000 : ℝ)|^135 ≤ (1055467728461/100000000000000 : ℝ)^103
        have hw : |(-77607147/2500000000 : ℝ)|=(77607147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179529593/500000000 : ℝ)|^135 ≤ (26119520544013/100000000000000 : ℝ)^103
        have hw : |(179529593/500000000 : ℝ)|=(179529593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-785100349/1000000000 : ℝ)|^135 ≤ (36412505857859/50000000000000 : ℝ)^103
        have hw : |(-785100349/1000000000 : ℝ)|=(785100349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2320943513/2500000000 : ℝ)*x 0 + (-298464767/2500000000 : ℝ)*x 1 + (-177116213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2320943513/2500000000 : ℝ)^135 ≤ (90718788444683/100000000000000 : ℝ)^103 := by
    have hnat : (2320943513 : ℕ)^135*100000000000000^103 ≤ 90718788444683^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320943513 2500000000 90718788444683 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298464767/2500000000 : ℝ)^135 ≤ (3084261570989/50000000000000 : ℝ)^103 := by
    have hnat : (298464767 : ℕ)^135*50000000000000^103 ≤ 3084261570989^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298464767 2500000000 3084261570989 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177116213/2500000000 : ℝ)^135 ≤ (3112688404801/100000000000000 : ℝ)^103 := by
    have hnat : (177116213 : ℕ)^135*100000000000000^103 ≤ 3112688404801^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177116213 2500000000 3112688404801 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2320943513/2500000000 : ℝ), (-298464767/2500000000 : ℝ), (-177116213/2500000000 : ℝ)] ![(90718788444683/100000000000000 : ℝ), (3084261570989/50000000000000 : ℝ), (3112688404801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2320943513/2500000000 : ℝ)|^135 ≤ (90718788444683/100000000000000 : ℝ)^103
        have hw : |(2320943513/2500000000 : ℝ)|=(2320943513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-298464767/2500000000 : ℝ)|^135 ≤ (3084261570989/50000000000000 : ℝ)^103
        have hw : |(-298464767/2500000000 : ℝ)|=(298464767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-177116213/2500000000 : ℝ)|^135 ≤ (3112688404801/100000000000000 : ℝ)^103
        have hw : |(-177116213/2500000000 : ℝ)|=(177116213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (122472401/312500000 : ℝ)*x 0 + (5872856279/10000000000 : ℝ)*x 1 + (3031942247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122472401/312500000 : ℝ)^135 ≤ (915482618621/3125000000000 : ℝ)^103 := by
    have hnat : (122472401 : ℕ)^135*3125000000000^103 ≤ 915482618621^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122472401 312500000 915482618621 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5872856279/10000000000 : ℝ)^135 ≤ (9955557418331/20000000000000 : ℝ)^103 := by
    have hnat : (5872856279 : ℕ)^135*20000000000000^103 ≤ 9955557418331^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5872856279 10000000000 9955557418331 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3031942247/10000000000 : ℝ)^135 ≤ (20926769107921/100000000000000 : ℝ)^103 := by
    have hnat : (3031942247 : ℕ)^135*100000000000000^103 ≤ 20926769107921^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031942247 10000000000 20926769107921 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(122472401/312500000 : ℝ), (5872856279/10000000000 : ℝ), (3031942247/10000000000 : ℝ)] ![(915482618621/3125000000000 : ℝ), (9955557418331/20000000000000 : ℝ), (20926769107921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(122472401/312500000 : ℝ)|^135 ≤ (915482618621/3125000000000 : ℝ)^103
        have hw : |(122472401/312500000 : ℝ)|=(122472401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5872856279/10000000000 : ℝ)|^135 ≤ (9955557418331/20000000000000 : ℝ)^103
        have hw : |(5872856279/10000000000 : ℝ)|=(5872856279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3031942247/10000000000 : ℝ)|^135 ≤ (20926769107921/100000000000000 : ℝ)^103
        have hw : |(3031942247/10000000000 : ℝ)|=(3031942247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2679221689/10000000000 : ℝ)*x 0 + (131329901/400000000 : ℝ)*x 1 + (-3341974633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679221689/10000000000 : ℝ)^135 ≤ (17795188792373/100000000000000 : ℝ)^103 := by
    have hnat : (2679221689 : ℕ)^135*100000000000000^103 ≤ 17795188792373^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679221689 10000000000 17795188792373 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131329901/400000000 : ℝ)^135 ≤ (23228920294161/100000000000000 : ℝ)^103 := by
    have hnat : (131329901 : ℕ)^135*100000000000000^103 ≤ 23228920294161^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131329901 400000000 23228920294161 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3341974633/5000000000 : ℝ)^135 ≤ (29487945448733/50000000000000 : ℝ)^103 := by
    have hnat : (3341974633 : ℕ)^135*50000000000000^103 ≤ 29487945448733^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3341974633 5000000000 29487945448733 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679221689/10000000000 : ℝ), (131329901/400000000 : ℝ), (-3341974633/5000000000 : ℝ)] ![(17795188792373/100000000000000 : ℝ), (23228920294161/100000000000000 : ℝ), (29487945448733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679221689/10000000000 : ℝ)|^135 ≤ (17795188792373/100000000000000 : ℝ)^103
        have hw : |(2679221689/10000000000 : ℝ)|=(2679221689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131329901/400000000 : ℝ)|^135 ≤ (23228920294161/100000000000000 : ℝ)^103
        have hw : |(131329901/400000000 : ℝ)|=(131329901/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3341974633/5000000000 : ℝ)|^135 ≤ (29487945448733/50000000000000 : ℝ)^103
        have hw : |(-3341974633/5000000000 : ℝ)|=(3341974633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-450070997/10000000000 : ℝ)*x 0 + (2858671297/5000000000 : ℝ)*x 1 + (-1182618423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450070997/10000000000 : ℝ)^135 ≤ (858722622873/50000000000000 : ℝ)^103 := by
    have hnat : (450070997 : ℕ)^135*50000000000000^103 ≤ 858722622873^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450070997 10000000000 858722622873 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2858671297/5000000000 : ℝ)^135 ≤ (4805730476673/10000000000000 : ℝ)^103 := by
    have hnat : (2858671297 : ℕ)^135*10000000000000^103 ≤ 4805730476673^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858671297 5000000000 4805730476673 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1182618423/2000000000 : ℝ)^135 ≤ (12556312493637/25000000000000 : ℝ)^103 := by
    have hnat : (1182618423 : ℕ)^135*25000000000000^103 ≤ 12556312493637^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182618423 2000000000 12556312493637 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-450070997/10000000000 : ℝ), (2858671297/5000000000 : ℝ), (-1182618423/2000000000 : ℝ)] ![(858722622873/50000000000000 : ℝ), (4805730476673/10000000000000 : ℝ), (12556312493637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-450070997/10000000000 : ℝ)|^135 ≤ (858722622873/50000000000000 : ℝ)^103
        have hw : |(-450070997/10000000000 : ℝ)|=(450070997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2858671297/5000000000 : ℝ)|^135 ≤ (4805730476673/10000000000000 : ℝ)^103
        have hw : |(2858671297/5000000000 : ℝ)|=(2858671297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1182618423/2000000000 : ℝ)|^135 ≤ (12556312493637/25000000000000 : ℝ)^103
        have hw : |(-1182618423/2000000000 : ℝ)|=(1182618423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (300841967/312500000 : ℝ)*x 0 + (-350175889/10000000000 : ℝ)*x 1 + (-397899649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (300841967/312500000 : ℝ)^135 ≤ (95138999450671/100000000000000 : ℝ)^103 := by
    have hnat : (300841967 : ℕ)^135*100000000000000^103 ≤ 95138999450671^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300841967 312500000 95138999450671 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350175889/10000000000 : ℝ)^135 ≤ (1236020444251/100000000000000 : ℝ)^103 := by
    have hnat : (350175889 : ℕ)^135*100000000000000^103 ≤ 1236020444251^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350175889 10000000000 1236020444251 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397899649/5000000000 : ℝ)^135 ≤ (1812490046863/50000000000000 : ℝ)^103 := by
    have hnat : (397899649 : ℕ)^135*50000000000000^103 ≤ 1812490046863^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397899649 5000000000 1812490046863 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(300841967/312500000 : ℝ), (-350175889/10000000000 : ℝ), (-397899649/5000000000 : ℝ)] ![(95138999450671/100000000000000 : ℝ), (1236020444251/100000000000000 : ℝ), (1812490046863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(300841967/312500000 : ℝ)|^135 ≤ (95138999450671/100000000000000 : ℝ)^103
        have hw : |(300841967/312500000 : ℝ)|=(300841967/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350175889/10000000000 : ℝ)|^135 ≤ (1236020444251/100000000000000 : ℝ)^103
        have hw : |(-350175889/10000000000 : ℝ)|=(350175889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397899649/5000000000 : ℝ)|^135 ≤ (1812490046863/50000000000000 : ℝ)^103
        have hw : |(-397899649/5000000000 : ℝ)|=(397899649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (523624829/2000000000 : ℝ)*x 0 + (6161635789/10000000000 : ℝ)*x 1 + (1981425743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523624829/2000000000 : ℝ)^135 ≤ (17265202178699/100000000000000 : ℝ)^103 := by
    have hnat : (523624829 : ℕ)^135*100000000000000^103 ≤ 17265202178699^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523624829 2000000000 17265202178699 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6161635789/10000000000 : ℝ)^135 ≤ (51767704709/97656250000 : ℝ)^103 := by
    have hnat : (6161635789 : ℕ)^135*97656250000^103 ≤ 51767704709^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6161635789 10000000000 51767704709 97656250000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981425743/5000000000 : ℝ)^135 ≤ (29724668177319/100000000000000 : ℝ)^103 := by
    have hnat : (1981425743 : ℕ)^135*100000000000000^103 ≤ 29724668177319^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981425743 5000000000 29724668177319 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523624829/2000000000 : ℝ), (6161635789/10000000000 : ℝ), (1981425743/5000000000 : ℝ)] ![(17265202178699/100000000000000 : ℝ), (51767704709/97656250000 : ℝ), (29724668177319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523624829/2000000000 : ℝ)|^135 ≤ (17265202178699/100000000000000 : ℝ)^103
        have hw : |(523624829/2000000000 : ℝ)|=(523624829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6161635789/10000000000 : ℝ)|^135 ≤ (51767704709/97656250000 : ℝ)^103
        have hw : |(6161635789/10000000000 : ℝ)|=(6161635789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1981425743/5000000000 : ℝ)|^135 ≤ (29724668177319/100000000000000 : ℝ)^103
        have hw : |(1981425743/5000000000 : ℝ)|=(1981425743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s0_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1096021263/2500000000 : ℝ)*x 0 + (669383119/1250000000 : ℝ)*x 1 + (-629129683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096021263/2500000000 : ℝ)^135 ≤ (16966336373699/50000000000000 : ℝ)^103 := by
    have hnat : (1096021263 : ℕ)^135*50000000000000^103 ≤ 16966336373699^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096021263 2500000000 16966336373699 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669383119/1250000000 : ℝ)^135 ≤ (44105980224941/100000000000000 : ℝ)^103 := by
    have hnat : (669383119 : ℕ)^135*100000000000000^103 ≤ 44105980224941^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669383119 1250000000 44105980224941 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629129683/2000000000 : ℝ)^135 ≤ (4392269403501/20000000000000 : ℝ)^103 := by
    have hnat : (629129683 : ℕ)^135*20000000000000^103 ≤ 4392269403501^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629129683 2000000000 4392269403501 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1096021263/2500000000 : ℝ), (669383119/1250000000 : ℝ), (-629129683/2000000000 : ℝ)] ![(16966336373699/50000000000000 : ℝ), (44105980224941/100000000000000 : ℝ), (4392269403501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1096021263/2500000000 : ℝ)|^135 ≤ (16966336373699/50000000000000 : ℝ)^103
        have hw : |(1096021263/2500000000 : ℝ)|=(1096021263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(669383119/1250000000 : ℝ)|^135 ≤ (44105980224941/100000000000000 : ℝ)^103
        have hw : |(669383119/1250000000 : ℝ)|=(669383119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-629129683/2000000000 : ℝ)|^135 ≤ (4392269403501/20000000000000 : ℝ)^103
        have hw : |(-629129683/2000000000 : ℝ)|=(629129683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s1_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-26856351/100000000 : ℝ)*x 0 + (178454839/400000000 : ℝ)*x 1 + (-5660324277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26856351/100000000 : ℝ)^135 ≤ (2231380134547/12500000000000 : ℝ)^103 := by
    have hnat : (26856351 : ℕ)^135*12500000000000^103 ≤ 2231380134547^103*100000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26856351 100000000 2231380134547 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178454839/400000000 : ℝ)^135 ≤ (34718847218623/100000000000000 : ℝ)^103 := by
    have hnat : (178454839 : ℕ)^135*100000000000000^103 ≤ 34718847218623^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178454839 400000000 34718847218623 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660324277/10000000000 : ℝ)^135 ≤ (47430111687893/100000000000000 : ℝ)^103 := by
    have hnat : (5660324277 : ℕ)^135*100000000000000^103 ≤ 47430111687893^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660324277 10000000000 47430111687893 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26856351/100000000 : ℝ), (178454839/400000000 : ℝ), (-5660324277/10000000000 : ℝ)] ![(2231380134547/12500000000000 : ℝ), (34718847218623/100000000000000 : ℝ), (47430111687893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26856351/100000000 : ℝ)|^135 ≤ (2231380134547/12500000000000 : ℝ)^103
        have hw : |(-26856351/100000000 : ℝ)|=(26856351/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(178454839/400000000 : ℝ)|^135 ≤ (34718847218623/100000000000000 : ℝ)^103
        have hw : |(178454839/400000000 : ℝ)|=(178454839/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5660324277/10000000000 : ℝ)|^135 ≤ (47430111687893/100000000000000 : ℝ)^103
        have hw : |(-5660324277/10000000000 : ℝ)|=(5660324277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s1_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6476907309/10000000000 : ℝ)*x 0 + (-359172011/1250000000 : ℝ)*x 1 + (-3355671043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6476907309/10000000000 : ℝ)^135 ≤ (11318619547797/20000000000000 : ℝ)^103 := by
    have hnat : (6476907309 : ℕ)^135*20000000000000^103 ≤ 11318619547797^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6476907309 10000000000 11318619547797 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359172011/1250000000 : ℝ)^135 ≤ (19504106388263/100000000000000 : ℝ)^103 := by
    have hnat : (359172011 : ℕ)^135*100000000000000^103 ≤ 19504106388263^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359172011 1250000000 19504106388263 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3355671043/10000000000 : ℝ)^135 ≤ (1493924740821/6250000000000 : ℝ)^103 := by
    have hnat : (3355671043 : ℕ)^135*6250000000000^103 ≤ 1493924740821^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3355671043 10000000000 1493924740821 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6476907309/10000000000 : ℝ), (-359172011/1250000000 : ℝ), (-3355671043/10000000000 : ℝ)] ![(11318619547797/20000000000000 : ℝ), (19504106388263/100000000000000 : ℝ), (1493924740821/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6476907309/10000000000 : ℝ)|^135 ≤ (11318619547797/20000000000000 : ℝ)^103
        have hw : |(6476907309/10000000000 : ℝ)|=(6476907309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-359172011/1250000000 : ℝ)|^135 ≤ (19504106388263/100000000000000 : ℝ)^103
        have hw : |(-359172011/1250000000 : ℝ)|=(359172011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3355671043/10000000000 : ℝ)|^135 ≤ (1493924740821/6250000000000 : ℝ)^103
        have hw : |(-3355671043/10000000000 : ℝ)|=(3355671043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (777370943/2000000000 : ℝ)*x 0 + (1302145157/2500000000 : ℝ)*x 1 + (3836513637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (777370943/2000000000 : ℝ)^135 ≤ (1159190626217/4000000000000 : ℝ)^103 := by
    have hnat : (777370943 : ℕ)^135*4000000000000^103 ≤ 1159190626217^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777370943 2000000000 1159190626217 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302145157/2500000000 : ℝ)^135 ≤ (1063285497789/2500000000000 : ℝ)^103 := by
    have hnat : (1302145157 : ℕ)^135*2500000000000^103 ≤ 1063285497789^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302145157 2500000000 1063285497789 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3836513637/10000000000 : ℝ)^135 ≤ (28488814418623/100000000000000 : ℝ)^103 := by
    have hnat : (3836513637 : ℕ)^135*100000000000000^103 ≤ 28488814418623^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3836513637 10000000000 28488814418623 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(777370943/2000000000 : ℝ), (1302145157/2500000000 : ℝ), (3836513637/10000000000 : ℝ)] ![(1159190626217/4000000000000 : ℝ), (1063285497789/2500000000000 : ℝ), (28488814418623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(777370943/2000000000 : ℝ)|^135 ≤ (1159190626217/4000000000000 : ℝ)^103
        have hw : |(777370943/2000000000 : ℝ)|=(777370943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302145157/2500000000 : ℝ)|^135 ≤ (1063285497789/2500000000000 : ℝ)^103
        have hw : |(1302145157/2500000000 : ℝ)|=(1302145157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3836513637/10000000000 : ℝ)|^135 ≤ (28488814418623/100000000000000 : ℝ)^103
        have hw : |(3836513637/10000000000 : ℝ)|=(3836513637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306079_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3833340001/10000000000 : ℝ)*x 0 + (4880578699/10000000000 : ℝ)*x 1 + (-2120385927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3833340001/10000000000 : ℝ)^135 ≤ (28457930281889/100000000000000 : ℝ)^103 := by
    have hnat : (3833340001 : ℕ)^135*100000000000000^103 ≤ 28457930281889^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3833340001 10000000000 28457930281889 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4880578699/10000000000 : ℝ)^135 ≤ (39055815534923/100000000000000 : ℝ)^103 := by
    have hnat : (4880578699 : ℕ)^135*100000000000000^103 ≤ 39055815534923^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880578699 10000000000 39055815534923 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120385927/5000000000 : ℝ)^135 ≤ (6497250832423/20000000000000 : ℝ)^103 := by
    have hnat : (2120385927 : ℕ)^135*20000000000000^103 ≤ 6497250832423^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120385927 5000000000 6497250832423 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3833340001/10000000000 : ℝ), (4880578699/10000000000 : ℝ), (-2120385927/5000000000 : ℝ)] ![(28457930281889/100000000000000 : ℝ), (39055815534923/100000000000000 : ℝ), (6497250832423/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3833340001/10000000000 : ℝ)|^135 ≤ (28457930281889/100000000000000 : ℝ)^103
        have hw : |(3833340001/10000000000 : ℝ)|=(3833340001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4880578699/10000000000 : ℝ)|^135 ≤ (39055815534923/100000000000000 : ℝ)^103
        have hw : |(4880578699/10000000000 : ℝ)|=(4880578699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2120385927/5000000000 : ℝ)|^135 ≤ (6497250832423/20000000000000 : ℝ)^103
        have hw : |(-2120385927/5000000000 : ℝ)|=(2120385927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306079 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
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
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(360031261787197/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4060256199/5000000000 : ℝ)*X 1 0+(-1537344571/10000000000 : ℝ)*X 1 1+(-1193087487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((201994079/625000000 : ℝ)*X 2 0+(1509360757/2500000000 : ℝ)*X 2 1+(884833553/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-342015271/2000000000 : ℝ)*X 0 0+(147442237/500000000 : ℝ)*X 0 1+(-7612769601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1614041481/2000000000 : ℝ)*X 1 0+(-3014597/100000000 : ℝ)*X 1 1+(-413823873/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((731264333/5000000000 : ℝ)*X 2 0+(7904552749/10000000000 : ℝ)*X 2 1+(11027711/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1203213673/5000000000 : ℝ)*X 0 0+(949200123/1250000000 : ℝ)*X 0 1+(-466261727/2000000000 : ℝ)*X 0 2+(1203213673/5000000000 : ℝ)*X 1 0+(949200123/1250000000 : ℝ)*X 1 1+(-466261727/2000000000 : ℝ)*X 1 2+(1203213673/5000000000 : ℝ)*X 2 0+(949200123/1250000000 : ℝ)*X 2 1+(-466261727/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-77607147/2500000000 : ℝ)*X 0 0+(179529593/500000000 : ℝ)*X 0 1+(-785100349/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2320943513/2500000000 : ℝ)*X 1 0+(-298464767/2500000000 : ℝ)*X 1 1+(-177116213/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((122472401/312500000 : ℝ)*X 2 0+(5872856279/10000000000 : ℝ)*X 2 1+(3031942247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2679221689/10000000000 : ℝ)*X 0 0+(131329901/400000000 : ℝ)*X 0 1+(-3341974633/5000000000 : ℝ)*X 0 2+(2679221689/10000000000 : ℝ)*X 1 0+(131329901/400000000 : ℝ)*X 1 1+(-3341974633/5000000000 : ℝ)*X 1 2+(2679221689/10000000000 : ℝ)*X 2 0+(131329901/400000000 : ℝ)*X 2 1+(-3341974633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-450070997/10000000000 : ℝ)*X 0 0+(2858671297/5000000000 : ℝ)*X 0 1+(-1182618423/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((300841967/312500000 : ℝ)*X 1 0+(-350175889/10000000000 : ℝ)*X 1 1+(-397899649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((523624829/2000000000 : ℝ)*X 2 0+(6161635789/10000000000 : ℝ)*X 2 1+(1981425743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1096021263/2500000000 : ℝ)*X 0 0+(669383119/1250000000 : ℝ)*X 0 1+(-629129683/2000000000 : ℝ)*X 0 2+(1096021263/2500000000 : ℝ)*X 1 0+(669383119/1250000000 : ℝ)*X 1 1+(-629129683/2000000000 : ℝ)*X 1 2+(1096021263/2500000000 : ℝ)*X 2 0+(669383119/1250000000 : ℝ)*X 2 1+(-629129683/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((42621/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42621/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2937795615772707800301/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248669/1000000000000 : ℝ)*(base18) + (739170027241/1000000000000 : ℝ)*(base39) + (95615436399/100000000000 : ℝ)*(base49) + (70557/20000000000 : ℝ)*(base53) + (120275078363/200000000000 : ℝ)*(base60) + (2626553022631/1000000000000 : ℝ)*(major_s0_0) + (2626553022631/1000000000000 : ℝ)*(major_s0_1) + (2626549494781/1000000000000 : ℝ)*(major_s0_2) + (7732371/500000000000 : ℝ)*(sp_s0_1) + (3549589088041/1000000000000 : ℝ)*(sp_s0_7) + (3549588796099/1000000000000 : ℝ)*(sp_s0_8) + (3549608037361/1000000000000 : ℝ)*(sp_s0_9) + (106468527567/62500000000 : ℝ)*(sp_s0_13) + (15421469/1000000000000 : ℝ)*(sp_s0_14) + (106468527567/62500000000 : ℝ)*(f.failure) + (3549608037361/1000000000000 : ℝ)*(f.sum) + (76032402445929/10000000000000000000000000000 : ℝ)*base63 + (1092513080572939/2500000000000000000000000000 : ℝ)*base65 + (875202412855307/2000000000000000000000000000 : ℝ)*base66 + (195003619518857/2000000000000000000000000000 : ℝ)*base69 + (3127412219568291/10000000000000000000000000000 : ℝ)*base71 + (243377180712911/2500000000000000000000000000 : ℝ)*base72 + (799864557212911/2500000000000000000000000000 : ℝ)*base75 + (1029766600344693/2000000000000000000000000000 : ℝ)*base76 + (1730351832128179/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (107/390625000000000 : ℝ)*base87 + (107/390625000000000 : ℝ)*base89 + (107/390625000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1723/3125 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1723/3125 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25351195743223659/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (1115395555641/1000000000000 : ℝ)*(base39) + (2270661/1000000000000 : ℝ)*(base40) + (561601482813/1000000000000 : ℝ)*(base49) + (31592309499/40000000000 : ℝ)*(base60) + (3179719168861/1000000000000 : ℝ)*(major_s0_0) + (3179719168861/1000000000000 : ℝ)*(major_s0_1) + (3179719168861/1000000000000 : ℝ)*(major_s0_2) + (4097169/500000000000 : ℝ)*(sp_s0_1) + (19373869/1000000000000 : ℝ)*(sp_s0_7) + (1074288837649/250000000000 : ℝ)*(sp_s0_14) + (4297125614029/1000000000000 : ℝ)*(sp_s0_15) + (268573420279/62500000000 : ℝ)*(sp_s0_16) + (2062261923171/1000000000000 : ℝ)*(sp_s0_20) + (20458049/500000000000 : ℝ)*(sp_s0_22) + (2062261923171/1000000000000 : ℝ)*(f.failure) + (268573420279/62500000000 : ℝ)*(f.sum) + (1259837572470751/10000000000000000000000000000 : ℝ)*base62 + (34997561041541/2500000000000000000000000000 : ℝ)*base64 + (216921468127383/2000000000000000000000000000 : ℝ)*base67 + (7194981727383/2000000000000000000000000000 : ℝ)*base68 + (2432093922196921/10000000000000000000000000000 : ℝ)*base71 + (1682098309791541/2500000000000000000000000000 : ℝ)*base72 + (85798254458459/2500000000000000000000000000 : ℝ)*base74 + (1678512044672617/2000000000000000000000000000 : ℝ)*base77 + (4324200425529249/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (28097/50000000000000000 : ℝ)*base86 + (28097/50000000000000000 : ℝ)*base88 + (28097/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-43639/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-43639/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5950312689511038407667/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1639663/1000000000000 : ℝ)*(base11) + (483027401489/500000000000 : ℝ)*(base39) + (596706900967/1000000000000 : ℝ)*(base49) + (319717/500000000000 : ℝ)*(base50) + (1233538564791/500000000000 : ℝ)*(major_s0_0) + (1233538564791/500000000000 : ℝ)*(major_s0_1) + (1233538564791/500000000000 : ℝ)*(major_s0_2) + (4166053/125000000000 : ℝ)*(sp_s0_2) + (552477/125000000000 : ℝ)*(sp_s0_9) + (413107/500000000000 : ℝ)*(sp_s0_13) + (3334086236779/1000000000000 : ℝ)*(sp_s0_21) + (1667043938221/500000000000 : ℝ)*(sp_s0_22) + (1667025064101/500000000000 : ℝ)*(sp_s0_23) + (200008095391/125000000000 : ℝ)*(sp_s0_27) + (800032794671/500000000000 : ℝ)*(f.failure) + (1667043938221/500000000000 : ℝ)*(f.sum) + (1536703271172381/5000000000000000000000000000 : ℝ)*base62 + (572383033105871/1250000000000000000000000000 : ℝ)*base64 + (998620720719173/1000000000000000000000000000 : ℝ)*base67 + (588664556019173/1000000000000000000000000000 : ℝ)*base68 + (1457801106519349/5000000000000000000000000000 : ℝ)*base70 + (146952827394129/1250000000000000000000000000 : ℝ)*base73 + (682550284394129/1250000000000000000000000000 : ℝ)*base74 + (696751747819173/1000000000000000000000000000 : ℝ)*base76 + (570825227672381/5000000000000000000000000000 : ℝ)*base79 + (21403/25000000000000000 : ℝ)*base87 + (21403/25000000000000000 : ℝ)*base89 + (21403/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (42621/100000 : ℝ) ^ (67/16 : ℝ) ≤ (2812217926461789421/100000000000000000000 : ℝ) := by
    have hpowers : (42621/100000 : ℝ)^67 ≤ (2812217926461789421/100000000000000000000 : ℝ)^16 := by
      have hnat : (42621 : ℕ)^67*100000000000000000000^16 ≤ 2812217926461789421^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42621 100000 2812217926461789421 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42621/100000 : ℝ)) (X := (2812217926461789421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102812217926461789421/100000000000000000000 : ℝ) ≤ (2013290056752999/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (102812217926461789421/100000000000000000000 : ℝ)^16 ≤ (2013290056752999/2000000000000000 : ℝ)^67 := by
      have hnat : (102812217926461789421 : ℕ)^16*2000000000000000^67 ≤ 2013290056752999^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102812217926461789421 100000000000000000000 2013290056752999 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2013290056752999/2000000000000000 : ℝ)) (X := (102812217926461789421/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52812217926461789421/50000000000000000000 : ℝ) ≤ (1266441385382239/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (52812217926461789421/50000000000000000000 : ℝ)^16 ≤ (1266441385382239/1250000000000000 : ℝ)^67 := by
      have hnat : (52812217926461789421 : ℕ)^16*1250000000000000^67 ≤ 1266441385382239^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52812217926461789421 50000000000000000000 1266441385382239 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1266441385382239/1250000000000000 : ℝ)) (X := (52812217926461789421/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(13290056752999/852420000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(65080799292917/4262100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (42621/100000 : ℝ)) (alpha := (13290056752999/852420000000000 : ℝ)) (beta := (65080799292917/4262100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (42621/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(13290056752999/852420000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(65080799292917/4262100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1723/3125 : ℝ) ^ (67/16 : ℝ) ≤ (1653065755311852249/20000000000000000000 : ℝ) := by
    have hpowers : (1723/3125 : ℝ)^67 ≤ (1653065755311852249/20000000000000000000 : ℝ)^16 := by
      have hnat : (1723 : ℕ)^67*20000000000000000000^16 ≤ 1653065755311852249^16*3125^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1723 3125 1653065755311852249 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1723/3125 : ℝ)) (X := (1653065755311852249/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (21653065755311852249/20000000000000000000 : ℝ) ≤ (10191456952478783/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (21653065755311852249/20000000000000000000 : ℝ)^16 ≤ (10191456952478783/10000000000000000 : ℝ)^67 := by
      have hnat : (21653065755311852249 : ℕ)^16*10000000000000000^67 ≤ 10191456952478783^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21653065755311852249 20000000000000000000 10191456952478783 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10191456952478783/10000000000000000 : ℝ)) (X := (21653065755311852249/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (11653065755311852249/10000000000000000000 : ℝ) ≤ (10372090935601271/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (11653065755311852249/10000000000000000000 : ℝ)^16 ≤ (10372090935601271/10000000000000000 : ℝ)^67 := by
      have hnat : (11653065755311852249 : ℕ)^16*10000000000000000^67 ≤ 10372090935601271^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11653065755311852249 10000000000000000000 10372090935601271 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10372090935601271/10000000000000000 : ℝ)) (X := (11653065755311852249/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(191456952478783/5513600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(22579247890311/689200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1723/3125 : ℝ)) (alpha := (191456952478783/5513600000000000 : ℝ)) (beta := (22579247890311/689200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1723/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(191456952478783/5513600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(22579247890311/689200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (43639/100000 : ℝ) ^ (67/16 : ℝ) ≤ (48506027578045801/1562500000000000000 : ℝ) := by
    have hpowers : (43639/100000 : ℝ)^67 ≤ (48506027578045801/1562500000000000000 : ℝ)^16 := by
      have hnat : (43639 : ℕ)^67*1562500000000000000^16 ≤ 48506027578045801^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43639 100000 48506027578045801 1562500000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43639/100000 : ℝ)) (X := (48506027578045801/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1611006027578045801/1562500000000000000 : ℝ) ≤ (10073274299554409/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (1611006027578045801/1562500000000000000 : ℝ)^16 ≤ (10073274299554409/10000000000000000 : ℝ)^67 := by
      have hnat : (1611006027578045801 : ℕ)^16*10000000000000000^67 ≤ 10073274299554409^67*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1611006027578045801 1562500000000000000 10073274299554409 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10073274299554409/10000000000000000 : ℝ)) (X := (1611006027578045801/1562500000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (829756027578045801/781250000000000000 : ℝ) ≤ (317027749628289/312500000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (829756027578045801/781250000000000000 : ℝ)^16 ≤ (317027749628289/312500000000000 : ℝ)^67 := by
      have hnat : (829756027578045801 : ℕ)^16*312500000000000^67 ≤ 317027749628289^67*781250000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        829756027578045801 781250000000000000 317027749628289 312500000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (317027749628289/312500000000000 : ℝ)) (X := (829756027578045801/781250000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(73274299554409/4363900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(71613688550839/4363900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (43639/100000 : ℝ)) (alpha := (73274299554409/4363900000000000 : ℝ)) (beta := (71613688550839/4363900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (43639/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(73274299554409/4363900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(71613688550839/4363900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-26856351/100000000 : ℝ)*X 0 0+(178454839/400000000 : ℝ)*X 0 1+(-5660324277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6476907309/10000000000 : ℝ)*X 1 0+(-359172011/1250000000 : ℝ)*X 1 1+(-3355671043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((777370943/2000000000 : ℝ)*X 2 0+(1302145157/2500000000 : ℝ)*X 2 1+(3836513637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3833340001/10000000000 : ℝ)*X 0 0+(4880578699/10000000000 : ℝ)*X 0 1+(-2120385927/5000000000 : ℝ)*X 0 2+(3833340001/10000000000 : ℝ)*X 1 0+(4880578699/10000000000 : ℝ)*X 1 1+(-2120385927/5000000000 : ℝ)*X 1 2+(3833340001/10000000000 : ℝ)*X 2 0+(4880578699/10000000000 : ℝ)*X 2 1+(-2120385927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-156279/25000 : ℝ) < ((-77093/50000 : ℝ)*P 0+(-77093/50000 : ℝ)*P 1+(-77093/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-156279/25000 : ℝ) < (-759826291980018278274334322579/122393305000000000000000000000 : ℝ) := by norm_num
    linear_combination (3047/200000000000 : ℝ)*(base12) + (75823/1000000000000 : ℝ)*(base15) + (1267/40000000000 : ℝ)*(base25) + (399831064889/1000000000000 : ℝ)*(base39) + (151841679859/500000000000 : ℝ)*(base49) + (563/1000000000000 : ℝ)*(base50) + (31177583021/200000000000 : ℝ)*(base60) + (7673/500000000000 : ℝ)*(ratio_s0_0) + (77093/50000 : ℝ)*(major_s1_0) + (77093/50000 : ℝ)*(major_s1_1) + (77093/50000 : ℝ)*(major_s1_2) + (2069356888391/1000000000000 : ℝ)*(sp_s1_0) + (2069356827803/1000000000000 : ℝ)*(sp_s1_1) + (129334804497/62500000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2069356903627/1000000000000 : ℝ)*(f.sum) + (2348353592738723/7518999700000000000000000000 : ℝ)*base62 + (154144464311/17455600000000000000000000 : ℝ)*base64 + (5234201894539/17230000000000000000000000 : ℝ)*base66 + (248634323289847/436390000000000000000000000 : ℝ)*base69 + (150846525040202227/2324922273750000000000000000000 : ℝ)*base71 + (153035482085491/426210000000000000000000000 : ℝ)*base72 + (144026467383/215375000000000000000000 : ℝ)*base74 + (184974341741/6659531250000000000000000 : ℝ)*base77 + (4398071418489677/183589957500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p006_b035 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c306079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c306080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p006_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

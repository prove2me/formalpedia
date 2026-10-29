-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:28:26.146485+00:00
-- url     : https://prove2.me/submissions/466757c0-d26b-4bad-8178-c8f3c5547daa

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305080_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305080_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305080_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305080_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c305080 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c305080_s0 p hpa hpb X hX
  have h1 := collision_c305080_s1 p hpa hpb X hX h0
  have h2 := collision_c305080_s2 p hpa hpb X hX h1
  exact collision_c305080_s3 p hpa hpb X hX h2

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
theorem collision_support_c305079_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4065982499/5000000000 : ℝ)*x 0 + (-307672103/2000000000 : ℝ)*x 1 + (-2388001569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4065982499/5000000000 : ℝ)^67 ≤ (19052920211443/25000000000000 : ℝ)^51 := by
    have hnat : (4065982499 : ℕ)^67*25000000000000^51 ≤ 19052920211443^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4065982499 5000000000 19052920211443 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307672103/2000000000 : ℝ)^67 ≤ (4275506197209/50000000000000 : ℝ)^51 := by
    have hnat : (307672103 : ℕ)^67*50000000000000^51 ≤ 4275506197209^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307672103 2000000000 4275506197209 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388001569/10000000000 : ℝ)^67 ≤ (1904663342049/12500000000000 : ℝ)^51 := by
    have hnat : (2388001569 : ℕ)^67*12500000000000^51 ≤ 1904663342049^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388001569 10000000000 1904663342049 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4065982499/5000000000 : ℝ), (-307672103/2000000000 : ℝ), (-2388001569/10000000000 : ℝ)] ![(19052920211443/25000000000000 : ℝ), (4275506197209/50000000000000 : ℝ), (1904663342049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4065982499/5000000000 : ℝ)|^67 ≤ (19052920211443/25000000000000 : ℝ)^51
        have hw : |(4065982499/5000000000 : ℝ)|=(4065982499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-307672103/2000000000 : ℝ)|^67 ≤ (4275506197209/50000000000000 : ℝ)^51
        have hw : |(-307672103/2000000000 : ℝ)|=(307672103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2388001569/10000000000 : ℝ)|^67 ≤ (1904663342049/12500000000000 : ℝ)^51
        have hw : |(-2388001569/10000000000 : ℝ)|=(2388001569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1620478271/5000000000 : ℝ)*x 0 + (6045716793/10000000000 : ℝ)*x 1 + (709176251/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1620478271/5000000000 : ℝ)^67 ≤ (910372040511/4000000000000 : ℝ)^51 := by
    have hnat : (1620478271 : ℕ)^67*4000000000000^51 ≤ 910372040511^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620478271 5000000000 910372040511 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6045716793/10000000000 : ℝ)^67 ≤ (322672846377/625000000000 : ℝ)^51 := by
    have hnat : (6045716793 : ℕ)^67*625000000000^51 ≤ 322672846377^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6045716793 10000000000 322672846377 625000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709176251/2000000000 : ℝ)^67 ≤ (25613043546831/100000000000000 : ℝ)^51 := by
    have hnat : (709176251 : ℕ)^67*100000000000000^51 ≤ 25613043546831^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709176251 2000000000 25613043546831 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1620478271/5000000000 : ℝ), (6045716793/10000000000 : ℝ), (709176251/2000000000 : ℝ)] ![(910372040511/4000000000000 : ℝ), (322672846377/625000000000 : ℝ), (25613043546831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1620478271/5000000000 : ℝ)|^67 ≤ (910372040511/4000000000000 : ℝ)^51
        have hw : |(1620478271/5000000000 : ℝ)|=(1620478271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6045716793/10000000000 : ℝ)|^67 ≤ (322672846377/625000000000 : ℝ)^51
        have hw : |(6045716793/10000000000 : ℝ)|=(6045716793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709176251/2000000000 : ℝ)|^67 ≤ (25613043546831/100000000000000 : ℝ)^51
        have hw : |(709176251/2000000000 : ℝ)|=(709176251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1702509421/10000000000 : ℝ)*x 0 + (734137781/2500000000 : ℝ)*x 1 + (-1910507971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1702509421/10000000000 : ℝ)^67 ≤ (9769283386011/100000000000000 : ℝ)^51 := by
    have hnat : (1702509421 : ℕ)^67*100000000000000^51 ≤ 9769283386011^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702509421 10000000000 9769283386011 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (734137781/2500000000 : ℝ)^67 ≤ (999665375283/5000000000000 : ℝ)^51 := by
    have hnat : (734137781 : ℕ)^67*5000000000000^51 ≤ 999665375283^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734137781 2500000000 999665375283 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1910507971/2500000000 : ℝ)^67 ≤ (70237409102167/100000000000000 : ℝ)^51 := by
    have hnat : (1910507971 : ℕ)^67*100000000000000^51 ≤ 70237409102167^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910507971 2500000000 70237409102167 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1702509421/10000000000 : ℝ), (734137781/2500000000 : ℝ), (-1910507971/2500000000 : ℝ)] ![(9769283386011/100000000000000 : ℝ), (999665375283/5000000000000 : ℝ), (70237409102167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1702509421/10000000000 : ℝ)|^67 ≤ (9769283386011/100000000000000 : ℝ)^51
        have hw : |(-1702509421/10000000000 : ℝ)|=(1702509421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(734137781/2500000000 : ℝ)|^67 ≤ (999665375283/5000000000000 : ℝ)^51
        have hw : |(734137781/2500000000 : ℝ)|=(734137781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1910507971/2500000000 : ℝ)|^67 ≤ (70237409102167/100000000000000 : ℝ)^51
        have hw : |(-1910507971/2500000000 : ℝ)|=(1910507971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2017745017/2500000000 : ℝ)*x 0 + (-294082017/10000000000 : ℝ)*x 1 + (-1663993567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017745017/2500000000 : ℝ)^67 ≤ (15092343126187/20000000000000 : ℝ)^51 := by
    have hnat : (2017745017 : ℕ)^67*20000000000000^51 ≤ 15092343126187^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017745017 2500000000 15092343126187 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294082017/10000000000 : ℝ)^67 ≤ (97272031899/10000000000000 : ℝ)^51 := by
    have hnat : (294082017 : ℕ)^67*10000000000000^51 ≤ 97272031899^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294082017 10000000000 97272031899 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1663993567/5000000000 : ℝ)^67 ≤ (23565564038421/100000000000000 : ℝ)^51 := by
    have hnat : (1663993567 : ℕ)^67*100000000000000^51 ≤ 23565564038421^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663993567 5000000000 23565564038421 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2017745017/2500000000 : ℝ), (-294082017/10000000000 : ℝ), (-1663993567/5000000000 : ℝ)] ![(15092343126187/20000000000000 : ℝ), (97272031899/10000000000000 : ℝ), (23565564038421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2017745017/2500000000 : ℝ)|^67 ≤ (15092343126187/20000000000000 : ℝ)^51
        have hw : |(2017745017/2500000000 : ℝ)|=(2017745017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294082017/10000000000 : ℝ)|^67 ≤ (97272031899/10000000000000 : ℝ)^51
        have hw : |(-294082017/10000000000 : ℝ)|=(294082017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1663993567/5000000000 : ℝ)|^67 ≤ (23565564038421/100000000000000 : ℝ)^51
        have hw : |(-1663993567/5000000000 : ℝ)|=(1663993567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1448215877/10000000000 : ℝ)*x 0 + (7930112539/10000000000 : ℝ)*x 1 + (688165723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1448215877/10000000000 : ℝ)^67 ≤ (7898876460819/100000000000000 : ℝ)^51 := by
    have hnat : (1448215877 : ℕ)^67*100000000000000^51 ≤ 7898876460819^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448215877 10000000000 7898876460819 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7930112539/10000000000 : ℝ)^67 ≤ (36868096861067/50000000000000 : ℝ)^51 := by
    have hnat : (7930112539 : ℕ)^67*50000000000000^51 ≤ 36868096861067^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7930112539 10000000000 36868096861067 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688165723/2500000000 : ℝ)^67 ≤ (3672985958773/20000000000000 : ℝ)^51 := by
    have hnat : (688165723 : ℕ)^67*20000000000000^51 ≤ 3672985958773^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688165723 2500000000 3672985958773 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1448215877/10000000000 : ℝ), (7930112539/10000000000 : ℝ), (688165723/2500000000 : ℝ)] ![(7898876460819/100000000000000 : ℝ), (36868096861067/50000000000000 : ℝ), (3672985958773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1448215877/10000000000 : ℝ)|^67 ≤ (7898876460819/100000000000000 : ℝ)^51
        have hw : |(1448215877/10000000000 : ℝ)|=(1448215877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7930112539/10000000000 : ℝ)|^67 ≤ (36868096861067/50000000000000 : ℝ)^51
        have hw : |(7930112539/10000000000 : ℝ)|=(7930112539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(688165723/2500000000 : ℝ)|^67 ≤ (3672985958773/20000000000000 : ℝ)^51
        have hw : |(688165723/2500000000 : ℝ)|=(688165723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1199791743/5000000000 : ℝ)*x 0 + (1902633813/2500000000 : ℝ)*x 1 + (-1168317361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1199791743/5000000000 : ℝ)^67 ≤ (3833616744927/25000000000000 : ℝ)^51 := by
    have hnat : (1199791743 : ℕ)^67*25000000000000^51 ≤ 3833616744927^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199791743 5000000000 3833616744927 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902633813/2500000000 : ℝ)^67 ≤ (17464338350879/25000000000000 : ℝ)^51 := by
    have hnat : (1902633813 : ℕ)^67*25000000000000^51 ≤ 17464338350879^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902633813 2500000000 17464338350879 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1168317361/5000000000 : ℝ)^67 ≤ (14808179607403/100000000000000 : ℝ)^51 := by
    have hnat : (1168317361 : ℕ)^67*100000000000000^51 ≤ 14808179607403^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168317361 5000000000 14808179607403 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1199791743/5000000000 : ℝ), (1902633813/2500000000 : ℝ), (-1168317361/5000000000 : ℝ)] ![(3833616744927/25000000000000 : ℝ), (17464338350879/25000000000000 : ℝ), (14808179607403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1199791743/5000000000 : ℝ)|^67 ≤ (3833616744927/25000000000000 : ℝ)^51
        have hw : |(1199791743/5000000000 : ℝ)|=(1199791743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1902633813/2500000000 : ℝ)|^67 ≤ (17464338350879/25000000000000 : ℝ)^51
        have hw : |(1902633813/2500000000 : ℝ)|=(1902633813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1168317361/5000000000 : ℝ)|^67 ≤ (14808179607403/100000000000000 : ℝ)^51
        have hw : |(-1168317361/5000000000 : ℝ)|=(1168317361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-304598559/10000000000 : ℝ)*x 0 + (3587245987/10000000000 : ℝ)*x 1 + (-7867724037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (304598559/10000000000 : ℝ)^67 ≤ (203734517369/20000000000000 : ℝ)^51 := by
    have hnat : (304598559 : ℕ)^67*20000000000000^51 ≤ 203734517369^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304598559 10000000000 203734517369 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3587245987/10000000000 : ℝ)^67 ≤ (26006289010531/100000000000000 : ℝ)^51 := by
    have hnat : (3587245987 : ℕ)^67*100000000000000^51 ≤ 26006289010531^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3587245987 10000000000 26006289010531 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7867724037/10000000000 : ℝ)^67 ≤ (570117487433/781250000000 : ℝ)^51 := by
    have hnat : (7867724037 : ℕ)^67*781250000000^51 ≤ 570117487433^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7867724037 10000000000 570117487433 781250000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-304598559/10000000000 : ℝ), (3587245987/10000000000 : ℝ), (-7867724037/10000000000 : ℝ)] ![(203734517369/20000000000000 : ℝ), (26006289010531/100000000000000 : ℝ), (570117487433/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-304598559/10000000000 : ℝ)|^67 ≤ (203734517369/20000000000000 : ℝ)^51
        have hw : |(-304598559/10000000000 : ℝ)|=(304598559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3587245987/10000000000 : ℝ)|^67 ≤ (26006289010531/100000000000000 : ℝ)^51
        have hw : |(3587245987/10000000000 : ℝ)|=(3587245987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7867724037/10000000000 : ℝ)|^67 ≤ (570117487433/781250000000 : ℝ)^51
        have hw : |(-7867724037/10000000000 : ℝ)|=(7867724037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (58167829/62500000 : ℝ)*x 0 + (-1174969741/10000000000 : ℝ)*x 1 + (-693761489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58167829/62500000 : ℝ)^67 ≤ (90994573234679/100000000000000 : ℝ)^51 := by
    have hnat : (58167829 : ℕ)^67*100000000000000^51 ≤ 90994573234679^51*62500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58167829 62500000 90994573234679 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1174969741/10000000000 : ℝ)^67 ≤ (6001645611991/100000000000000 : ℝ)^51 := by
    have hnat : (1174969741 : ℕ)^67*100000000000000^51 ≤ 6001645611991^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174969741 10000000000 6001645611991 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693761489/10000000000 : ℝ)^67 ≤ (150189057157/5000000000000 : ℝ)^51 := by
    have hnat : (693761489 : ℕ)^67*5000000000000^51 ≤ 150189057157^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693761489 10000000000 150189057157 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(58167829/62500000 : ℝ), (-1174969741/10000000000 : ℝ), (-693761489/10000000000 : ℝ)] ![(90994573234679/100000000000000 : ℝ), (6001645611991/100000000000000 : ℝ), (150189057157/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(58167829/62500000 : ℝ)|^67 ≤ (90994573234679/100000000000000 : ℝ)^51
        have hw : |(58167829/62500000 : ℝ)|=(58167829/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1174969741/10000000000 : ℝ)|^67 ≤ (6001645611991/100000000000000 : ℝ)^51
        have hw : |(-1174969741/10000000000 : ℝ)|=(1174969741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-693761489/10000000000 : ℝ)|^67 ≤ (150189057157/5000000000000 : ℝ)^51
        have hw : |(-693761489/10000000000 : ℝ)|=(693761489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (15769059/40000000 : ℝ)*x 0 + (2934924827/5000000000 : ℝ)*x 1 + (3037095489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15769059/40000000 : ℝ)^67 ≤ (14719428214577/50000000000000 : ℝ)^51 := by
    have hnat : (15769059 : ℕ)^67*50000000000000^51 ≤ 14719428214577^51*40000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15769059 40000000 14719428214577 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2934924827/5000000000 : ℝ)^67 ≤ (49663733278611/100000000000000 : ℝ)^51 := by
    have hnat : (2934924827 : ℕ)^67*100000000000000^51 ≤ 49663733278611^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934924827 5000000000 49663733278611 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3037095489/10000000000 : ℝ)^67 ≤ (20897410276153/100000000000000 : ℝ)^51 := by
    have hnat : (3037095489 : ℕ)^67*100000000000000^51 ≤ 20897410276153^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3037095489 10000000000 20897410276153 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(15769059/40000000 : ℝ), (2934924827/5000000000 : ℝ), (3037095489/10000000000 : ℝ)] ![(14719428214577/50000000000000 : ℝ), (49663733278611/100000000000000 : ℝ), (20897410276153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(15769059/40000000 : ℝ)|^67 ≤ (14719428214577/50000000000000 : ℝ)^51
        have hw : |(15769059/40000000 : ℝ)|=(15769059/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2934924827/5000000000 : ℝ)|^67 ≤ (49663733278611/100000000000000 : ℝ)^51
        have hw : |(2934924827/5000000000 : ℝ)|=(2934924827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3037095489/10000000000 : ℝ)|^67 ≤ (20897410276153/100000000000000 : ℝ)^51
        have hw : |(3037095489/10000000000 : ℝ)|=(3037095489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (268445799/1000000000 : ℝ)*x 0 + (3270703627/10000000000 : ℝ)*x 1 + (-6709228407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268445799/1000000000 : ℝ)^67 ≤ (8884732913181/50000000000000 : ℝ)^51 := by
    have hnat : (268445799 : ℕ)^67*50000000000000^51 ≤ 8884732913181^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268445799 1000000000 8884732913181 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3270703627/10000000000 : ℝ)^67 ≤ (1151706365251/5000000000000 : ℝ)^51 := by
    have hnat : (3270703627 : ℕ)^67*5000000000000^51 ≤ 1151706365251^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3270703627 10000000000 1151706365251 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6709228407/10000000000 : ℝ)^67 ≤ (29598203427647/50000000000000 : ℝ)^51 := by
    have hnat : (6709228407 : ℕ)^67*50000000000000^51 ≤ 29598203427647^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6709228407 10000000000 29598203427647 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268445799/1000000000 : ℝ), (3270703627/10000000000 : ℝ), (-6709228407/10000000000 : ℝ)] ![(8884732913181/50000000000000 : ℝ), (1151706365251/5000000000000 : ℝ), (29598203427647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268445799/1000000000 : ℝ)|^67 ≤ (8884732913181/50000000000000 : ℝ)^51
        have hw : |(268445799/1000000000 : ℝ)|=(268445799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3270703627/10000000000 : ℝ)|^67 ≤ (1151706365251/5000000000000 : ℝ)^51
        have hw : |(3270703627/10000000000 : ℝ)|=(3270703627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6709228407/10000000000 : ℝ)|^67 ≤ (29598203427647/50000000000000 : ℝ)^51
        have hw : |(-6709228407/10000000000 : ℝ)|=(6709228407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-223654421/5000000000 : ℝ)*x 0 + (5735358449/10000000000 : ℝ)*x 1 + (-2956242147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223654421/5000000000 : ℝ)^67 ≤ (1687596648189/100000000000000 : ℝ)^51 := by
    have hnat : (223654421 : ℕ)^67*100000000000000^51 ≤ 1687596648189^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223654421 5000000000 1687596648189 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5735358449/10000000000 : ℝ)^67 ≤ (48174238763469/100000000000000 : ℝ)^51 := by
    have hnat : (5735358449 : ℕ)^67*100000000000000^51 ≤ 48174238763469^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5735358449 10000000000 48174238763469 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956242147/5000000000 : ℝ)^67 ≤ (10027632913479/20000000000000 : ℝ)^51 := by
    have hnat : (2956242147 : ℕ)^67*20000000000000^51 ≤ 10027632913479^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956242147 5000000000 10027632913479 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223654421/5000000000 : ℝ), (5735358449/10000000000 : ℝ), (-2956242147/5000000000 : ℝ)] ![(1687596648189/100000000000000 : ℝ), (48174238763469/100000000000000 : ℝ), (10027632913479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223654421/5000000000 : ℝ)|^67 ≤ (1687596648189/100000000000000 : ℝ)^51
        have hw : |(-223654421/5000000000 : ℝ)|=(223654421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5735358449/10000000000 : ℝ)|^67 ≤ (48174238763469/100000000000000 : ℝ)^51
        have hw : |(5735358449/10000000000 : ℝ)|=(5735358449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2956242147/5000000000 : ℝ)|^67 ≤ (10027632913479/20000000000000 : ℝ)^51
        have hw : |(-2956242147/5000000000 : ℝ)|=(2956242147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9639118449/10000000000 : ℝ)*x 0 + (-345291917/10000000000 : ℝ)*x 1 + (-781561409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9639118449/10000000000 : ℝ)^67 ≤ (47643035150087/50000000000000 : ℝ)^51 := by
    have hnat : (9639118449 : ℕ)^67*50000000000000^51 ≤ 47643035150087^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9639118449 10000000000 47643035150087 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345291917/10000000000 : ℝ)^67 ≤ (1201097401823/100000000000000 : ℝ)^51 := by
    have hnat : (345291917 : ℕ)^67*100000000000000^51 ≤ 1201097401823^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345291917 10000000000 1201097401823 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (781561409/10000000000 : ℝ)^67 ≤ (219552017693/6250000000000 : ℝ)^51 := by
    have hnat : (781561409 : ℕ)^67*6250000000000^51 ≤ 219552017693^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781561409 10000000000 219552017693 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9639118449/10000000000 : ℝ), (-345291917/10000000000 : ℝ), (-781561409/10000000000 : ℝ)] ![(47643035150087/50000000000000 : ℝ), (1201097401823/100000000000000 : ℝ), (219552017693/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9639118449/10000000000 : ℝ)|^67 ≤ (47643035150087/50000000000000 : ℝ)^51
        have hw : |(9639118449/10000000000 : ℝ)|=(9639118449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345291917/10000000000 : ℝ)|^67 ≤ (1201097401823/100000000000000 : ℝ)^51
        have hw : |(-345291917/10000000000 : ℝ)|=(345291917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-781561409/10000000000 : ℝ)|^67 ≤ (219552017693/6250000000000 : ℝ)^51
        have hw : |(-781561409/10000000000 : ℝ)|=(781561409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2618702359/10000000000 : ℝ)*x 0 + (618417629/1000000000 : ℝ)*x 1 + (792013083/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618702359/10000000000 : ℝ)^67 ≤ (8599930323609/50000000000000 : ℝ)^51 := by
    have hnat : (2618702359 : ℕ)^67*50000000000000^51 ≤ 8599930323609^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618702359 10000000000 8599930323609 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618417629/1000000000 : ℝ)^67 ≤ (53186530493571/100000000000000 : ℝ)^51 := by
    have hnat : (618417629 : ℕ)^67*100000000000000^51 ≤ 53186530493571^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618417629 1000000000 53186530493571 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792013083/2000000000 : ℝ)^67 ≤ (29613608842653/100000000000000 : ℝ)^51 := by
    have hnat : (792013083 : ℕ)^67*100000000000000^51 ≤ 29613608842653^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792013083 2000000000 29613608842653 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618702359/10000000000 : ℝ), (618417629/1000000000 : ℝ), (792013083/2000000000 : ℝ)] ![(8599930323609/50000000000000 : ℝ), (53186530493571/100000000000000 : ℝ), (29613608842653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618702359/10000000000 : ℝ)|^67 ≤ (8599930323609/50000000000000 : ℝ)^51
        have hw : |(2618702359/10000000000 : ℝ)|=(2618702359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618417629/1000000000 : ℝ)|^67 ≤ (53186530493571/100000000000000 : ℝ)^51
        have hw : |(618417629/1000000000 : ℝ)|=(618417629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792013083/2000000000 : ℝ)|^67 ≤ (29613608842653/100000000000000 : ℝ)^51
        have hw : |(792013083/2000000000 : ℝ)|=(792013083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s0_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2215664073/5000000000 : ℝ)*x 0 + (1334429577/2500000000 : ℝ)*x 1 + (-3140552069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215664073/5000000000 : ℝ)^67 ≤ (3432753269/10000000000 : ℝ)^51 := by
    have hnat : (2215664073 : ℕ)^67*10000000000^51 ≤ 3432753269^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215664073 5000000000 3432753269 10000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1334429577/2500000000 : ℝ)^67 ≤ (43834914975827/100000000000000 : ℝ)^51 := by
    have hnat : (1334429577 : ℕ)^67*100000000000000^51 ≤ 43834914975827^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334429577 2500000000 43834914975827 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3140552069/10000000000 : ℝ)^67 ≤ (10918776158313/50000000000000 : ℝ)^51 := by
    have hnat : (3140552069 : ℕ)^67*50000000000000^51 ≤ 10918776158313^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3140552069 10000000000 10918776158313 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2215664073/5000000000 : ℝ), (1334429577/2500000000 : ℝ), (-3140552069/10000000000 : ℝ)] ![(3432753269/10000000000 : ℝ), (43834914975827/100000000000000 : ℝ), (10918776158313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2215664073/5000000000 : ℝ)|^67 ≤ (3432753269/10000000000 : ℝ)^51
        have hw : |(2215664073/5000000000 : ℝ)|=(2215664073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1334429577/2500000000 : ℝ)|^67 ≤ (43834914975827/100000000000000 : ℝ)^51
        have hw : |(1334429577/2500000000 : ℝ)|=(1334429577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3140552069/10000000000 : ℝ)|^67 ≤ (10918776158313/50000000000000 : ℝ)^51
        have hw : |(-3140552069/10000000000 : ℝ)|=(3140552069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2685400567/10000000000 : ℝ)*x 0 + (446844957/1000000000 : ℝ)*x 1 + (-1135131361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685400567/10000000000 : ℝ)^67 ≤ (17777662981283/100000000000000 : ℝ)^51 := by
    have hnat : (2685400567 : ℕ)^67*100000000000000^51 ≤ 17777662981283^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685400567 10000000000 17777662981283 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446844957/1000000000 : ℝ)^67 ≤ (34705807265209/100000000000000 : ℝ)^51 := by
    have hnat : (446844957 : ℕ)^67*100000000000000^51 ≤ 34705807265209^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446844957 1000000000 34705807265209 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135131361/2000000000 : ℝ)^67 ≤ (23758264872293/50000000000000 : ℝ)^51 := by
    have hnat : (1135131361 : ℕ)^67*50000000000000^51 ≤ 23758264872293^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135131361 2000000000 23758264872293 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2685400567/10000000000 : ℝ), (446844957/1000000000 : ℝ), (-1135131361/2000000000 : ℝ)] ![(17777662981283/100000000000000 : ℝ), (34705807265209/100000000000000 : ℝ), (23758264872293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2685400567/10000000000 : ℝ)|^67 ≤ (17777662981283/100000000000000 : ℝ)^51
        have hw : |(-2685400567/10000000000 : ℝ)|=(2685400567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(446844957/1000000000 : ℝ)|^67 ≤ (34705807265209/100000000000000 : ℝ)^51
        have hw : |(446844957/1000000000 : ℝ)|=(446844957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135131361/2000000000 : ℝ)|^67 ≤ (23758264872293/50000000000000 : ℝ)^51
        have hw : |(-1135131361/2000000000 : ℝ)|=(1135131361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1622860549/2500000000 : ℝ)*x 0 + (-2881129681/10000000000 : ℝ)*x 1 + (-3354871283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1622860549/2500000000 : ℝ)^67 ≤ (28342479925727/50000000000000 : ℝ)^51 := by
    have hnat : (1622860549 : ℕ)^67*50000000000000^51 ≤ 28342479925727^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1622860549 2500000000 28342479925727 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2881129681/10000000000 : ℝ)^67 ≤ (609345916049/3125000000000 : ℝ)^51 := by
    have hnat : (2881129681 : ℕ)^67*3125000000000^51 ≤ 609345916049^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2881129681 10000000000 609345916049 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3354871283/10000000000 : ℝ)^67 ≤ (2976996352363/12500000000000 : ℝ)^51 := by
    have hnat : (3354871283 : ℕ)^67*12500000000000^51 ≤ 2976996352363^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3354871283 10000000000 2976996352363 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1622860549/2500000000 : ℝ), (-2881129681/10000000000 : ℝ), (-3354871283/10000000000 : ℝ)] ![(28342479925727/50000000000000 : ℝ), (609345916049/3125000000000 : ℝ), (2976996352363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1622860549/2500000000 : ℝ)|^67 ≤ (28342479925727/50000000000000 : ℝ)^51
        have hw : |(1622860549/2500000000 : ℝ)|=(1622860549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2881129681/10000000000 : ℝ)|^67 ≤ (609345916049/3125000000000 : ℝ)^51
        have hw : |(-2881129681/10000000000 : ℝ)|=(2881129681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3354871283/10000000000 : ℝ)|^67 ≤ (2976996352363/12500000000000 : ℝ)^51
        have hw : |(-3354871283/10000000000 : ℝ)|=(3354871283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (30459389/78125000 : ℝ)*x 0 + (2608553863/5000000000 : ℝ)*x 1 + (480112353/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30459389/78125000 : ℝ)^67 ≤ (1160528539583/4000000000000 : ℝ)^51 := by
    have hnat : (30459389 : ℕ)^67*4000000000000^51 ≤ 1160528539583^51*78125000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30459389 78125000 1160528539583 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608553863/5000000000 : ℝ)^67 ≤ (42538319734859/100000000000000 : ℝ)^51 := by
    have hnat : (2608553863 : ℕ)^67*100000000000000^51 ≤ 42538319734859^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608553863 5000000000 42538319734859 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480112353/1250000000 : ℝ)^67 ≤ (14224233376531/50000000000000 : ℝ)^51 := by
    have hnat : (480112353 : ℕ)^67*50000000000000^51 ≤ 14224233376531^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480112353 1250000000 14224233376531 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30459389/78125000 : ℝ), (2608553863/5000000000 : ℝ), (480112353/1250000000 : ℝ)] ![(1160528539583/4000000000000 : ℝ), (42538319734859/100000000000000 : ℝ), (14224233376531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30459389/78125000 : ℝ)|^67 ≤ (1160528539583/4000000000000 : ℝ)^51
        have hw : |(30459389/78125000 : ℝ)|=(30459389/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608553863/5000000000 : ℝ)|^67 ≤ (42538319734859/100000000000000 : ℝ)^51
        have hw : |(2608553863/5000000000 : ℝ)|=(2608553863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(480112353/1250000000 : ℝ)|^67 ≤ (14224233376531/50000000000000 : ℝ)^51
        have hw : |(480112353/1250000000 : ℝ)|=(480112353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305079_s1_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (768088173/2000000000 : ℝ)*x 0 + (39051777/80000000 : ℝ)*x 1 + (-1064537829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (768088173/2000000000 : ℝ)^67 ≤ (7111002678217/25000000000000 : ℝ)^51 := by
    have hnat : (768088173 : ℕ)^67*25000000000000^51 ≤ 7111002678217^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768088173 2000000000 7111002678217 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39051777/80000000 : ℝ)^67 ≤ (19489974430669/50000000000000 : ℝ)^51 := by
    have hnat : (39051777 : ℕ)^67*50000000000000^51 ≤ 19489974430669^51*80000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39051777 80000000 19489974430669 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064537829/2500000000 : ℝ)^67 ≤ (32576040412879/100000000000000 : ℝ)^51 := by
    have hnat : (1064537829 : ℕ)^67*100000000000000^51 ≤ 32576040412879^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064537829 2500000000 32576040412879 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(768088173/2000000000 : ℝ), (39051777/80000000 : ℝ), (-1064537829/2500000000 : ℝ)] ![(7111002678217/25000000000000 : ℝ), (19489974430669/50000000000000 : ℝ), (32576040412879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(768088173/2000000000 : ℝ)|^67 ≤ (7111002678217/25000000000000 : ℝ)^51
        have hw : |(768088173/2000000000 : ℝ)|=(768088173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39051777/80000000 : ℝ)|^67 ≤ (19489974430669/50000000000000 : ℝ)^51
        have hw : |(39051777/80000000 : ℝ)|=(39051777/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064537829/2500000000 : ℝ)|^67 ≤ (32576040412879/100000000000000 : ℝ)^51
        have hw : |(-1064537829/2500000000 : ℝ)|=(1064537829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305079 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4065982499/5000000000 : ℝ)*X 1 0+(-307672103/2000000000 : ℝ)*X 1 1+(-2388001569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1620478271/5000000000 : ℝ)*X 2 0+(6045716793/10000000000 : ℝ)*X 2 1+(709176251/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1702509421/10000000000 : ℝ)*X 0 0+(734137781/2500000000 : ℝ)*X 0 1+(-1910507971/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2017745017/2500000000 : ℝ)*X 1 0+(-294082017/10000000000 : ℝ)*X 1 1+(-1663993567/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1448215877/10000000000 : ℝ)*X 2 0+(7930112539/10000000000 : ℝ)*X 2 1+(688165723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1199791743/5000000000 : ℝ)*X 0 0+(1902633813/2500000000 : ℝ)*X 0 1+(-1168317361/5000000000 : ℝ)*X 0 2+(1199791743/5000000000 : ℝ)*X 1 0+(1902633813/2500000000 : ℝ)*X 1 1+(-1168317361/5000000000 : ℝ)*X 1 2+(1199791743/5000000000 : ℝ)*X 2 0+(1902633813/2500000000 : ℝ)*X 2 1+(-1168317361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-304598559/10000000000 : ℝ)*X 0 0+(3587245987/10000000000 : ℝ)*X 0 1+(-7867724037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((58167829/62500000 : ℝ)*X 1 0+(-1174969741/10000000000 : ℝ)*X 1 1+(-693761489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((15769059/40000000 : ℝ)*X 2 0+(2934924827/5000000000 : ℝ)*X 2 1+(3037095489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((268445799/1000000000 : ℝ)*X 0 0+(3270703627/10000000000 : ℝ)*X 0 1+(-6709228407/10000000000 : ℝ)*X 0 2+(268445799/1000000000 : ℝ)*X 1 0+(3270703627/10000000000 : ℝ)*X 1 1+(-6709228407/10000000000 : ℝ)*X 1 2+(268445799/1000000000 : ℝ)*X 2 0+(3270703627/10000000000 : ℝ)*X 2 1+(-6709228407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-223654421/5000000000 : ℝ)*X 0 0+(5735358449/10000000000 : ℝ)*X 0 1+(-2956242147/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((9639118449/10000000000 : ℝ)*X 1 0+(-345291917/10000000000 : ℝ)*X 1 1+(-781561409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2618702359/10000000000 : ℝ)*X 2 0+(618417629/1000000000 : ℝ)*X 2 1+(792013083/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((2215664073/5000000000 : ℝ)*X 0 0+(1334429577/2500000000 : ℝ)*X 0 1+(-3140552069/10000000000 : ℝ)*X 0 2+(2215664073/5000000000 : ℝ)*X 1 0+(1334429577/2500000000 : ℝ)*X 1 1+(-3140552069/10000000000 : ℝ)*X 1 2+(2215664073/5000000000 : ℝ)*X 2 0+(1334429577/2500000000 : ℝ)*X 2 1+(-3140552069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((43341/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43341/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26042886195580481750529/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46369/500000000000 : ℝ)*(base18) + (725048760153/1000000000000 : ℝ)*(base39) + (470238803257/500000000000 : ℝ)*(base49) + (8312599/1000000000000 : ℝ)*(base53) + (297319585433/500000000000 : ℝ)*(base60) + (2606616771651/1000000000000 : ℝ)*(major_s0_0) + (2606616771651/1000000000000 : ℝ)*(major_s0_1) + (651652114763/250000000000 : ℝ)*(major_s0_2) + (17794983/500000000000 : ℝ)*(sp_s0_1) + (1754357714129/500000000000 : ℝ)*(sp_s0_7) + (350871287799/100000000000 : ℝ)*(sp_s0_8) + (877189218323/250000000000 : ℝ)*(sp_s0_9) + (106529574851/62500000000 : ℝ)*(sp_s0_13) + (6626487/200000000000 : ℝ)*(sp_s0_14) + (106529574851/62500000000 : ℝ)*(f.failure) + (877189218323/250000000000 : ℝ)*(f.sum) + (3646216753696363/10000000000000000000000000000 : ℝ)*base63 + (1665669071893589/2500000000000000000000000000 : ℝ)*base65 + (1527070607045979/5000000000000000000000000000 : ℝ)*base66 + (708287618756573/1250000000000000000000000000 : ℝ)*base68 + (3248853538833157/5000000000000000000000000000 : ℝ)*base71 + (3330835533251053/10000000000000000000000000000 : ℝ)*base73 + (6742998072748947/10000000000000000000000000000 : ℝ)*base75 + (2759007256545979/5000000000000000000000000000 : ℝ)*base77 + (88867124431819/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (2511/3125000000000000 : ℝ)*base86 + (2511/3125000000000000 : ℝ)*base88 + (2511/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((56109/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(56109/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4044044005294318047663/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (548245460093/500000000000 : ℝ)*(base39) + (588813/200000000000 : ℝ)*(base40) + (136518481469/250000000000 : ℝ)*(base49) + (780402325857/1000000000000 : ℝ)*(base60) + (1580754620983/500000000000 : ℝ)*(major_s0_0) + (1580754620983/500000000000 : ℝ)*(major_s0_1) + (1580754620983/500000000000 : ℝ)*(major_s0_2) + (11033793/1000000000000 : ℝ)*(sp_s0_1) + (11928521/500000000000 : ℝ)*(sp_s0_7) + (4255673704389/1000000000000 : ℝ)*(sp_s0_14) + (4255631866897/1000000000000 : ℝ)*(sp_s0_15) + (4255697561431/1000000000000 : ℝ)*(sp_s0_16) + (2067318765671/1000000000000 : ℝ)*(sp_s0_20) + (27330371/500000000000 : ℝ)*(sp_s0_22) + (2067318765671/1000000000000 : ℝ)*(f.failure) + (4255697561431/1000000000000 : ℝ)*(f.sum) + (373793945201473/1000000000000000000000000000 : ℝ)*base63 + (1079157759095751/5000000000000000000000000000 : ℝ)*base64 + (1004554085205807/2500000000000000000000000000 : ℝ)*base66 + (547166995794193/2500000000000000000000000000 : ℝ)*base68 + (374817961184137/5000000000000000000000000000 : ℝ)*base70 + (1298951112595751/5000000000000000000000000000 : ℝ)*base72 + (176971944904249/5000000000000000000000000000 : ℝ)*base74 + (1038893591955807/2500000000000000000000000000 : ℝ)*base77 + (268890127101473/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (2041/3125000000000000 : ℝ)*base86 + (2041/3125000000000000 : ℝ)*base88 + (2041/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22209/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-22209/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1200072621224889/156250000000000000000 : ℝ) := by norm_num
    linear_combination (3472229/1000000000000 : ℝ)*(base11) + (956422702129/1000000000000 : ℝ)*(base39) + (583198021681/1000000000000 : ℝ)*(base49) + (155867/100000000000 : ℝ)*(base50) + (492855067349/200000000000 : ℝ)*(major_s0_0) + (492855067349/200000000000 : ℝ)*(major_s0_1) + (492855067349/200000000000 : ℝ)*(major_s0_2) + (85600411/1000000000000 : ℝ)*(sp_s0_2) + (15804793/1000000000000 : ℝ)*(sp_s0_9) + (79947/62500000000 : ℝ)*(sp_s0_15) + (1658574431103/500000000000 : ℝ)*(sp_s0_21) + (3317151055283/1000000000000 : ℝ)*(sp_s0_22) + (3317050929231/1000000000000 : ℝ)*(sp_s0_23) + (1611395778893/1000000000000 : ℝ)*(sp_s0_27) + (1611395778893/1000000000000 : ℝ)*(f.failure) + (829288083609/250000000000 : ℝ)*(f.sum) + (55471300199181/400000000000000000000000000 : ℝ)*base62 + (906902343565947/2000000000000000000000000000 : ℝ)*base65 + (409000549585021/1000000000000000000000000000 : ℝ)*base66 + (581687795185021/1000000000000000000000000000 : ℝ)*base69 + (419908993664011/2000000000000000000000000000 : ℝ)*base70 + (193661210434053/2000000000000000000000000000 : ℝ)*base72 + (354304242834053/2000000000000000000000000000 : ℝ)*base75 + (399267029285021/1000000000000000000000000000 : ℝ)*base77 + (48663286799181/400000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (761/1562500000000000 : ℝ)*base87 + (761/1562500000000000 : ℝ)*base89 + (761/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (43341/100000 : ℝ) ^ (133/32 : ℝ) ≤ (1548214646897407921/50000000000000000000 : ℝ) := by
    have hpowers : (43341/100000 : ℝ)^133 ≤ (1548214646897407921/50000000000000000000 : ℝ)^32 := by
      have hnat : (43341 : ℕ)^133*50000000000000000000^32 ≤ 1548214646897407921^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43341 100000 1548214646897407921 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43341/100000 : ℝ)) (X := (1548214646897407921/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (51548214646897407921/50000000000000000000 : ℝ) ≤ (314801256770529/312500000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (51548214646897407921/50000000000000000000 : ℝ)^32 ≤ (314801256770529/312500000000000 : ℝ)^133 := by
      have hnat : (51548214646897407921 : ℕ)^32*312500000000000^133 ≤ 314801256770529^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51548214646897407921 50000000000000000000 314801256770529 312500000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314801256770529/312500000000000 : ℝ)) (X := (51548214646897407921/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (26548214646897407921/25000000000000000000 : ℝ) ≤ (5072809757746507/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (26548214646897407921/25000000000000000000 : ℝ)^32 ≤ (5072809757746507/5000000000000000 : ℝ)^133 := by
      have hnat : (26548214646897407921 : ℕ)^32*5000000000000000^133 ≤ 5072809757746507^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26548214646897407921 25000000000000000000 5072809757746507 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5072809757746507/5000000000000000 : ℝ)) (X := (26548214646897407921/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2301256770529/135440625000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(35989649418043/2167050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (43341/100000 : ℝ)) (alpha := (2301256770529/135440625000000 : ℝ)) (beta := (35989649418043/2167050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (43341/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2301256770529/135440625000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(35989649418043/2167050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (56109/100000 : ℝ) ^ (133/32 : ℝ) ≤ (9055583654828723811/100000000000000000000 : ℝ) := by
    have hpowers : (56109/100000 : ℝ)^133 ≤ (9055583654828723811/100000000000000000000 : ℝ)^32 := by
      have hnat : (56109 : ℕ)^133*100000000000000000000^32 ≤ 9055583654828723811^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56109 100000 9055583654828723811 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (56109/100000 : ℝ)) (X := (9055583654828723811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (109055583654828723811/100000000000000000000 : ℝ) ≤ (10210761751713851/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (109055583654828723811/100000000000000000000 : ℝ)^32 ≤ (10210761751713851/10000000000000000 : ℝ)^133 := by
      have hnat : (109055583654828723811 : ℕ)^32*10000000000000000^133 ≤ 10210761751713851^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109055583654828723811 100000000000000000000 10210761751713851 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10210761751713851/10000000000000000 : ℝ)) (X := (109055583654828723811/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (59055583654828723811/50000000000000000000 : ℝ) ≤ (2602155962171387/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (59055583654828723811/50000000000000000000 : ℝ)^32 ≤ (2602155962171387/2500000000000000 : ℝ)^133 := by
      have hnat : (59055583654828723811 : ℕ)^32*2500000000000000^133 ≤ 2602155962171387^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59055583654828723811 50000000000000000000 2602155962171387 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2602155962171387/2500000000000000 : ℝ)) (X := (59055583654828723811/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(210761751713851/5610900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(65954032323899/1870300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (56109/100000 : ℝ)) (alpha := (210761751713851/5610900000000000 : ℝ)) (beta := (65954032323899/1870300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (56109/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(210761751713851/5610900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(65954032323899/1870300000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (22209/50000 : ℝ) ^ (133/32 : ℝ) ≤ (3428996902270324881/100000000000000000000 : ℝ) := by
    have hpowers : (22209/50000 : ℝ)^133 ≤ (3428996902270324881/100000000000000000000 : ℝ)^32 := by
      have hnat : (22209 : ℕ)^133*100000000000000000000^32 ≤ 3428996902270324881^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22209 50000 3428996902270324881 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22209/50000 : ℝ)) (X := (3428996902270324881/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (103428996902270324881/100000000000000000000 : ℝ) ≤ (10081449116250679/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (103428996902270324881/100000000000000000000 : ℝ)^32 ≤ (10081449116250679/10000000000000000 : ℝ)^133 := by
      have hnat : (103428996902270324881 : ℕ)^32*10000000000000000^133 ≤ 10081449116250679^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103428996902270324881 100000000000000000000 10081449116250679 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10081449116250679/10000000000000000 : ℝ)) (X := (103428996902270324881/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (53428996902270324881/50000000000000000000 : ℝ) ≤ (10160872725269089/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (53428996902270324881/50000000000000000000 : ℝ)^32 ≤ (10160872725269089/10000000000000000 : ℝ)^133 := by
      have hnat : (53428996902270324881 : ℕ)^32*10000000000000000^133 ≤ 10160872725269089^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53428996902270324881 50000000000000000000 10160872725269089 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10160872725269089/10000000000000000 : ℝ)) (X := (53428996902270324881/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(27149705416893/1480600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2647453633947/148060000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (22209/50000 : ℝ)) (alpha := (27149705416893/1480600000000000 : ℝ)) (beta := (2647453633947/148060000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (22209/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(27149705416893/1480600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2647453633947/148060000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2685400567/10000000000 : ℝ)*X 0 0+(446844957/1000000000 : ℝ)*X 0 1+(-1135131361/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1622860549/2500000000 : ℝ)*X 1 0+(-2881129681/10000000000 : ℝ)*X 1 1+(-3354871283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((30459389/78125000 : ℝ)*X 2 0+(2608553863/5000000000 : ℝ)*X 2 1+(480112353/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((768088173/2000000000 : ℝ)*X 0 0+(39051777/80000000 : ℝ)*X 0 1+(-1064537829/2500000000 : ℝ)*X 0 2+(768088173/2000000000 : ℝ)*X 1 0+(39051777/80000000 : ℝ)*X 1 1+(-1064537829/2500000000 : ℝ)*X 1 2+(768088173/2000000000 : ℝ)*X 2 0+(39051777/80000000 : ℝ)*X 2 1+(-1064537829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-2600507052172194331206590050019889/423793896212500000000000000000000 : ℝ) := by norm_num
    linear_combination (843/62500000000 : ℝ)*(base12) + (6381/125000000000 : ℝ)*(base15) + (3589/250000000000 : ℝ)*(base25) + (195927843163/500000000000 : ℝ)*(base39) + (146919815719/500000000000 : ℝ)*(base49) + (191/500000000000 : ℝ)*(base50) + (7724652173/50000000000 : ℝ)*(base60) + (764640003249/500000000000 : ℝ)*(major_s1_0) + (4779/3125 : ℝ)*(major_s1_1) + (4779/3125 : ℝ)*(major_s1_2) + (1022709007639/500000000000 : ℝ)*(sp_s1_0) + (2045417984217/1000000000000 : ℝ)*(sp_s1_1) + (2045418020909/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1022709014383/500000000000 : ℝ)*(f.sum) + (8076637966714063/11733755000000000000000000000 : ℝ)*base63 + (1020217149769/3701500000000000000000000 : ℝ)*base64 + (89789462757/317000000000000000000000 : ℝ)*base66 + (7468301849599/18507500000000000000000000 : ℝ)*base68 + (1148960591972060543/5347557050000000000000000000000 : ℝ)*base70 + (189858956069723/722350000000000000000000000 : ℝ)*base73 + (3060578517/24765625000000000000000 : ℝ)*base74 + (50079185442233/361175000000000000000000000 : ℝ)*base76 + (17458294418400087/114492475000000000000000000000 : ℝ)*base78 + (6499/1000000000000 : ℝ)*base83 + (6499/1000000000000 : ℝ)*base85 + (3249/500000000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p005_b035 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c305079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c305080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

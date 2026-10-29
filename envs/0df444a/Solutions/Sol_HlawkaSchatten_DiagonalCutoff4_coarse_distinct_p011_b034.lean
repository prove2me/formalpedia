-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p011_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:59:04.51398+00:00
-- url     : https://prove2.me/submissions/07724a4a-30e2-4840-8f74-d7b741f0bd8d

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311080_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311080_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311080_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c311080 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c311080_s0 p hpa hpb X hX
  have h1 := collision_c311080_s1 p hpa hpb X hX h0
  exact collision_c311080_s2 p hpa hpb X hX h1

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
theorem collision_support_c311079_s0_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (8026212287/10000000000 : ℝ)*x 0 + (-1527057519/10000000000 : ℝ)*x 1 + (-592240859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8026212287/10000000000 : ℝ)^9 ≤ (1177736120119/1562500000000 : ℝ)^7 := by
    have hnat : (8026212287 : ℕ)^9*1562500000000^7 ≤ 1177736120119^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8026212287 10000000000 1177736120119 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1527057519/10000000000 : ℝ)^9 ≤ (8926294745279/100000000000000 : ℝ)^7 := by
    have hnat : (1527057519 : ℕ)^9*100000000000000^7 ≤ 8926294745279^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1527057519 10000000000 8926294745279 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592240859/2500000000 : ℝ)^9 ≤ (7849296777771/50000000000000 : ℝ)^7 := by
    have hnat : (592240859 : ℕ)^9*50000000000000^7 ≤ 7849296777771^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592240859 2500000000 7849296777771 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8026212287/10000000000 : ℝ), (-1527057519/10000000000 : ℝ), (-592240859/2500000000 : ℝ)] ![(1177736120119/1562500000000 : ℝ), (8926294745279/100000000000000 : ℝ), (7849296777771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8026212287/10000000000 : ℝ)|^9 ≤ (1177736120119/1562500000000 : ℝ)^7
        have hw : |(8026212287/10000000000 : ℝ)|=(8026212287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1527057519/10000000000 : ℝ)|^9 ≤ (8926294745279/100000000000000 : ℝ)^7
        have hw : |(-1527057519/10000000000 : ℝ)|=(1527057519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-592240859/2500000000 : ℝ)|^9 ≤ (7849296777771/50000000000000 : ℝ)^7
        have hw : |(-592240859/2500000000 : ℝ)|=(592240859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (126329659/400000000 : ℝ)*x 0 + (238715579/400000000 : ℝ)*x 1 + (1742299429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126329659/400000000 : ℝ)^9 ≤ (22721118841497/100000000000000 : ℝ)^7 := by
    have hnat : (126329659 : ℕ)^9*100000000000000^7 ≤ 22721118841497^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126329659 400000000 22721118841497 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238715579/400000000 : ℝ)^9 ≤ (25747766833961/50000000000000 : ℝ)^7 := by
    have hnat : (238715579 : ℕ)^9*50000000000000^7 ≤ 25747766833961^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238715579 400000000 25747766833961 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1742299429/5000000000 : ℝ)^9 ≤ (12891673733187/50000000000000 : ℝ)^7 := by
    have hnat : (1742299429 : ℕ)^9*50000000000000^7 ≤ 12891673733187^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742299429 5000000000 12891673733187 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(126329659/400000000 : ℝ), (238715579/400000000 : ℝ), (1742299429/5000000000 : ℝ)] ![(22721118841497/100000000000000 : ℝ), (25747766833961/50000000000000 : ℝ), (12891673733187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(126329659/400000000 : ℝ)|^9 ≤ (22721118841497/100000000000000 : ℝ)^7
        have hw : |(126329659/400000000 : ℝ)|=(126329659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238715579/400000000 : ℝ)|^9 ≤ (25747766833961/50000000000000 : ℝ)^7
        have hw : |(238715579/400000000 : ℝ)|=(238715579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1742299429/5000000000 : ℝ)|^9 ≤ (12891673733187/50000000000000 : ℝ)^7
        have hw : |(1742299429/5000000000 : ℝ)|=(1742299429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-436302371/2500000000 : ℝ)*x 0 + (598273991/2000000000 : ℝ)*x 1 + (-7426471431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436302371/2500000000 : ℝ)^9 ≤ (10598211516627/100000000000000 : ℝ)^7 := by
    have hnat : (436302371 : ℕ)^9*100000000000000^7 ≤ 10598211516627^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436302371 2500000000 10598211516627 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598273991/2000000000 : ℝ)^9 ≤ (10594701848201/50000000000000 : ℝ)^7 := by
    have hnat : (598273991 : ℕ)^9*50000000000000^7 ≤ 10594701848201^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598273991 2000000000 10594701848201 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7426471431/10000000000 : ℝ)^9 ≤ (34106192387809/50000000000000 : ℝ)^7 := by
    have hnat : (7426471431 : ℕ)^9*50000000000000^7 ≤ 34106192387809^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7426471431 10000000000 34106192387809 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436302371/2500000000 : ℝ), (598273991/2000000000 : ℝ), (-7426471431/10000000000 : ℝ)] ![(10598211516627/100000000000000 : ℝ), (10594701848201/50000000000000 : ℝ), (34106192387809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436302371/2500000000 : ℝ)|^9 ≤ (10598211516627/100000000000000 : ℝ)^7
        have hw : |(-436302371/2500000000 : ℝ)|=(436302371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598273991/2000000000 : ℝ)|^9 ≤ (10594701848201/50000000000000 : ℝ)^7
        have hw : |(598273991/2000000000 : ℝ)|=(598273991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7426471431/10000000000 : ℝ)|^9 ≤ (34106192387809/50000000000000 : ℝ)^7
        have hw : |(-7426471431/10000000000 : ℝ)|=(7426471431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (8039547299/10000000000 : ℝ)*x 0 + (-165729273/5000000000 : ℝ)*x 1 + (-3211139657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8039547299/10000000000 : ℝ)^9 ≤ (37768080380871/50000000000000 : ℝ)^7 := by
    have hnat : (8039547299 : ℕ)^9*50000000000000^7 ≤ 37768080380871^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8039547299 10000000000 37768080380871 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165729273/5000000000 : ℝ)^9 ≤ (1252260588649/100000000000000 : ℝ)^7 := by
    have hnat : (165729273 : ℕ)^9*100000000000000^7 ≤ 1252260588649^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165729273 5000000000 1252260588649 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3211139657/10000000000 : ℝ)^9 ≤ (23211578632623/100000000000000 : ℝ)^7 := by
    have hnat : (3211139657 : ℕ)^9*100000000000000^7 ≤ 23211578632623^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3211139657 10000000000 23211578632623 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8039547299/10000000000 : ℝ), (-165729273/5000000000 : ℝ), (-3211139657/10000000000 : ℝ)] ![(37768080380871/50000000000000 : ℝ), (1252260588649/100000000000000 : ℝ), (23211578632623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8039547299/10000000000 : ℝ)|^9 ≤ (37768080380871/50000000000000 : ℝ)^7
        have hw : |(8039547299/10000000000 : ℝ)|=(8039547299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-165729273/5000000000 : ℝ)|^9 ≤ (1252260588649/100000000000000 : ℝ)^7
        have hw : |(-165729273/5000000000 : ℝ)|=(165729273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3211139657/10000000000 : ℝ)|^9 ≤ (23211578632623/100000000000000 : ℝ)^7
        have hw : |(-3211139657/10000000000 : ℝ)|=(3211139657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (753541573/5000000000 : ℝ)*x 0 + (15509859/20000000 : ℝ)*x 1 + (2760233209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (753541573/5000000000 : ℝ)^9 ≤ (8776457900983/100000000000000 : ℝ)^7 := by
    have hnat : (753541573 : ℕ)^9*100000000000000^7 ≤ 8776457900983^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753541573 5000000000 8776457900983 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15509859/20000000 : ℝ)^9 ≤ (7211550837983/10000000000000 : ℝ)^7 := by
    have hnat : (15509859 : ℕ)^9*10000000000000^7 ≤ 7211550837983^7*20000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15509859 20000000 7211550837983 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760233209/10000000000 : ℝ)^9 ≤ (19108033700651/100000000000000 : ℝ)^7 := by
    have hnat : (2760233209 : ℕ)^9*100000000000000^7 ≤ 19108033700651^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760233209 10000000000 19108033700651 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(753541573/5000000000 : ℝ), (15509859/20000000 : ℝ), (2760233209/10000000000 : ℝ)] ![(8776457900983/100000000000000 : ℝ), (7211550837983/10000000000000 : ℝ), (19108033700651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(753541573/5000000000 : ℝ)|^9 ≤ (8776457900983/100000000000000 : ℝ)^7
        have hw : |(753541573/5000000000 : ℝ)|=(753541573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15509859/20000000 : ℝ)|^9 ≤ (7211550837983/10000000000000 : ℝ)^7
        have hw : |(15509859/20000000 : ℝ)|=(15509859/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760233209/10000000000 : ℝ)|^9 ≤ (19108033700651/100000000000000 : ℝ)^7
        have hw : |(2760233209/10000000000 : ℝ)|=(2760233209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (600548249/2500000000 : ℝ)*x 0 + (7535210591/10000000000 : ℝ)*x 1 + (-2229265949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600548249/2500000000 : ℝ)^9 ≤ (15982279592843/100000000000000 : ℝ)^7 := by
    have hnat : (600548249 : ℕ)^9*100000000000000^7 ≤ 15982279592843^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600548249 2500000000 15982279592843 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7535210591/10000000000 : ℝ)^9 ≤ (69499197950149/100000000000000 : ℝ)^7 := by
    have hnat : (7535210591 : ℕ)^9*100000000000000^7 ≤ 69499197950149^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7535210591 10000000000 69499197950149 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229265949/10000000000 : ℝ)^9 ≤ (14518522443393/100000000000000 : ℝ)^7 := by
    have hnat : (2229265949 : ℕ)^9*100000000000000^7 ≤ 14518522443393^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229265949 10000000000 14518522443393 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(600548249/2500000000 : ℝ), (7535210591/10000000000 : ℝ), (-2229265949/10000000000 : ℝ)] ![(15982279592843/100000000000000 : ℝ), (69499197950149/100000000000000 : ℝ), (14518522443393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(600548249/2500000000 : ℝ)|^9 ≤ (15982279592843/100000000000000 : ℝ)^7
        have hw : |(600548249/2500000000 : ℝ)|=(600548249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7535210591/10000000000 : ℝ)|^9 ≤ (69499197950149/100000000000000 : ℝ)^7
        have hw : |(7535210591/10000000000 : ℝ)|=(7535210591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229265949/10000000000 : ℝ)|^9 ≤ (14518522443393/100000000000000 : ℝ)^7
        have hw : |(-2229265949/10000000000 : ℝ)|=(2229265949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-329947053/10000000000 : ℝ)*x 0 + (3583022839/10000000000 : ℝ)*x 1 + (-7747913967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329947053/10000000000 : ℝ)^9 ≤ (248984669539/20000000000000 : ℝ)^7 := by
    have hnat : (329947053 : ℕ)^9*20000000000000^7 ≤ 248984669539^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329947053 10000000000 248984669539 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3583022839/10000000000 : ℝ)^9 ≤ (3340429617197/12500000000000 : ℝ)^7 := by
    have hnat : (3583022839 : ℕ)^9*12500000000000^7 ≤ 3340429617197^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3583022839 10000000000 3340429617197 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7747913967/10000000000 : ℝ)^9 ≤ (14406327939713/20000000000000 : ℝ)^7 := by
    have hnat : (7747913967 : ℕ)^9*20000000000000^7 ≤ 14406327939713^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7747913967 10000000000 14406327939713 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-329947053/10000000000 : ℝ), (3583022839/10000000000 : ℝ), (-7747913967/10000000000 : ℝ)] ![(248984669539/20000000000000 : ℝ), (3340429617197/12500000000000 : ℝ), (14406327939713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-329947053/10000000000 : ℝ)|^9 ≤ (248984669539/20000000000000 : ℝ)^7
        have hw : |(-329947053/10000000000 : ℝ)|=(329947053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3583022839/10000000000 : ℝ)|^9 ≤ (3340429617197/12500000000000 : ℝ)^7
        have hw : |(3583022839/10000000000 : ℝ)|=(3583022839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7747913967/10000000000 : ℝ)|^9 ≤ (14406327939713/20000000000000 : ℝ)^7
        have hw : |(-7747913967/10000000000 : ℝ)|=(7747913967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2283515803/2500000000 : ℝ)*x 0 + (-32511443/250000000 : ℝ)*x 1 + (-774984483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2283515803/2500000000 : ℝ)^9 ≤ (5562950258213/6250000000000 : ℝ)^7 := by
    have hnat : (2283515803 : ℕ)^9*6250000000000^7 ≤ 5562950258213^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283515803 2500000000 5562950258213 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32511443/250000000 : ℝ)^9 ≤ (907592481083/12500000000000 : ℝ)^7 := by
    have hnat : (32511443 : ℕ)^9*12500000000000^7 ≤ 907592481083^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32511443 250000000 907592481083 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774984483/10000000000 : ℝ)^9 ≤ (3732056000783/100000000000000 : ℝ)^7 := by
    have hnat : (774984483 : ℕ)^9*100000000000000^7 ≤ 3732056000783^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774984483 10000000000 3732056000783 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2283515803/2500000000 : ℝ), (-32511443/250000000 : ℝ), (-774984483/10000000000 : ℝ)] ![(5562950258213/6250000000000 : ℝ), (907592481083/12500000000000 : ℝ), (3732056000783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2283515803/2500000000 : ℝ)|^9 ≤ (5562950258213/6250000000000 : ℝ)^7
        have hw : |(2283515803/2500000000 : ℝ)|=(2283515803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32511443/250000000 : ℝ)|^9 ≤ (907592481083/12500000000000 : ℝ)^7
        have hw : |(-32511443/250000000 : ℝ)|=(32511443/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-774984483/10000000000 : ℝ)|^9 ≤ (3732056000783/100000000000000 : ℝ)^7
        have hw : |(-774984483/10000000000 : ℝ)|=(774984483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3770158117/10000000000 : ℝ)*x 0 + (586542081/1000000000 : ℝ)*x 1 + (2982351693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3770158117/10000000000 : ℝ)^9 ≤ (14265580355321/50000000000000 : ℝ)^7 := by
    have hnat : (3770158117 : ℕ)^9*50000000000000^7 ≤ 14265580355321^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3770158117 10000000000 14265580355321 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586542081/1000000000 : ℝ)^9 ≤ (314759580271/625000000000 : ℝ)^7 := by
    have hnat : (586542081 : ℕ)^9*625000000000^7 ≤ 314759580271^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586542081 1000000000 314759580271 625000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2982351693/10000000000 : ℝ)^9 ≤ (21107306427687/100000000000000 : ℝ)^7 := by
    have hnat : (2982351693 : ℕ)^9*100000000000000^7 ≤ 21107306427687^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982351693 10000000000 21107306427687 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3770158117/10000000000 : ℝ), (586542081/1000000000 : ℝ), (2982351693/10000000000 : ℝ)] ![(14265580355321/50000000000000 : ℝ), (314759580271/625000000000 : ℝ), (21107306427687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3770158117/10000000000 : ℝ)|^9 ≤ (14265580355321/50000000000000 : ℝ)^7
        have hw : |(3770158117/10000000000 : ℝ)|=(3770158117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586542081/1000000000 : ℝ)|^9 ≤ (314759580271/625000000000 : ℝ)^7
        have hw : |(586542081/1000000000 : ℝ)|=(586542081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2982351693/10000000000 : ℝ)|^9 ≤ (21107306427687/100000000000000 : ℝ)^7
        have hw : |(2982351693/10000000000 : ℝ)|=(2982351693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_17 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4999999953/5000000000 : ℝ)*x 0 + (3469/5000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4999999953/5000000000 : ℝ)^9 ≤ (99999998791429/100000000000000 : ℝ)^7 := by
    have hnat : (4999999953 : ℕ)^9*100000000000000^7 ≤ 99999998791429^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999953 5000000000 99999998791429 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3469/5000000000 : ℝ)^9 ≤ (603333/50000000000000 : ℝ)^7 := by
    have hnat : (3469 : ℕ)^9*50000000000000^7 ≤ 603333^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3469 5000000000 603333 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^9 ≤ (0 : ℝ)^7 := by
    have hnat : (0 : ℕ)^9*1^7 ≤ 0^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4999999953/5000000000 : ℝ), (3469/5000000000 : ℝ), (0 : ℝ)] ![(99999998791429/100000000000000 : ℝ), (603333/50000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4999999953/5000000000 : ℝ)|^9 ≤ (99999998791429/100000000000000 : ℝ)^7
        have hw : |(4999999953/5000000000 : ℝ)|=(4999999953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3469/5000000000 : ℝ)|^9 ≤ (603333/50000000000000 : ℝ)^7
        have hw : |(3469/5000000000 : ℝ)|=(3469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^9 ≤ (0 : ℝ)^7
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1301791959/5000000000 : ℝ)*x 0 + (413920659/1250000000 : ℝ)*x 1 + (-1639388283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301791959/5000000000 : ℝ)^9 ≤ (17725236227277/100000000000000 : ℝ)^7 := by
    have hnat : (1301791959 : ℕ)^9*100000000000000^7 ≤ 17725236227277^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301791959 5000000000 17725236227277 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413920659/1250000000 : ℝ)^9 ≤ (12073585519621/50000000000000 : ℝ)^7 := by
    have hnat : (413920659 : ℕ)^9*50000000000000^7 ≤ 12073585519621^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413920659 1250000000 12073585519621 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1639388283/2500000000 : ℝ)^9 ≤ (58127592718923/100000000000000 : ℝ)^7 := by
    have hnat : (1639388283 : ℕ)^9*100000000000000^7 ≤ 58127592718923^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639388283 2500000000 58127592718923 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301791959/5000000000 : ℝ), (413920659/1250000000 : ℝ), (-1639388283/2500000000 : ℝ)] ![(17725236227277/100000000000000 : ℝ), (12073585519621/50000000000000 : ℝ), (58127592718923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301791959/5000000000 : ℝ)|^9 ≤ (17725236227277/100000000000000 : ℝ)^7
        have hw : |(1301791959/5000000000 : ℝ)|=(1301791959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(413920659/1250000000 : ℝ)|^9 ≤ (12073585519621/50000000000000 : ℝ)^7
        have hw : |(413920659/1250000000 : ℝ)|=(413920659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1639388283/2500000000 : ℝ)|^9 ≤ (58127592718923/100000000000000 : ℝ)^7
        have hw : |(-1639388283/2500000000 : ℝ)|=(1639388283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-18043351/400000000 : ℝ)*x 0 + (5605226347/10000000000 : ℝ)*x 1 + (-1472462941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18043351/400000000 : ℝ)^9 ≤ (1861055244793/100000000000000 : ℝ)^7 := by
    have hnat : (18043351 : ℕ)^9*100000000000000^7 ≤ 1861055244793^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18043351 400000000 1861055244793 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5605226347/10000000000 : ℝ)^9 ≤ (38006039421/80000000000 : ℝ)^7 := by
    have hnat : (5605226347 : ℕ)^9*80000000000^7 ≤ 38006039421^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605226347 10000000000 38006039421 80000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1472462941/2500000000 : ℝ)^9 ≤ (10126279094629/20000000000000 : ℝ)^7 := by
    have hnat : (1472462941 : ℕ)^9*20000000000000^7 ≤ 10126279094629^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472462941 2500000000 10126279094629 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18043351/400000000 : ℝ), (5605226347/10000000000 : ℝ), (-1472462941/2500000000 : ℝ)] ![(1861055244793/100000000000000 : ℝ), (38006039421/80000000000 : ℝ), (10126279094629/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18043351/400000000 : ℝ)|^9 ≤ (1861055244793/100000000000000 : ℝ)^7
        have hw : |(-18043351/400000000 : ℝ)|=(18043351/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5605226347/10000000000 : ℝ)|^9 ≤ (38006039421/80000000000 : ℝ)^7
        have hw : |(5605226347/10000000000 : ℝ)|=(5605226347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1472462941/2500000000 : ℝ)|^9 ≤ (10126279094629/20000000000000 : ℝ)^7
        have hw : |(-1472462941/2500000000 : ℝ)|=(1472462941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (9554214623/10000000000 : ℝ)*x 0 + (-5721039/156250000 : ℝ)*x 1 + (-860774129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9554214623/10000000000 : ℝ)^9 ≤ (94305369160591/100000000000000 : ℝ)^7 := by
    have hnat : (9554214623 : ℕ)^9*100000000000000^7 ≤ 94305369160591^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9554214623 10000000000 94305369160591 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5721039/156250000 : ℝ)^9 ≤ (355803791479/25000000000000 : ℝ)^7 := by
    have hnat : (5721039 : ℕ)^9*25000000000000^7 ≤ 355803791479^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5721039 156250000 355803791479 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860774129/10000000000 : ℝ)^9 ≤ (854283132387/20000000000000 : ℝ)^7 := by
    have hnat : (860774129 : ℕ)^9*20000000000000^7 ≤ 854283132387^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860774129 10000000000 854283132387 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9554214623/10000000000 : ℝ), (-5721039/156250000 : ℝ), (-860774129/10000000000 : ℝ)] ![(94305369160591/100000000000000 : ℝ), (355803791479/25000000000000 : ℝ), (854283132387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9554214623/10000000000 : ℝ)|^9 ≤ (94305369160591/100000000000000 : ℝ)^7
        have hw : |(9554214623/10000000000 : ℝ)|=(9554214623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5721039/156250000 : ℝ)|^9 ≤ (355803791479/25000000000000 : ℝ)^7
        have hw : |(-5721039/156250000 : ℝ)|=(5721039/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-860774129/10000000000 : ℝ)|^9 ≤ (854283132387/20000000000000 : ℝ)^7
        have hw : |(-860774129/10000000000 : ℝ)|=(860774129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1289239257/5000000000 : ℝ)*x 0 + (3008178173/5000000000 : ℝ)*x 1 + (3966984991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1289239257/5000000000 : ℝ)^9 ≤ (8752893995937/50000000000000 : ℝ)^7 := by
    have hnat : (1289239257 : ℕ)^9*50000000000000^7 ≤ 8752893995937^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289239257 5000000000 8752893995937 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3008178173/5000000000 : ℝ)^9 ≤ (2081354162959/4000000000000 : ℝ)^7 := by
    have hnat : (3008178173 : ℕ)^9*4000000000000^7 ≤ 2081354162959^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008178173 5000000000 2081354162959 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3966984991/10000000000 : ℝ)^9 ≤ (30460357929967/100000000000000 : ℝ)^7 := by
    have hnat : (3966984991 : ℕ)^9*100000000000000^7 ≤ 30460357929967^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3966984991 10000000000 30460357929967 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1289239257/5000000000 : ℝ), (3008178173/5000000000 : ℝ), (3966984991/10000000000 : ℝ)] ![(8752893995937/50000000000000 : ℝ), (2081354162959/4000000000000 : ℝ), (30460357929967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1289239257/5000000000 : ℝ)|^9 ≤ (8752893995937/50000000000000 : ℝ)^7
        have hw : |(1289239257/5000000000 : ℝ)|=(1289239257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3008178173/5000000000 : ℝ)|^9 ≤ (2081354162959/4000000000000 : ℝ)^7
        have hw : |(3008178173/5000000000 : ℝ)|=(3008178173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3966984991/10000000000 : ℝ)|^9 ≤ (30460357929967/100000000000000 : ℝ)^7
        have hw : |(3966984991/10000000000 : ℝ)|=(3966984991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s0_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1022751581/2500000000 : ℝ)*x 0 + (2727071371/5000000000 : ℝ)*x 1 + (-3128055729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022751581/2500000000 : ℝ)^9 ≤ (15845081742429/50000000000000 : ℝ)^7 := by
    have hnat : (1022751581 : ℕ)^9*50000000000000^7 ≤ 15845081742429^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022751581 2500000000 15845081742429 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727071371/5000000000 : ℝ)^9 ≤ (9173509085253/20000000000000 : ℝ)^7 := by
    have hnat : (2727071371 : ℕ)^9*20000000000000^7 ≤ 9173509085253^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727071371 5000000000 9173509085253 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3128055729/10000000000 : ℝ)^9 ≤ (5610572769121/25000000000000 : ℝ)^7 := by
    have hnat : (3128055729 : ℕ)^9*25000000000000^7 ≤ 5610572769121^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3128055729 10000000000 5610572769121 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1022751581/2500000000 : ℝ), (2727071371/5000000000 : ℝ), (-3128055729/10000000000 : ℝ)] ![(15845081742429/50000000000000 : ℝ), (9173509085253/20000000000000 : ℝ), (5610572769121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1022751581/2500000000 : ℝ)|^9 ≤ (15845081742429/50000000000000 : ℝ)^7
        have hw : |(1022751581/2500000000 : ℝ)|=(1022751581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727071371/5000000000 : ℝ)|^9 ≤ (9173509085253/20000000000000 : ℝ)^7
        have hw : |(2727071371/5000000000 : ℝ)|=(2727071371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3128055729/10000000000 : ℝ)|^9 ≤ (5610572769121/25000000000000 : ℝ)^7
        have hw : |(-3128055729/10000000000 : ℝ)|=(3128055729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2640179343/10000000000 : ℝ)*x 0 + (4401412367/10000000000 : ℝ)*x 1 + (-1392848999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640179343/10000000000 : ℝ)^9 ≤ (18046202941851/100000000000000 : ℝ)^7 := by
    have hnat : (2640179343 : ℕ)^9*100000000000000^7 ≤ 18046202941851^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640179343 10000000000 18046202941851 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4401412367/10000000000 : ℝ)^9 ≤ (17407292363243/50000000000000 : ℝ)^7 := by
    have hnat : (4401412367 : ℕ)^9*50000000000000^7 ≤ 17407292363243^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401412367 10000000000 17407292363243 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392848999/2500000000 : ℝ)^9 ≤ (1178480308117/2500000000000 : ℝ)^7 := by
    have hnat : (1392848999 : ℕ)^9*2500000000000^7 ≤ 1178480308117^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392848999 2500000000 1178480308117 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2640179343/10000000000 : ℝ), (4401412367/10000000000 : ℝ), (-1392848999/2500000000 : ℝ)] ![(18046202941851/100000000000000 : ℝ), (17407292363243/50000000000000 : ℝ), (1178480308117/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2640179343/10000000000 : ℝ)|^9 ≤ (18046202941851/100000000000000 : ℝ)^7
        have hw : |(-2640179343/10000000000 : ℝ)|=(2640179343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4401412367/10000000000 : ℝ)|^9 ≤ (17407292363243/50000000000000 : ℝ)^7
        have hw : |(4401412367/10000000000 : ℝ)|=(4401412367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1392848999/2500000000 : ℝ)|^9 ≤ (1178480308117/2500000000000 : ℝ)^7
        have hw : |(-1392848999/2500000000 : ℝ)|=(1392848999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (320445489/500000000 : ℝ)*x 0 + (-347905681/1250000000 : ℝ)*x 1 + (-3322099711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (320445489/500000000 : ℝ)^9 ≤ (5643904177121/10000000000000 : ℝ)^7 := by
    have hnat : (320445489 : ℕ)^9*10000000000000^7 ≤ 5643904177121^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320445489 500000000 5643904177121 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347905681/1250000000 : ℝ)^9 ≤ (19313097729773/100000000000000 : ℝ)^7 := by
    have hnat : (347905681 : ℕ)^9*100000000000000^7 ≤ 19313097729773^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347905681 1250000000 19313097729773 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3322099711/10000000000 : ℝ)^9 ≤ (12123930237869/50000000000000 : ℝ)^7 := by
    have hnat : (3322099711 : ℕ)^9*50000000000000^7 ≤ 12123930237869^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3322099711 10000000000 12123930237869 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(320445489/500000000 : ℝ), (-347905681/1250000000 : ℝ), (-3322099711/10000000000 : ℝ)] ![(5643904177121/10000000000000 : ℝ), (19313097729773/100000000000000 : ℝ), (12123930237869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(320445489/500000000 : ℝ)|^9 ≤ (5643904177121/10000000000000 : ℝ)^7
        have hw : |(320445489/500000000 : ℝ)|=(320445489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-347905681/1250000000 : ℝ)|^9 ≤ (19313097729773/100000000000000 : ℝ)^7
        have hw : |(-347905681/1250000000 : ℝ)|=(347905681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3322099711/10000000000 : ℝ)|^9 ≤ (12123930237869/50000000000000 : ℝ)^7
        have hw : |(-3322099711/10000000000 : ℝ)|=(3322099711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s1_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3782961179/10000000000 : ℝ)*x 0 + (2578865033/5000000000 : ℝ)*x 1 + (3783022789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3782961179/10000000000 : ℝ)^9 ≤ (229246339611/800000000000 : ℝ)^7 := by
    have hnat : (3782961179 : ℕ)^9*800000000000^7 ≤ 229246339611^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3782961179 10000000000 229246339611 800000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2578865033/5000000000 : ℝ)^9 ≤ (21343907519857/50000000000000 : ℝ)^7 := by
    have hnat : (2578865033 : ℕ)^9*50000000000000^7 ≤ 21343907519857^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578865033 5000000000 21343907519857 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3783022789/10000000000 : ℝ)^9 ≤ (895512265227/3125000000000 : ℝ)^7 := by
    have hnat : (3783022789 : ℕ)^9*3125000000000^7 ≤ 895512265227^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3783022789 10000000000 895512265227 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3782961179/10000000000 : ℝ), (2578865033/5000000000 : ℝ), (3783022789/10000000000 : ℝ)] ![(229246339611/800000000000 : ℝ), (21343907519857/50000000000000 : ℝ), (895512265227/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3782961179/10000000000 : ℝ)|^9 ≤ (229246339611/800000000000 : ℝ)^7
        have hw : |(3782961179/10000000000 : ℝ)|=(3782961179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2578865033/5000000000 : ℝ)|^9 ≤ (21343907519857/50000000000000 : ℝ)^7
        have hw : |(2578865033/5000000000 : ℝ)|=(2578865033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3783022789/10000000000 : ℝ)|^9 ≤ (895512265227/3125000000000 : ℝ)^7
        have hw : |(3783022789/10000000000 : ℝ)|=(3783022789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311079_s1_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3760029363/10000000000 : ℝ)*x 0 + (4870828431/10000000000 : ℝ)*x 1 + (-4112853763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3760029363/10000000000 : ℝ)^9 ≤ (28432647709469/100000000000000 : ℝ)^7 := by
    have hnat : (3760029363 : ℕ)^9*100000000000000^7 ≤ 28432647709469^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760029363 10000000000 28432647709469 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4870828431/10000000000 : ℝ)^9 ≤ (19829716399859/50000000000000 : ℝ)^7 := by
    have hnat : (4870828431 : ℕ)^9*50000000000000^7 ≤ 19829716399859^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870828431 10000000000 19829716399859 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4112853763/10000000000 : ℝ)^9 ≤ (3988489934599/12500000000000 : ℝ)^7 := by
    have hnat : (4112853763 : ℕ)^9*12500000000000^7 ≤ 3988489934599^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112853763 10000000000 3988489934599 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3760029363/10000000000 : ℝ), (4870828431/10000000000 : ℝ), (-4112853763/10000000000 : ℝ)] ![(28432647709469/100000000000000 : ℝ), (19829716399859/50000000000000 : ℝ), (3988489934599/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3760029363/10000000000 : ℝ)|^9 ≤ (28432647709469/100000000000000 : ℝ)^7
        have hw : |(3760029363/10000000000 : ℝ)|=(3760029363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4870828431/10000000000 : ℝ)|^9 ≤ (19829716399859/50000000000000 : ℝ)^7
        have hw : |(4870828431/10000000000 : ℝ)|=(4870828431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4112853763/10000000000 : ℝ)|^9 ≤ (3988489934599/12500000000000 : ℝ)^7
        have hw : |(-4112853763/10000000000 : ℝ)|=(4112853763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311079 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
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
  have s0_pow0 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((8026212287/10000000000 : ℝ)*X 1 0+(-1527057519/10000000000 : ℝ)*X 1 1+(-592240859/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((126329659/400000000 : ℝ)*X 2 0+(238715579/400000000 : ℝ)*X 2 1+(1742299429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-436302371/2500000000 : ℝ)*X 0 0+(598273991/2000000000 : ℝ)*X 0 1+(-7426471431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((8039547299/10000000000 : ℝ)*X 1 0+(-165729273/5000000000 : ℝ)*X 1 1+(-3211139657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((753541573/5000000000 : ℝ)*X 2 0+(15509859/20000000 : ℝ)*X 2 1+(2760233209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((600548249/2500000000 : ℝ)*X 0 0+(7535210591/10000000000 : ℝ)*X 0 1+(-2229265949/10000000000 : ℝ)*X 0 2+(600548249/2500000000 : ℝ)*X 1 0+(7535210591/10000000000 : ℝ)*X 1 1+(-2229265949/10000000000 : ℝ)*X 1 2+(600548249/2500000000 : ℝ)*X 2 0+(7535210591/10000000000 : ℝ)*X 2 1+(-2229265949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-329947053/10000000000 : ℝ)*X 0 0+(3583022839/10000000000 : ℝ)*X 0 1+(-7747913967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2283515803/2500000000 : ℝ)*X 1 0+(-32511443/250000000 : ℝ)*X 1 1+(-774984483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3770158117/10000000000 : ℝ)*X 2 0+(586542081/1000000000 : ℝ)*X 2 1+(2982351693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((4999999953/5000000000 : ℝ)*X 1 0+(3469/5000000000 : ℝ)*X 1 1+(4999999953/5000000000 : ℝ)*X 2 0+(3469/5000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1301791959/5000000000 : ℝ)*X 0 0+(413920659/1250000000 : ℝ)*X 0 1+(-1639388283/2500000000 : ℝ)*X 0 2+(1301791959/5000000000 : ℝ)*X 1 0+(413920659/1250000000 : ℝ)*X 1 1+(-1639388283/2500000000 : ℝ)*X 1 2+(1301791959/5000000000 : ℝ)*X 2 0+(413920659/1250000000 : ℝ)*X 2 1+(-1639388283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-18043351/400000000 : ℝ)*X 0 0+(5605226347/10000000000 : ℝ)*X 0 1+(-1472462941/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((9554214623/10000000000 : ℝ)*X 1 0+(-5721039/156250000 : ℝ)*X 1 1+(-860774129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1289239257/5000000000 : ℝ)*X 2 0+(3008178173/5000000000 : ℝ)*X 2 1+(3966984991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1022751581/2500000000 : ℝ)*X 0 0+(2727071371/5000000000 : ℝ)*X 0 1+(-3128055729/10000000000 : ℝ)*X 0 2+(1022751581/2500000000 : ℝ)*X 1 0+(2727071371/5000000000 : ℝ)*X 1 1+(-3128055729/10000000000 : ℝ)*X 1 2+(1022751581/2500000000 : ℝ)*X 2 0+(2727071371/5000000000 : ℝ)*X 2 1+(-3128055729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((38331/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38331/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20894830588090676315541/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (482117/500000000000 : ℝ)*(base18) + (103669832681/125000000000 : ℝ)*(base39) + (26522384431/25000000000 : ℝ)*(base49) + (235699/50000000000 : ℝ)*(base53) + (321665227579/500000000000 : ℝ)*(base60) + (2713310751423/1000000000000 : ℝ)*(major_s0_0) + (2713310751423/1000000000000 : ℝ)*(major_s0_1) + (2713306037443/1000000000000 : ℝ)*(major_s0_2) + (5186449/200000000000 : ℝ)*(sp_s0_1) + (3775632778951/1000000000000 : ℝ)*(sp_s0_7) + (3775632576127/1000000000000 : ℝ)*(sp_s0_8) + (1887832093293/500000000000 : ℝ)*(sp_s0_9) + (1650954530279/1000000000000 : ℝ)*(sp_s0_13) + (5338731/200000000000 : ℝ)*(sp_s0_14) + (1650954530279/1000000000000 : ℝ)*(f.failure) + (1887832093293/500000000000 : ℝ)*(f.sum) + (517014693427539/10000000000000000000000000000 : ℝ)*base63 + (317532456867421/625000000000000000000000000 : ℝ)*base65 + (578089396336467/2000000000000000000000000000 : ℝ)*base66 + (702414461279047/2000000000000000000000000000 : ℝ)*base69 + (1080299575561071/10000000000000000000000000000 : ℝ)*base71 + (312739683122981/625000000000000000000000000 : ℝ)*base73 + (357268228752019/625000000000000000000000000 : ℝ)*base75 + (654474625936467/2000000000000000000000000000 : ℝ)*base77 + (5355693178285361/10000000000000000000000000000 : ℝ)*base79 + (1727/25000000000000000 : ℝ)*base86 + (1727/25000000000000000 : ℝ)*base88 + (1727/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((49137/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(49137/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (58276760432766655971237/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1237623364489/1000000000000 : ℝ)*(base39) + (66571011723/100000000000 : ℝ)*(base49) + (42259176549/50000000000 : ℝ)*(base60) + (3245839146327/1000000000000 : ℝ)*(major_s0_0) + (649161664101/200000000000 : ℝ)*(major_s0_1) + (649161664101/200000000000 : ℝ)*(major_s0_2) + (6173289/200000000000 : ℝ)*(sp_s0_1) + (4695821/125000000000 : ℝ)*(sp_s0_7) + (180664581781/40000000000 : ℝ)*(sp_s0_14) + (4516532932719/1000000000000 : ℝ)*(sp_s0_15) + (4516652111093/1000000000000 : ℝ)*(sp_s0_16) + (30825823/1000000000000 : ℝ)*(sp_s0_17) + (1974960644793/1000000000000 : ℝ)*(sp_s0_20) + (88311929/1000000000000 : ℝ)*(sp_s0_22) + (1974960644793/1000000000000 : ℝ)*(f.failure) + (4516652111093/1000000000000 : ℝ)*(f.sum) + (1059721863801493/2000000000000000000000000000 : ℝ)*base63 + (7179665790947/125000000000000000000000000 : ℝ)*base65 + (167796570851329/400000000000000000000000000 : ℝ)*base66 + (153345483668671/400000000000000000000000000 : ℝ)*base68 + (108299804989313/400000000000000000000000000 : ℝ)*base70 + (500366558003731/625000000000000000000000000 : ℝ)*base72 + (73182204590947/125000000000000000000000000 : ℝ)*base74 + (541329050398283/2000000000000000000000000000 : ℝ)*base77 + (5191239945342921/10000000000000000000000000000 : ℝ)*base78 + (9991/25000000000000000 : ℝ)*base87 + (15009/25000000000000000 : ℝ)*base88 + (15009/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-311/800 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-311/800 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17303882025259918136007/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1023294718029/1000000000000 : ℝ)*(base39) + (42813531449/62500000000 : ℝ)*(base49) + (939153/500000000000 : ℝ)*(base50) + (1221413727343/500000000000 : ℝ)*(major_s0_0) + (1221413727343/500000000000 : ℝ)*(major_s0_1) + (1221413727343/500000000000 : ℝ)*(major_s0_2) + (41188047/500000000000 : ℝ)*(sp_s0_2) + (2686501/1000000000000 : ℝ)*(sp_s0_9) + (397189/62500000000 : ℝ)*(sp_s0_13) + (14899723/1000000000000 : ℝ)*(sp_s0_15) + (339927768147/100000000000 : ℝ)*(sp_s0_21) + (3399262781747/1000000000000 : ℝ)*(sp_s0_22) + (849798154719/250000000000 : ℝ)*(sp_s0_23) + (297273713137/200000000000 : ℝ)*(sp_s0_27) + (1486374920709/1000000000000 : ℝ)*(f.failure) + (339927768147/100000000000 : ℝ)*(f.sum) + (3009254986332801/5000000000000000000000000000 : ℝ)*base62 + (216298266589779/312500000000000000000000000 : ℝ)*base64 + (772199258653853/1000000000000000000000000000 : ℝ)*base67 + (558182286653853/1000000000000000000000000000 : ℝ)*base68 + (1626438367205729/5000000000000000000000000000 : ℝ)*base70 + (291949116441471/312500000000000000000000000 : ℝ)*base73 + (380673684910221/312500000000000000000000000 : ℝ)*base74 + (1388378706553853/1000000000000000000000000000 : ℝ)*base76 + (2060995021332801/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (20683/25000000000000000 : ℝ)*base87 + (20683/25000000000000000 : ℝ)*base89 + (20683/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (38331/100000 : ℝ) ^ (71/16 : ℝ) ≤ (35476747513817599/2500000000000000000 : ℝ) := by
    have hpowers : (38331/100000 : ℝ)^71 ≤ (35476747513817599/2500000000000000000 : ℝ)^16 := by
      have hnat : (38331 : ℕ)^71*2500000000000000000^16 ≤ 35476747513817599^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38331 100000 35476747513817599 2500000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38331/100000 : ℝ)) (X := (35476747513817599/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (2535476747513817599/2500000000000000000 : ℝ) ≤ (5015902365811697/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2535476747513817599/2500000000000000000 : ℝ)^16 ≤ (5015902365811697/5000000000000000 : ℝ)^71 := by
      have hnat : (2535476747513817599 : ℕ)^16*5000000000000000^71 ≤ 5015902365811697^71*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2535476747513817599 2500000000000000000 5015902365811697 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015902365811697/5000000000000000 : ℝ)) (X := (2535476747513817599/2500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1285476747513817599/1250000000000000000 : ℝ) ≤ (5031633289210167/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1285476747513817599/1250000000000000000 : ℝ)^16 ≤ (5031633289210167/5000000000000000 : ℝ)^71 := by
      have hnat : (1285476747513817599 : ℕ)^16*5000000000000000^71 ≤ 5031633289210167^71*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1285476747513817599 1250000000000000000 5031633289210167 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5031633289210167/5000000000000000 : ℝ)) (X := (1285476747513817599/1250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1766929534633/212950000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1573092339847/191655000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (38331/100000 : ℝ)) (alpha := (1766929534633/212950000000000 : ℝ)) (beta := (1573092339847/191655000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38331/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1766929534633/212950000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1573092339847/191655000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (49137/100000 : ℝ) ^ (71/16 : ℝ) ≤ (213597336973041007/5000000000000000000 : ℝ) := by
    have hpowers : (49137/100000 : ℝ)^71 ≤ (213597336973041007/5000000000000000000 : ℝ)^16 := by
      have hnat : (49137 : ℕ)^71*5000000000000000000^16 ≤ 213597336973041007^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49137 100000 213597336973041007 5000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (49137/100000 : ℝ)) (X := (213597336973041007/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (5213597336973041007/5000000000000000000 : ℝ) ≤ (100947154234517/100000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (5213597336973041007/5000000000000000000 : ℝ)^16 ≤ (100947154234517/100000000000000 : ℝ)^71 := by
      have hnat : (5213597336973041007 : ℕ)^16*100000000000000^71 ≤ 100947154234517^71*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5213597336973041007 5000000000000000000 100947154234517 100000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100947154234517/100000000000000 : ℝ)) (X := (5213597336973041007/5000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2713597336973041007/2500000000000000000 : ℝ) ≤ (407458838141479/400000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2713597336973041007/2500000000000000000 : ℝ)^16 ≤ (407458838141479/400000000000000 : ℝ)^71 := by
      have hnat : (2713597336973041007 : ℕ)^16*400000000000000^71 ≤ 407458838141479^71*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2713597336973041007 2500000000000000000 407458838141479 400000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (407458838141479/400000000000000 : ℝ)) (X := (2713597336973041007/2500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(947154234517/49137000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(3670221203411/196548000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (49137/100000 : ℝ)) (alpha := (947154234517/49137000000000 : ℝ)) (beta := (3670221203411/196548000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (49137/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(947154234517/49137000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(3670221203411/196548000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (311/800 : ℝ) ^ (71/16 : ℝ) ≤ (755322485132142993/50000000000000000000 : ℝ) := by
    have hpowers : (311/800 : ℝ)^71 ≤ (755322485132142993/50000000000000000000 : ℝ)^16 := by
      have hnat : (311 : ℕ)^71*50000000000000000000^16 ≤ 755322485132142993^16*800^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        311 800 755322485132142993 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (311/800 : ℝ)) (X := (755322485132142993/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50755322485132142993/50000000000000000000 : ℝ) ≤ (10033845278178253/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (50755322485132142993/50000000000000000000 : ℝ)^16 ≤ (10033845278178253/10000000000000000 : ℝ)^71 := by
      have hnat : (50755322485132142993 : ℕ)^16*10000000000000000^71 ≤ 10033845278178253^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50755322485132142993 50000000000000000000 10033845278178253 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10033845278178253/10000000000000000 : ℝ)) (X := (50755322485132142993/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25755322485132142993/25000000000000000000 : ℝ) ≤ (2013460521497881/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (25755322485132142993/25000000000000000000 : ℝ)^16 ≤ (2013460521497881/2000000000000000 : ℝ)^71 := by
      have hnat : (25755322485132142993 : ℕ)^16*2000000000000000^71 ≤ 2013460521497881^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25755322485132142993 25000000000000000000 2013460521497881 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2013460521497881/2000000000000000 : ℝ)) (X := (25755322485132142993/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(33845278178253/3887500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2091083081947/242968750000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (311/800 : ℝ)) (alpha := (33845278178253/3887500000000000 : ℝ)) (beta := (2091083081947/242968750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (311/800 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(33845278178253/3887500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2091083081947/242968750000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2640179343/10000000000 : ℝ)*X 0 0+(4401412367/10000000000 : ℝ)*X 0 1+(-1392848999/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((320445489/500000000 : ℝ)*X 1 0+(-347905681/1250000000 : ℝ)*X 1 1+(-3322099711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3782961179/10000000000 : ℝ)*X 2 0+(2578865033/5000000000 : ℝ)*X 2 1+(3783022789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3760029363/10000000000 : ℝ)*X 0 0+(4870828431/10000000000 : ℝ)*X 0 1+(-4112853763/10000000000 : ℝ)*X 0 2+(3760029363/10000000000 : ℝ)*X 1 0+(4870828431/10000000000 : ℝ)*X 1 1+(-4112853763/10000000000 : ℝ)*X 1 2+(3760029363/10000000000 : ℝ)*X 2 0+(4870828431/10000000000 : ℝ)*X 2 1+(-4112853763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-85761/12500 : ℝ) < ((-41087/25000 : ℝ)*P 0+(-41087/25000 : ℝ)*P 1+(-41087/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-85761/12500 : ℝ) < (-2214663204052664909359033295189923/325421821065000000000000000000000 : ℝ) := by norm_num
    linear_combination (1329/500000000000 : ℝ)*(base11) + (27393/500000000000 : ℝ)*(base16) + (11907/1000000000000 : ℝ)*(base18) + (46508506453/100000000000 : ℝ)*(base39) + (12093/250000000000 : ℝ)*(base43) + (45079/1000000000000 : ℝ)*(base44) + (378621045149/1000000000000 : ℝ)*(base49) + (5377465001/31250000000 : ℝ)*(base60) + (41087/25000 : ℝ)*(major_s1_0) + (410869976637/250000000000 : ℝ)*(major_s1_1) + (41087/25000 : ℝ)*(major_s1_2) + (2268505071337/1000000000000 : ℝ)*(sp_s1_0) + (453701002119/200000000000 : ℝ)*(sp_s1_1) + (453701014799/200000000000 : ℝ)*(sp_s1_2) + (999999954921/1000000000000 : ℝ)*(sp_s1_6) + (2268505122367/1000000000000 : ℝ)*(f.sum) + (13512265281328849/25469345000000000000000000000 : ℝ)*base62 + (157153994093/311000000000000000000000 : ℝ)*base64 + (7825900324081/32758000000000000000000000 : ℝ)*base67 + (1756737083553/3110000000000000000000000 : ℝ)*base68 + (3811744645900341/13245490000000000000000000000 : ℝ)*base71 + (21174425280401/47913750000000000000000000 : ℝ)*base73 + (40032971943951/81895000000000000000000000 : ℝ)*base74 + (26299273172839/42590000000000000000000000 : ℝ)*base76 + (403249326505475903/1569558622500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base89 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p011_b034 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c311079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c311080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p011_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

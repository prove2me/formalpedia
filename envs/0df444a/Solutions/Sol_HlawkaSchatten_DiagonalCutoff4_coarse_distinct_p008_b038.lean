-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b038
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:27:06.26281+00:00
-- url     : https://prove2.me/submissions/b02ec601-3d6a-4341-ab93-c4e2f2569610

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308080_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308080_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308080_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308080_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c308080 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c308080_s0 p hpa hpb X hX
  have h1 := collision_c308080_s1 p hpa hpb X hX h0
  have h2 := collision_c308080_s2 p hpa hpb X hX h1
  exact collision_c308080_s3 p hpa hpb X hX h2

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
theorem collision_support_c308079_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (808979949/1000000000 : ℝ)*x 0 + (-47897917/312500000 : ℝ)*x 1 + (-47565767/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808979949/1000000000 : ℝ)^69 ≤ (75883155550369/100000000000000 : ℝ)^53 := by
    have hnat : (808979949 : ℕ)^69*100000000000000^53 ≤ 75883155550369^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808979949 1000000000 75883155550369 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47897917/312500000 : ℝ)^69 ≤ (1087626409729/12500000000000 : ℝ)^53 := by
    have hnat : (47897917 : ℕ)^69*12500000000000^53 ≤ 1087626409729^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47897917 312500000 1087626409729 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47565767/200000000 : ℝ)^69 ≤ (15415833165731/100000000000000 : ℝ)^53 := by
    have hnat : (47565767 : ℕ)^69*100000000000000^53 ≤ 15415833165731^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47565767 200000000 15415833165731 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808979949/1000000000 : ℝ), (-47897917/312500000 : ℝ), (-47565767/200000000 : ℝ)] ![(75883155550369/100000000000000 : ℝ), (1087626409729/12500000000000 : ℝ), (15415833165731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808979949/1000000000 : ℝ)|^69 ≤ (75883155550369/100000000000000 : ℝ)^53
        have hw : |(808979949/1000000000 : ℝ)|=(808979949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47897917/312500000 : ℝ)|^69 ≤ (1087626409729/12500000000000 : ℝ)^53
        have hw : |(-47897917/312500000 : ℝ)|=(47897917/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47565767/200000000 : ℝ)|^69 ≤ (15415833165731/100000000000000 : ℝ)^53
        have hw : |(-47565767/200000000 : ℝ)|=(47565767/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3207109111/10000000000 : ℝ)*x 0 + (1503107279/2500000000 : ℝ)*x 1 + (1760040451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3207109111/10000000000 : ℝ)^69 ≤ (22751812257551/100000000000000 : ℝ)^53 := by
    have hnat : (3207109111 : ℕ)^69*100000000000000^53 ≤ 22751812257551^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3207109111 10000000000 22751812257551 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1503107279/2500000000 : ℝ)^69 ≤ (12891043736253/25000000000000 : ℝ)^53 := by
    have hnat : (1503107279 : ℕ)^69*25000000000000^53 ≤ 12891043736253^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503107279 2500000000 12891043736253 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1760040451/5000000000 : ℝ)^69 ≤ (1284200639249/5000000000000 : ℝ)^53 := by
    have hnat : (1760040451 : ℕ)^69*5000000000000^53 ≤ 1284200639249^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760040451 5000000000 1284200639249 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3207109111/10000000000 : ℝ), (1503107279/2500000000 : ℝ), (1760040451/5000000000 : ℝ)] ![(22751812257551/100000000000000 : ℝ), (12891043736253/25000000000000 : ℝ), (1284200639249/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3207109111/10000000000 : ℝ)|^69 ≤ (22751812257551/100000000000000 : ℝ)^53
        have hw : |(3207109111/10000000000 : ℝ)|=(3207109111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1503107279/2500000000 : ℝ)|^69 ≤ (12891043736253/25000000000000 : ℝ)^53
        have hw : |(1503107279/2500000000 : ℝ)|=(1503107279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1760040451/5000000000 : ℝ)|^69 ≤ (1284200639249/5000000000000 : ℝ)^53
        have hw : |(1760040451/5000000000 : ℝ)|=(1760040451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-853937611/5000000000 : ℝ)*x 0 + (728922561/2500000000 : ℝ)*x 1 + (-1898487943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853937611/5000000000 : ℝ)^69 ≤ (2504290994867/25000000000000 : ℝ)^53 := by
    have hnat : (853937611 : ℕ)^69*25000000000000^53 ≤ 2504290994867^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853937611 5000000000 2504290994867 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (728922561/2500000000 : ℝ)^69 ≤ (10049023948133/50000000000000 : ℝ)^53 := by
    have hnat : (728922561 : ℕ)^69*50000000000000^53 ≤ 10049023948133^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728922561 2500000000 10049023948133 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1898487943/2500000000 : ℝ)^69 ≤ (34942394051977/50000000000000 : ℝ)^53 := by
    have hnat : (1898487943 : ℕ)^69*50000000000000^53 ≤ 34942394051977^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898487943 2500000000 34942394051977 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-853937611/5000000000 : ℝ), (728922561/2500000000 : ℝ), (-1898487943/2500000000 : ℝ)] ![(2504290994867/25000000000000 : ℝ), (10049023948133/50000000000000 : ℝ), (34942394051977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-853937611/5000000000 : ℝ)|^69 ≤ (2504290994867/25000000000000 : ℝ)^53
        have hw : |(-853937611/5000000000 : ℝ)|=(853937611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(728922561/2500000000 : ℝ)|^69 ≤ (10049023948133/50000000000000 : ℝ)^53
        have hw : |(728922561/2500000000 : ℝ)|=(728922561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1898487943/2500000000 : ℝ)|^69 ≤ (34942394051977/50000000000000 : ℝ)^53
        have hw : |(-1898487943/2500000000 : ℝ)|=(1898487943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1005799111/1250000000 : ℝ)*x 0 + (-35590779/1250000000 : ℝ)*x 1 + (-413313421/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005799111/1250000000 : ℝ)^69 ≤ (75353511233559/100000000000000 : ℝ)^53 := by
    have hnat : (1005799111 : ℕ)^69*100000000000000^53 ≤ 75353511233559^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005799111 1250000000 75353511233559 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35590779/1250000000 : ℝ)^69 ≤ (194477581997/20000000000000 : ℝ)^53 := by
    have hnat : (35590779 : ℕ)^69*20000000000000^53 ≤ 194477581997^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35590779 1250000000 194477581997 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413313421/1250000000 : ℝ)^69 ≤ (23674100843373/100000000000000 : ℝ)^53 := by
    have hnat : (413313421 : ℕ)^69*100000000000000^53 ≤ 23674100843373^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413313421 1250000000 23674100843373 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1005799111/1250000000 : ℝ), (-35590779/1250000000 : ℝ), (-413313421/1250000000 : ℝ)] ![(75353511233559/100000000000000 : ℝ), (194477581997/20000000000000 : ℝ), (23674100843373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1005799111/1250000000 : ℝ)|^69 ≤ (75353511233559/100000000000000 : ℝ)^53
        have hw : |(1005799111/1250000000 : ℝ)|=(1005799111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35590779/1250000000 : ℝ)|^69 ≤ (194477581997/20000000000000 : ℝ)^53
        have hw : |(-35590779/1250000000 : ℝ)|=(35590779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413313421/1250000000 : ℝ)|^69 ≤ (23674100843373/100000000000000 : ℝ)^53
        have hw : |(-413313421/1250000000 : ℝ)|=(413313421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1420926719/10000000000 : ℝ)*x 0 + (1975946939/2500000000 : ℝ)*x 1 + (1367759993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1420926719/10000000000 : ℝ)^69 ≤ (394197865183/5000000000000 : ℝ)^53 := by
    have hnat : (1420926719 : ℕ)^69*5000000000000^53 ≤ 394197865183^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420926719 10000000000 394197865183 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975946939/2500000000 : ℝ)^69 ≤ (36809768908023/50000000000000 : ℝ)^53 := by
    have hnat : (1975946939 : ℕ)^69*50000000000000^53 ≤ 36809768908023^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975946939 2500000000 36809768908023 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367759993/5000000000 : ℝ)^69 ≤ (18496504858349/100000000000000 : ℝ)^53 := by
    have hnat : (1367759993 : ℕ)^69*100000000000000^53 ≤ 18496504858349^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367759993 5000000000 18496504858349 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1420926719/10000000000 : ℝ), (1975946939/2500000000 : ℝ), (1367759993/5000000000 : ℝ)] ![(394197865183/5000000000000 : ℝ), (36809768908023/50000000000000 : ℝ), (18496504858349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1420926719/10000000000 : ℝ)|^69 ≤ (394197865183/5000000000000 : ℝ)^53
        have hw : |(1420926719/10000000000 : ℝ)|=(1420926719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1975946939/2500000000 : ℝ)|^69 ≤ (36809768908023/50000000000000 : ℝ)^53
        have hw : |(1975946939/2500000000 : ℝ)|=(1975946939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367759993/5000000000 : ℝ)|^69 ≤ (18496504858349/100000000000000 : ℝ)^53
        have hw : |(1367759993/5000000000 : ℝ)|=(1367759993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (590038191/2500000000 : ℝ)*x 0 + (7643385163/10000000000 : ℝ)*x 1 + (-1120009907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (590038191/2500000000 : ℝ)^69 ≤ (3052593760691/20000000000000 : ℝ)^53 := by
    have hnat : (590038191 : ℕ)^69*20000000000000^53 ≤ 3052593760691^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590038191 2500000000 3052593760691 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7643385163/10000000000 : ℝ)^69 ≤ (4404851485007/6250000000000 : ℝ)^53 := by
    have hnat : (7643385163 : ℕ)^69*6250000000000^53 ≤ 4404851485007^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7643385163 10000000000 4404851485007 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120009907/5000000000 : ℝ)^69 ≤ (891212963961/6250000000000 : ℝ)^53 := by
    have hnat : (1120009907 : ℕ)^69*6250000000000^53 ≤ 891212963961^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120009907 5000000000 891212963961 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(590038191/2500000000 : ℝ), (7643385163/10000000000 : ℝ), (-1120009907/5000000000 : ℝ)] ![(3052593760691/20000000000000 : ℝ), (4404851485007/6250000000000 : ℝ), (891212963961/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(590038191/2500000000 : ℝ)|^69 ≤ (3052593760691/20000000000000 : ℝ)^53
        have hw : |(590038191/2500000000 : ℝ)|=(590038191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7643385163/10000000000 : ℝ)|^69 ≤ (4404851485007/6250000000000 : ℝ)^53
        have hw : |(7643385163/10000000000 : ℝ)|=(7643385163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120009907/5000000000 : ℝ)|^69 ≤ (891212963961/6250000000000 : ℝ)^53
        have hw : |(-1120009907/5000000000 : ℝ)|=(1120009907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-292838591/10000000000 : ℝ)*x 0 + (3562198359/10000000000 : ℝ)*x 1 + (-7844927251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (292838591/10000000000 : ℝ)^69 ≤ (504305438109/50000000000000 : ℝ)^53 := by
    have hnat : (292838591 : ℕ)^69*50000000000000^53 ≤ 504305438109^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292838591 10000000000 504305438109 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3562198359/10000000000 : ℝ)^69 ≤ (652120304673/2500000000000 : ℝ)^53 := by
    have hnat : (3562198359 : ℕ)^69*2500000000000^53 ≤ 652120304673^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3562198359 10000000000 652120304673 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7844927251/10000000000 : ℝ)^69 ≤ (72906576921253/100000000000000 : ℝ)^53 := by
    have hnat : (7844927251 : ℕ)^69*100000000000000^53 ≤ 72906576921253^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7844927251 10000000000 72906576921253 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-292838591/10000000000 : ℝ), (3562198359/10000000000 : ℝ), (-7844927251/10000000000 : ℝ)] ![(504305438109/50000000000000 : ℝ), (652120304673/2500000000000 : ℝ), (72906576921253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-292838591/10000000000 : ℝ)|^69 ≤ (504305438109/50000000000000 : ℝ)^53
        have hw : |(-292838591/10000000000 : ℝ)|=(292838591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3562198359/10000000000 : ℝ)|^69 ≤ (652120304673/2500000000000 : ℝ)^53
        have hw : |(3562198359/10000000000 : ℝ)|=(3562198359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7844927251/10000000000 : ℝ)|^69 ≤ (72906576921253/100000000000000 : ℝ)^53
        have hw : |(-7844927251/10000000000 : ℝ)|=(7844927251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (927135263/1000000000 : ℝ)*x 0 + (-300071401/2500000000 : ℝ)*x 1 + (-137059803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927135263/1000000000 : ℝ)^69 ≤ (18123999055243/20000000000000 : ℝ)^53 := by
    have hnat : (927135263 : ℕ)^69*20000000000000^53 ≤ 18123999055243^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927135263 1000000000 18123999055243 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300071401/2500000000 : ℝ)^69 ≤ (6328966218583/100000000000000 : ℝ)^53 := by
    have hnat : (300071401 : ℕ)^69*100000000000000^53 ≤ 6328966218583^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300071401 2500000000 6328966218583 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137059803/2000000000 : ℝ)^69 ≤ (762759623869/25000000000000 : ℝ)^53 := by
    have hnat : (137059803 : ℕ)^69*25000000000000^53 ≤ 762759623869^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137059803 2000000000 762759623869 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(927135263/1000000000 : ℝ), (-300071401/2500000000 : ℝ), (-137059803/2000000000 : ℝ)] ![(18123999055243/20000000000000 : ℝ), (6328966218583/100000000000000 : ℝ), (762759623869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(927135263/1000000000 : ℝ)|^69 ≤ (18123999055243/20000000000000 : ℝ)^53
        have hw : |(927135263/1000000000 : ℝ)|=(927135263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300071401/2500000000 : ℝ)|^69 ≤ (6328966218583/100000000000000 : ℝ)^53
        have hw : |(-300071401/2500000000 : ℝ)|=(300071401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137059803/2000000000 : ℝ)|^69 ≤ (762759623869/25000000000000 : ℝ)^53
        have hw : |(-137059803/2000000000 : ℝ)|=(137059803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (389339949/1000000000 : ℝ)*x 0 + (2926747211/5000000000 : ℝ)*x 1 + (751648233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389339949/1000000000 : ℝ)^69 ≤ (29285638268521/100000000000000 : ℝ)^53 := by
    have hnat : (389339949 : ℕ)^69*100000000000000^53 ≤ 29285638268521^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389339949 1000000000 29285638268521 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2926747211/5000000000 : ℝ)^69 ≤ (49796742310231/100000000000000 : ℝ)^53 := by
    have hnat : (2926747211 : ℕ)^69*100000000000000^53 ≤ 49796742310231^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2926747211 5000000000 49796742310231 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (751648233/2500000000 : ℝ)^69 ≤ (20917619415231/100000000000000 : ℝ)^53 := by
    have hnat : (751648233 : ℕ)^69*100000000000000^53 ≤ 20917619415231^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751648233 2500000000 20917619415231 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(389339949/1000000000 : ℝ), (2926747211/5000000000 : ℝ), (751648233/2500000000 : ℝ)] ![(29285638268521/100000000000000 : ℝ), (49796742310231/100000000000000 : ℝ), (20917619415231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(389339949/1000000000 : ℝ)|^69 ≤ (29285638268521/100000000000000 : ℝ)^53
        have hw : |(389339949/1000000000 : ℝ)|=(389339949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2926747211/5000000000 : ℝ)|^69 ≤ (49796742310231/100000000000000 : ℝ)^53
        have hw : |(2926747211/5000000000 : ℝ)|=(2926747211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(751648233/2500000000 : ℝ)|^69 ≤ (20917619415231/100000000000000 : ℝ)^53
        have hw : |(751648233/2500000000 : ℝ)|=(751648233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_17 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999963/10000000000 : ℝ)*x 0 + (201/500000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999963/10000000000 : ℝ)^69 ≤ (49999999759151/50000000000000 : ℝ)^53 := by
    have hnat : (9999999963 : ℕ)^69*50000000000000^53 ≤ 49999999759151^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999963 10000000000 49999999759151 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201/500000000 : ℝ)^69 ≤ (5893/1250000000000 : ℝ)^53 := by
    have hnat : (201 : ℕ)^69*1250000000000^53 ≤ 5893^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201 500000000 5893 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^69 ≤ (0 : ℝ)^53 := by
    have hnat : (0 : ℕ)^69*1^53 ≤ 0^53*1^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999963/10000000000 : ℝ), (201/500000000 : ℝ), (0 : ℝ)] ![(49999999759151/50000000000000 : ℝ), (5893/1250000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999963/10000000000 : ℝ)|^69 ≤ (49999999759151/50000000000000 : ℝ)^53
        have hw : |(9999999963/10000000000 : ℝ)|=(9999999963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201/500000000 : ℝ)|^69 ≤ (5893/1250000000000 : ℝ)^53
        have hw : |(201/500000000 : ℝ)|=(201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^69 ≤ (0 : ℝ)^53
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2620736413/10000000000 : ℝ)*x 0 + (805927877/2500000000 : ℝ)*x 1 + (-3360046619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620736413/10000000000 : ℝ)^69 ≤ (8746273134697/50000000000000 : ℝ)^53 := by
    have hnat : (2620736413 : ℕ)^69*50000000000000^53 ≤ 8746273134697^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620736413 10000000000 8746273134697 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805927877/2500000000 : ℝ)^69 ≤ (22905268687831/100000000000000 : ℝ)^53 := by
    have hnat : (805927877 : ℕ)^69*100000000000000^53 ≤ 22905268687831^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805927877 2500000000 22905268687831 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3360046619/5000000000 : ℝ)^69 ≤ (59602185027491/100000000000000 : ℝ)^53 := by
    have hnat : (3360046619 : ℕ)^69*100000000000000^53 ≤ 59602185027491^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3360046619 5000000000 59602185027491 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620736413/10000000000 : ℝ), (805927877/2500000000 : ℝ), (-3360046619/5000000000 : ℝ)] ![(8746273134697/50000000000000 : ℝ), (22905268687831/100000000000000 : ℝ), (59602185027491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620736413/10000000000 : ℝ)|^69 ≤ (8746273134697/50000000000000 : ℝ)^53
        have hw : |(2620736413/10000000000 : ℝ)|=(2620736413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805927877/2500000000 : ℝ)|^69 ≤ (22905268687831/100000000000000 : ℝ)^53
        have hw : |(805927877/2500000000 : ℝ)|=(805927877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3360046619/5000000000 : ℝ)|^69 ≤ (59602185027491/100000000000000 : ℝ)^53
        have hw : |(-3360046619/5000000000 : ℝ)|=(3360046619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-217622677/5000000000 : ℝ)*x 0 + (5704245133/10000000000 : ℝ)*x 1 + (-117725747/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217622677/5000000000 : ℝ)^69 ≤ (33792160299/2000000000000 : ℝ)^53 := by
    have hnat : (217622677 : ℕ)^69*2000000000000^53 ≤ 33792160299^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217622677 5000000000 33792160299 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5704245133/10000000000 : ℝ)^69 ≤ (24075074270763/50000000000000 : ℝ)^53 := by
    have hnat : (5704245133 : ℕ)^69*50000000000000^53 ≤ 24075074270763^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704245133 10000000000 24075074270763 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117725747/200000000 : ℝ)^69 ≤ (25080121717483/50000000000000 : ℝ)^53 := by
    have hnat : (117725747 : ℕ)^69*50000000000000^53 ≤ 25080121717483^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117725747 200000000 25080121717483 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217622677/5000000000 : ℝ), (5704245133/10000000000 : ℝ), (-117725747/200000000 : ℝ)] ![(33792160299/2000000000000 : ℝ), (24075074270763/50000000000000 : ℝ), (25080121717483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217622677/5000000000 : ℝ)|^69 ≤ (33792160299/2000000000000 : ℝ)^53
        have hw : |(-217622677/5000000000 : ℝ)|=(217622677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5704245133/10000000000 : ℝ)|^69 ≤ (24075074270763/50000000000000 : ℝ)^53
        have hw : |(5704245133/10000000000 : ℝ)|=(5704245133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117725747/200000000 : ℝ)|^69 ≤ (25080121717483/50000000000000 : ℝ)^53
        have hw : |(-117725747/200000000 : ℝ)|=(117725747/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9629191957/10000000000 : ℝ)*x 0 + (-337782577/10000000000 : ℝ)*x 1 + (-775773713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9629191957/10000000000 : ℝ)^69 ≤ (95199755978099/100000000000000 : ℝ)^53 := by
    have hnat : (9629191957 : ℕ)^69*100000000000000^53 ≤ 95199755978099^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9629191957 10000000000 95199755978099 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337782577/10000000000 : ℝ)^69 ≤ (1214653097317/100000000000000 : ℝ)^53 := by
    have hnat : (337782577 : ℕ)^69*100000000000000^53 ≤ 1214653097317^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337782577 10000000000 1214653097317 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775773713/10000000000 : ℝ)^69 ≤ (3585590907053/100000000000000 : ℝ)^53 := by
    have hnat : (775773713 : ℕ)^69*100000000000000^53 ≤ 3585590907053^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775773713 10000000000 3585590907053 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9629191957/10000000000 : ℝ), (-337782577/10000000000 : ℝ), (-775773713/10000000000 : ℝ)] ![(95199755978099/100000000000000 : ℝ), (1214653097317/100000000000000 : ℝ), (3585590907053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9629191957/10000000000 : ℝ)|^69 ≤ (95199755978099/100000000000000 : ℝ)^53
        have hw : |(9629191957/10000000000 : ℝ)|=(9629191957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-337782577/10000000000 : ℝ)|^69 ≤ (1214653097317/100000000000000 : ℝ)^53
        have hw : |(-337782577/10000000000 : ℝ)|=(337782577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-775773713/10000000000 : ℝ)|^69 ≤ (3585590907053/100000000000000 : ℝ)^53
        have hw : |(-775773713/10000000000 : ℝ)|=(775773713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (257283959/1000000000 : ℝ)*x 0 + (6139753347/10000000000 : ℝ)*x 1 + (79185137/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257283959/1000000000 : ℝ)^69 ≤ (1707749213601/10000000000000 : ℝ)^53 := by
    have hnat : (257283959 : ℕ)^69*10000000000000^53 ≤ 1707749213601^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257283959 1000000000 1707749213601 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6139753347/10000000000 : ℝ)^69 ≤ (52990313227759/100000000000000 : ℝ)^53 := by
    have hnat : (6139753347 : ℕ)^69*100000000000000^53 ≤ 52990313227759^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6139753347 10000000000 52990313227759 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79185137/200000000 : ℝ)^69 ≤ (14966097309157/50000000000000 : ℝ)^53 := by
    have hnat : (79185137 : ℕ)^69*50000000000000^53 ≤ 14966097309157^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79185137 200000000 14966097309157 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257283959/1000000000 : ℝ), (6139753347/10000000000 : ℝ), (79185137/200000000 : ℝ)] ![(1707749213601/10000000000000 : ℝ), (52990313227759/100000000000000 : ℝ), (14966097309157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257283959/1000000000 : ℝ)|^69 ≤ (1707749213601/10000000000000 : ℝ)^53
        have hw : |(257283959/1000000000 : ℝ)|=(257283959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6139753347/10000000000 : ℝ)|^69 ≤ (52990313227759/100000000000000 : ℝ)^53
        have hw : |(6139753347/10000000000 : ℝ)|=(6139753347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79185137/200000000 : ℝ)|^69 ≤ (14966097309157/50000000000000 : ℝ)^53
        have hw : |(79185137/200000000 : ℝ)|=(79185137/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s0_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4371470909/10000000000 : ℝ)*x 0 + (667949889/1250000000 : ℝ)*x 1 + (-3095131863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371470909/10000000000 : ℝ)^69 ≤ (2128226402063/6250000000000 : ℝ)^53 := by
    have hnat : (4371470909 : ℕ)^69*6250000000000^53 ≤ 2128226402063^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371470909 10000000000 2128226402063 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667949889/1250000000 : ℝ)^69 ≤ (11056317899797/25000000000000 : ℝ)^53 := by
    have hnat : (667949889 : ℕ)^69*25000000000000^53 ≤ 11056317899797^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667949889 1250000000 11056317899797 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3095131863/10000000000 : ℝ)^69 ≤ (21723105944281/100000000000000 : ℝ)^53 := by
    have hnat : (3095131863 : ℕ)^69*100000000000000^53 ≤ 21723105944281^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3095131863 10000000000 21723105944281 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371470909/10000000000 : ℝ), (667949889/1250000000 : ℝ), (-3095131863/10000000000 : ℝ)] ![(2128226402063/6250000000000 : ℝ), (11056317899797/25000000000000 : ℝ), (21723105944281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371470909/10000000000 : ℝ)|^69 ≤ (2128226402063/6250000000000 : ℝ)^53
        have hw : |(4371470909/10000000000 : ℝ)|=(4371470909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(667949889/1250000000 : ℝ)|^69 ≤ (11056317899797/25000000000000 : ℝ)^53
        have hw : |(667949889/1250000000 : ℝ)|=(667949889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3095131863/10000000000 : ℝ)|^69 ≤ (21723105944281/100000000000000 : ℝ)^53
        have hw : |(-3095131863/10000000000 : ℝ)|=(3095131863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-532338541/2000000000 : ℝ)*x 0 + (4438358013/10000000000 : ℝ)*x 1 + (-1127523201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532338541/2000000000 : ℝ)^69 ≤ (17849279119053/100000000000000 : ℝ)^53 := by
    have hnat : (532338541 : ℕ)^69*100000000000000^53 ≤ 17849279119053^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532338541 2000000000 17849279119053 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4438358013/10000000000 : ℝ)^69 ≤ (17365744873653/50000000000000 : ℝ)^53 := by
    have hnat : (4438358013 : ℕ)^69*50000000000000^53 ≤ 17365744873653^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438358013 10000000000 17365744873653 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127523201/2000000000 : ℝ)^69 ≤ (379353848871/800000000000 : ℝ)^53 := by
    have hnat : (1127523201 : ℕ)^69*800000000000^53 ≤ 379353848871^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127523201 2000000000 379353848871 800000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532338541/2000000000 : ℝ), (4438358013/10000000000 : ℝ), (-1127523201/2000000000 : ℝ)] ![(17849279119053/100000000000000 : ℝ), (17365744873653/50000000000000 : ℝ), (379353848871/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532338541/2000000000 : ℝ)|^69 ≤ (17849279119053/100000000000000 : ℝ)^53
        have hw : |(-532338541/2000000000 : ℝ)|=(532338541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4438358013/10000000000 : ℝ)|^69 ≤ (17365744873653/50000000000000 : ℝ)^53
        have hw : |(4438358013/10000000000 : ℝ)|=(4438358013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127523201/2000000000 : ℝ)|^69 ≤ (379353848871/800000000000 : ℝ)^53
        have hw : |(-1127523201/2000000000 : ℝ)|=(1127523201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (646090611/1000000000 : ℝ)*x 0 + (-2840380139/10000000000 : ℝ)*x 1 + (-833966761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646090611/1000000000 : ℝ)^69 ≤ (7078374476657/12500000000000 : ℝ)^53 := by
    have hnat : (646090611 : ℕ)^69*12500000000000^53 ≤ 7078374476657^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646090611 1000000000 7078374476657 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2840380139/10000000000 : ℝ)^69 ≤ (19424866478397/100000000000000 : ℝ)^53 := by
    have hnat : (2840380139 : ℕ)^69*100000000000000^53 ≤ 19424866478397^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840380139 10000000000 19424866478397 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833966761/2500000000 : ℝ)^69 ≤ (957925507779/4000000000000 : ℝ)^53 := by
    have hnat : (833966761 : ℕ)^69*4000000000000^53 ≤ 957925507779^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833966761 2500000000 957925507779 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646090611/1000000000 : ℝ), (-2840380139/10000000000 : ℝ), (-833966761/2500000000 : ℝ)] ![(7078374476657/12500000000000 : ℝ), (19424866478397/100000000000000 : ℝ), (957925507779/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646090611/1000000000 : ℝ)|^69 ≤ (7078374476657/12500000000000 : ℝ)^53
        have hw : |(646090611/1000000000 : ℝ)|=(646090611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2840380139/10000000000 : ℝ)|^69 ≤ (19424866478397/100000000000000 : ℝ)^53
        have hw : |(-2840380139/10000000000 : ℝ)|=(2840380139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-833966761/2500000000 : ℝ)|^69 ≤ (957925507779/4000000000000 : ℝ)^53
        have hw : |(-833966761/2500000000 : ℝ)|=(833966761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1926087209/5000000000 : ℝ)*x 0 + (5192983633/10000000000 : ℝ)*x 1 + (190687333/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926087209/5000000000 : ℝ)^69 ≤ (28882583577747/100000000000000 : ℝ)^53 := by
    have hnat : (1926087209 : ℕ)^69*100000000000000^53 ≤ 28882583577747^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926087209 5000000000 28882583577747 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192983633/10000000000 : ℝ)^69 ≤ (1704374712923/4000000000000 : ℝ)^53 := by
    have hnat : (5192983633 : ℕ)^69*4000000000000^53 ≤ 1704374712923^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192983633 10000000000 1704374712923 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190687333/500000000 : ℝ)^69 ≤ (5701609716127/20000000000000 : ℝ)^53 := by
    have hnat : (190687333 : ℕ)^69*20000000000000^53 ≤ 5701609716127^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190687333 500000000 5701609716127 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1926087209/5000000000 : ℝ), (5192983633/10000000000 : ℝ), (190687333/500000000 : ℝ)] ![(28882583577747/100000000000000 : ℝ), (1704374712923/4000000000000 : ℝ), (5701609716127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1926087209/5000000000 : ℝ)|^69 ≤ (28882583577747/100000000000000 : ℝ)^53
        have hw : |(1926087209/5000000000 : ℝ)|=(1926087209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192983633/10000000000 : ℝ)|^69 ≤ (1704374712923/4000000000000 : ℝ)^53
        have hw : |(5192983633/10000000000 : ℝ)|=(5192983633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190687333/500000000 : ℝ)|^69 ≤ (5701609716127/20000000000000 : ℝ)^53
        have hw : |(190687333/500000000 : ℝ)|=(190687333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308079_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3805120177/10000000000 : ℝ)*x 0 + (974555209/2000000000 : ℝ)*x 1 + (-2101577279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3805120177/10000000000 : ℝ)^69 ≤ (2842412688327/10000000000000 : ℝ)^53 := by
    have hnat : (3805120177 : ℕ)^69*10000000000000^53 ≤ 2842412688327^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805120177 10000000000 2842412688327 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974555209/2000000000 : ℝ)^69 ≤ (39221146608309/100000000000000 : ℝ)^53 := by
    have hnat : (974555209 : ℕ)^69*100000000000000^53 ≤ 39221146608309^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974555209 2000000000 39221146608309 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101577279/5000000000 : ℝ)^69 ≤ (6470945299949/20000000000000 : ℝ)^53 := by
    have hnat : (2101577279 : ℕ)^69*20000000000000^53 ≤ 6470945299949^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101577279 5000000000 6470945299949 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3805120177/10000000000 : ℝ), (974555209/2000000000 : ℝ), (-2101577279/5000000000 : ℝ)] ![(2842412688327/10000000000000 : ℝ), (39221146608309/100000000000000 : ℝ), (6470945299949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3805120177/10000000000 : ℝ)|^69 ≤ (2842412688327/10000000000000 : ℝ)^53
        have hw : |(3805120177/10000000000 : ℝ)|=(3805120177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(974555209/2000000000 : ℝ)|^69 ≤ (39221146608309/100000000000000 : ℝ)^53
        have hw : |(974555209/2000000000 : ℝ)|=(974555209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2101577279/5000000000 : ℝ)|^69 ≤ (6470945299949/20000000000000 : ℝ)^53
        have hw : |(-2101577279/5000000000 : ℝ)|=(2101577279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308079 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
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
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((808979949/1000000000 : ℝ)*X 1 0+(-47897917/312500000 : ℝ)*X 1 1+(-47565767/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3207109111/10000000000 : ℝ)*X 2 0+(1503107279/2500000000 : ℝ)*X 2 1+(1760040451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-853937611/5000000000 : ℝ)*X 0 0+(728922561/2500000000 : ℝ)*X 0 1+(-1898487943/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1005799111/1250000000 : ℝ)*X 1 0+(-35590779/1250000000 : ℝ)*X 1 1+(-413313421/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1420926719/10000000000 : ℝ)*X 2 0+(1975946939/2500000000 : ℝ)*X 2 1+(1367759993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((590038191/2500000000 : ℝ)*X 0 0+(7643385163/10000000000 : ℝ)*X 0 1+(-1120009907/5000000000 : ℝ)*X 0 2+(590038191/2500000000 : ℝ)*X 1 0+(7643385163/10000000000 : ℝ)*X 1 1+(-1120009907/5000000000 : ℝ)*X 1 2+(590038191/2500000000 : ℝ)*X 2 0+(7643385163/10000000000 : ℝ)*X 2 1+(-1120009907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-292838591/10000000000 : ℝ)*X 0 0+(3562198359/10000000000 : ℝ)*X 0 1+(-7844927251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((927135263/1000000000 : ℝ)*X 1 0+(-300071401/2500000000 : ℝ)*X 1 1+(-137059803/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((389339949/1000000000 : ℝ)*X 2 0+(2926747211/5000000000 : ℝ)*X 2 1+(751648233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((9999999963/10000000000 : ℝ)*X 1 0+(201/500000000 : ℝ)*X 1 1+(9999999963/10000000000 : ℝ)*X 2 0+(201/500000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2620736413/10000000000 : ℝ)*X 0 0+(805927877/2500000000 : ℝ)*X 0 1+(-3360046619/5000000000 : ℝ)*X 0 2+(2620736413/10000000000 : ℝ)*X 1 0+(805927877/2500000000 : ℝ)*X 1 1+(-3360046619/5000000000 : ℝ)*X 1 2+(2620736413/10000000000 : ℝ)*X 2 0+(805927877/2500000000 : ℝ)*X 2 1+(-3360046619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-217622677/5000000000 : ℝ)*X 0 0+(5704245133/10000000000 : ℝ)*X 0 1+(-117725747/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((9629191957/10000000000 : ℝ)*X 1 0+(-337782577/10000000000 : ℝ)*X 1 1+(-775773713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((257283959/1000000000 : ℝ)*X 2 0+(6139753347/10000000000 : ℝ)*X 2 1+(79185137/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4371470909/10000000000 : ℝ)*X 0 0+(667949889/1250000000 : ℝ)*X 0 1+(-3095131863/10000000000 : ℝ)*X 0 2+(4371470909/10000000000 : ℝ)*X 1 0+(667949889/1250000000 : ℝ)*X 1 1+(-3095131863/10000000000 : ℝ)*X 1 2+(4371470909/10000000000 : ℝ)*X 2 0+(667949889/1250000000 : ℝ)*X 2 1+(-3095131863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((42309/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42309/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (919475330128628867589/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151353/500000000000 : ℝ)*(base18) + (746568084251/1000000000000 : ℝ)*(base39) + (967230936101/1000000000000 : ℝ)*(base49) + (1305667/500000000000 : ℝ)*(base53) + (602116083919/1000000000000 : ℝ)*(base60) + (1292010555331/500000000000 : ℝ)*(major_s0_0) + (1292010555331/500000000000 : ℝ)*(major_s0_1) + (10093822263/3906250000 : ℝ)*(major_s0_2) + (11566619/1000000000000 : ℝ)*(sp_s0_1) + (3519117817373/1000000000000 : ℝ)*(sp_s0_7) + (1759558971859/500000000000 : ℝ)*(sp_s0_8) + (439891553047/125000000000 : ℝ)*(sp_s0_9) + (51528392843/31250000000 : ℝ)*(sp_s0_13) + (11995669/1000000000000 : ℝ)*(sp_s0_14) + (51528392843/31250000000 : ℝ)*(f.failure) + (439891553047/125000000000 : ℝ)*(f.sum) + (394116034693563/625000000000000000000000000 : ℝ)*base63 + (77037734146767/156250000000000000000000000 : ℝ)*base64 + (767237567747413/5000000000000000000000000000 : ℝ)*base67 + (16426131651773/78125000000000000000000000 : ℝ)*base68 + (2106095043443957/5000000000000000000000000000 : ℝ)*base70 + (694526000654753/625000000000000000000000000 : ℝ)*base73 + (121495332470247/625000000000000000000000000 : ℝ)*base75 + (443457570247413/5000000000000000000000000000 : ℝ)*base76 + (1954640098485437/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (623/3125000000000000 : ℝ)*base87 + (623/3125000000000000 : ℝ)*base89 + (623/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((27223/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(27223/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32943627946415531546223/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1124827171329/1000000000000 : ℝ)*(base39) + (288532446153/500000000000 : ℝ)*(base49) + (394825460409/500000000000 : ℝ)*(base60) + (1562212783177/500000000000 : ℝ)*(major_s0_0) + (124976407227/40000000000 : ℝ)*(major_s0_1) + (124976407227/40000000000 : ℝ)*(major_s0_2) + (5828517/500000000000 : ℝ)*(sp_s0_1) + (23871967/1000000000000 : ℝ)*(sp_s0_7) + (851010821709/200000000000 : ℝ)*(sp_s0_14) + (265938466021/62500000000 : ℝ)*(sp_s0_15) + (132971186891/31250000000 : ℝ)*(sp_s0_16) + (15385679/1000000000000 : ℝ)*(sp_s0_17) + (1993740184591/1000000000000 : ℝ)*(sp_s0_20) + (25433571/500000000000 : ℝ)*(sp_s0_22) + (1993740184591/1000000000000 : ℝ)*(f.failure) + (132971186891/31250000000 : ℝ)*(f.sum) + (51918776189371/400000000000000000000000000 : ℝ)*base63 + (3026349786601/50000000000000000000000000 : ℝ)*base65 + (10823981202179/400000000000000000000000000 : ℝ)*base66 + (110202587477821/400000000000000000000000000 : ℝ)*base68 + (1471045345535429/5000000000000000000000000000 : ℝ)*base71 + (304535720568549/625000000000000000000000000 : ℝ)*base72 + (3966041858399/50000000000000000000000000 : ℝ)*base75 + (414718867624671/5000000000000000000000000000 : ℝ)*base76 + (7103344406151259/10000000000000000000000000000 : ℝ)*base78 + (59799/100000000000000000 : ℝ)*base86 + (59799/100000000000000000 : ℝ)*base88 + (59799/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1077/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1077/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6559994396613067506057/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4660709/1000000000000 : ℝ)*(base11) + (242631039311/250000000000 : ℝ)*(base39) + (305942146577/500000000000 : ℝ)*(base49) + (2092221/1000000000000 : ℝ)*(base50) + (2420217474487/1000000000000 : ℝ)*(major_s0_0) + (2420217474487/1000000000000 : ℝ)*(major_s0_1) + (2420217474487/1000000000000 : ℝ)*(major_s0_2) + (110327689/1000000000000 : ℝ)*(sp_s0_2) + (20188257/1000000000000 : ℝ)*(sp_s0_9) + (353467/250000000000 : ℝ)*(sp_s0_15) + (164802207623/50000000000 : ℝ)*(sp_s0_21) + (3296047399301/1000000000000 : ℝ)*(sp_s0_22) + (3295918297223/1000000000000 : ℝ)*(sp_s0_23) + (1544382637139/1000000000000 : ℝ)*(sp_s0_27) + (1544382637139/1000000000000 : ℝ)*(f.failure) + (3296048813169/1000000000000 : ℝ)*(f.sum) + (678562094656649/10000000000000000000000000000 : ℝ)*base62 + (287545606372981/1250000000000000000000000000 : ℝ)*base65 + (31221941672801/10000000000000000000000000000 : ℝ)*base67 + (3025834767327199/10000000000000000000000000000 : ℝ)*base69 + (435695995311047/10000000000000000000000000000 : ℝ)*base71 + (686482851377019/1250000000000000000000000000 : ℝ)*base72 + (190534527252019/1250000000000000000000000000 : ℝ)*base75 + (3854368850327199/10000000000000000000000000000 : ℝ)*base77 + (790376110656649/10000000000000000000000000000 : ℝ)*base79 + (10171/100000000000000000 : ℝ)*base86 + (10171/100000000000000000 : ℝ)*base88 + (10171/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (42309/100000 : ℝ) ^ (17/4 : ℝ) ≤ (2584278013240030003/100000000000000000000 : ℝ) := by
    have hpowers : (42309/100000 : ℝ)^17 ≤ (2584278013240030003/100000000000000000000 : ℝ)^4 := by
      have hnat : (42309 : ℕ)^17*100000000000000000000^4 ≤ 2584278013240030003^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42309 100000 2584278013240030003 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42309/100000 : ℝ)) (X := (2584278013240030003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102584278013240030003/100000000000000000000 : ℝ) ≤ (10060214681835667/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (102584278013240030003/100000000000000000000 : ℝ)^4 ≤ (10060214681835667/10000000000000000 : ℝ)^17 := by
      have hnat : (102584278013240030003 : ℕ)^4*10000000000000000^17 ≤ 10060214681835667^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102584278013240030003 100000000000000000000 10060214681835667 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060214681835667/10000000000000000 : ℝ)) (X := (102584278013240030003/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52584278013240030003/50000000000000000000 : ℝ) ≤ (10119280306366773/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (52584278013240030003/50000000000000000000 : ℝ)^4 ≤ (10119280306366773/10000000000000000 : ℝ)^17 := by
      have hnat : (52584278013240030003 : ℕ)^4*10000000000000000^17 ≤ 10119280306366773^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52584278013240030003 50000000000000000000 10119280306366773 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10119280306366773/10000000000000000 : ℝ)) (X := (52584278013240030003/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2230173401321/156700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(29532812265553/2115450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (42309/100000 : ℝ)) (alpha := (2230173401321/156700000000000 : ℝ)) (beta := (29532812265553/2115450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (42309/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2230173401321/156700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(29532812265553/2115450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (27223/50000 : ℝ) ^ (17/4 : ℝ) ≤ (7548408760818464621/100000000000000000000 : ℝ) := by
    have hpowers : (27223/50000 : ℝ)^17 ≤ (7548408760818464621/100000000000000000000 : ℝ)^4 := by
      have hnat : (27223 : ℕ)^17*100000000000000000000^4 ≤ 7548408760818464621^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27223 50000 7548408760818464621 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27223/50000 : ℝ)) (X := (7548408760818464621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (107548408760818464621/100000000000000000000 : ℝ) ≤ (5086349949623279/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (107548408760818464621/100000000000000000000 : ℝ)^4 ≤ (5086349949623279/5000000000000000 : ℝ)^17 := by
      have hnat : (107548408760818464621 : ℕ)^4*5000000000000000^17 ≤ 5086349949623279^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107548408760818464621 100000000000000000000 5086349949623279 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5086349949623279/5000000000000000 : ℝ)) (X := (107548408760818464621/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (57548408760818464621/50000000000000000000 : ℝ) ≤ (5168182524798153/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (57548408760818464621/50000000000000000000 : ℝ)^4 ≤ (5168182524798153/5000000000000000 : ℝ)^17 := by
      have hnat : (57548408760818464621 : ℕ)^4*5000000000000000^17 ≤ 5168182524798153^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57548408760818464621 50000000000000000000 5168182524798153 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5168182524798153/5000000000000000 : ℝ)) (X := (57548408760818464621/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(86349949623279/2722300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(40916287587437/1361150000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (27223/50000 : ℝ)) (alpha := (86349949623279/2722300000000000 : ℝ)) (beta := (40916287587437/1361150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (27223/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(86349949623279/2722300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(40916287587437/1361150000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1077/2500 : ℝ) ^ (17/4 : ℝ) ≤ (1395216830442333137/50000000000000000000 : ℝ) := by
    have hpowers : (1077/2500 : ℝ)^17 ≤ (1395216830442333137/50000000000000000000 : ℝ)^4 := by
      have hnat : (1077 : ℕ)^17*50000000000000000000^4 ≤ 1395216830442333137^4*2500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1077 2500 1395216830442333137 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1077/2500 : ℝ)) (X := (1395216830442333137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (51395216830442333137/50000000000000000000 : ℝ) ≤ (10064968026539403/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (51395216830442333137/50000000000000000000 : ℝ)^4 ≤ (10064968026539403/10000000000000000 : ℝ)^17 := by
      have hnat : (51395216830442333137 : ℕ)^4*10000000000000000^17 ≤ 10064968026539403^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51395216830442333137 50000000000000000000 10064968026539403 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10064968026539403/10000000000000000 : ℝ)) (X := (51395216830442333137/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26395216830442333137/25000000000000000000 : ℝ) ≤ (10128601038305819/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (26395216830442333137/25000000000000000000 : ℝ)^4 ≤ (10128601038305819/10000000000000000 : ℝ)^17 := by
      have hnat : (26395216830442333137 : ℕ)^4*10000000000000000^17 ≤ 10128601038305819^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26395216830442333137 25000000000000000000 10128601038305819 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10128601038305819/10000000000000000 : ℝ)) (X := (26395216830442333137/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(64968026539403/4308000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(3977063235401/269250000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1077/2500 : ℝ)) (alpha := (64968026539403/4308000000000000 : ℝ)) (beta := (3977063235401/269250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1077/2500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(64968026539403/4308000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(3977063235401/269250000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-532338541/2000000000 : ℝ)*X 0 0+(4438358013/10000000000 : ℝ)*X 0 1+(-1127523201/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((646090611/1000000000 : ℝ)*X 1 0+(-2840380139/10000000000 : ℝ)*X 1 1+(-833966761/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1926087209/5000000000 : ℝ)*X 2 0+(5192983633/10000000000 : ℝ)*X 2 1+(190687333/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3805120177/10000000000 : ℝ)*X 0 0+(974555209/2000000000 : ℝ)*X 0 1+(-2101577279/5000000000 : ℝ)*X 0 2+(3805120177/10000000000 : ℝ)*X 1 0+(974555209/2000000000 : ℝ)*X 1 1+(-2101577279/5000000000 : ℝ)*X 1 2+(3805120177/10000000000 : ℝ)*X 2 0+(974555209/2000000000 : ℝ)*X 2 1+(-2101577279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-104472505946175061966947403886173/16408264627500000000000000000000 : ℝ) := by norm_num
    linear_combination (72803/1000000000000 : ℝ)*(base12) + (17779/50000000000 : ℝ)*(base15) + (47617/500000000000 : ℝ)*(base25) + (104231858591/250000000000 : ℝ)*(base39) + (32192230907/100000000000 : ℝ)*(base49) + (31747/1000000000000 : ℝ)*(base50) + (161002744557/1000000000000 : ℝ)*(base60) + (2849/40000000000 : ℝ)*(ratio_s0_0) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (156711/100000 : ℝ)*(major_s1_2) + (2122355303541/1000000000000 : ℝ)*(sp_s1_0) + (2122355020763/1000000000000 : ℝ)*(sp_s1_1) + (212235528111/100000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2122355376343/1000000000000 : ℝ)*(f.sum) + (13581998824177817/19546114000000000000000000000 : ℝ)*base63 + (1197005227847/3590000000000000000000000 : ℝ)*base64 + (79180885757/54446000000000000000000000 : ℝ)*base66 + (203407154213/359000000000000000000000 : ℝ)*base69 + (813831757556479/5625530000000000000000000000 : ℝ)*base70 + (12773842057771/35257500000000000000000000 : ℝ)*base72 + (5258372121623/13611500000000000000000000 : ℝ)*base75 + (22106918879/1567000000000000000000000 : ℝ)*base77 + (20853626265086147/19196298450000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p008_b038 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c308079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c308080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b038 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

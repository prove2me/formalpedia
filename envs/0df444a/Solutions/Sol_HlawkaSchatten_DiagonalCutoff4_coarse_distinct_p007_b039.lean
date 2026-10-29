-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b039
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:12:56.322565+00:00
-- url     : https://prove2.me/submissions/7048655b-ca77-4a06-be98-55afc5c41188

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307086_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307086_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307086_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307086_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307086_s4
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c307086 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c307086_s0 p hpa hpb X hX
  have h1 := collision_c307086_s1 p hpa hpb X hX h0
  have h2 := collision_c307086_s2 p hpa hpb X hX h1
  have h3 := collision_c307086_s3 p hpa hpb X hX h2
  exact collision_c307086_s4 p hpa hpb X hX h3

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
theorem collision_support_c307085_s0_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1003584589/5000000000 : ℝ)*x 0 + (-3724642889/5000000000 : ℝ)*x 1 + (1444366533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003584589/5000000000 : ℝ)^17 ≤ (3061501264913/25000000000000 : ℝ)^13 := by
    have hnat : (1003584589 : ℕ)^17*25000000000000^13 ≤ 3061501264913^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003584589 5000000000 3061501264913 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3724642889/5000000000 : ℝ)^17 ≤ (34020077364951/50000000000000 : ℝ)^13 := by
    have hnat : (3724642889 : ℕ)^17*50000000000000^13 ≤ 34020077364951^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3724642889 5000000000 34020077364951 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1444366533/5000000000 : ℝ)^17 ≤ (19713840201897/100000000000000 : ℝ)^13 := by
    have hnat : (1444366533 : ℕ)^17*100000000000000^13 ≤ 19713840201897^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444366533 5000000000 19713840201897 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1003584589/5000000000 : ℝ), (-3724642889/5000000000 : ℝ), (1444366533/5000000000 : ℝ)] ![(3061501264913/25000000000000 : ℝ), (34020077364951/50000000000000 : ℝ), (19713840201897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1003584589/5000000000 : ℝ)|^17 ≤ (3061501264913/25000000000000 : ℝ)^13
        have hw : |(-1003584589/5000000000 : ℝ)|=(1003584589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3724642889/5000000000 : ℝ)|^17 ≤ (34020077364951/50000000000000 : ℝ)^13
        have hw : |(-3724642889/5000000000 : ℝ)|=(3724642889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1444366533/5000000000 : ℝ)|^17 ≤ (19713840201897/100000000000000 : ℝ)^13
        have hw : |(1444366533/5000000000 : ℝ)|=(1444366533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3378071951/5000000000 : ℝ)*x 0 + (-1138096167/5000000000 : ℝ)*x 1 + (141450399/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3378071951/5000000000 : ℝ)^17 ≤ (59882310670913/100000000000000 : ℝ)^13 := by
    have hnat : (3378071951 : ℕ)^17*100000000000000^13 ≤ 59882310670913^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3378071951 5000000000 59882310670913 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138096167/5000000000 : ℝ)^17 ≤ (3608835659383/25000000000000 : ℝ)^13 := by
    have hnat : (1138096167 : ℕ)^17*25000000000000^13 ≤ 3608835659383^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138096167 5000000000 3608835659383 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141450399/400000000 : ℝ)^17 ≤ (25682346681037/100000000000000 : ℝ)^13 := by
    have hnat : (141450399 : ℕ)^17*100000000000000^13 ≤ 25682346681037^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141450399 400000000 25682346681037 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3378071951/5000000000 : ℝ), (-1138096167/5000000000 : ℝ), (141450399/400000000 : ℝ)] ![(59882310670913/100000000000000 : ℝ), (3608835659383/25000000000000 : ℝ), (25682346681037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3378071951/5000000000 : ℝ)|^17 ≤ (59882310670913/100000000000000 : ℝ)^13
        have hw : |(3378071951/5000000000 : ℝ)|=(3378071951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138096167/5000000000 : ℝ)|^17 ≤ (3608835659383/25000000000000 : ℝ)^13
        have hw : |(-1138096167/5000000000 : ℝ)|=(1138096167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141450399/400000000 : ℝ)|^17 ≤ (25682346681037/100000000000000 : ℝ)^13
        have hw : |(141450399/400000000 : ℝ)|=(141450399/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1534045057/10000000000 : ℝ)*x 0 + (-2061797287/2500000000 : ℝ)*x 1 + (2182072251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1534045057/10000000000 : ℝ)^17 ≤ (215410453607/2500000000000 : ℝ)^13 := by
    have hnat : (1534045057 : ℕ)^17*2500000000000^13 ≤ 215410453607^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534045057 10000000000 215410453607 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061797287/2500000000 : ℝ)^17 ≤ (1943094623209/2500000000000 : ℝ)^13 := by
    have hnat : (2061797287 : ℕ)^17*2500000000000^13 ≤ 1943094623209^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061797287 2500000000 1943094623209 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182072251/10000000000 : ℝ)^17 ≤ (13659796907317/100000000000000 : ℝ)^13 := by
    have hnat : (2182072251 : ℕ)^17*100000000000000^13 ≤ 13659796907317^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182072251 10000000000 13659796907317 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1534045057/10000000000 : ℝ), (-2061797287/2500000000 : ℝ), (2182072251/10000000000 : ℝ)] ![(215410453607/2500000000000 : ℝ), (1943094623209/2500000000000 : ℝ), (13659796907317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1534045057/10000000000 : ℝ)|^17 ≤ (215410453607/2500000000000 : ℝ)^13
        have hw : |(-1534045057/10000000000 : ℝ)|=(1534045057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061797287/2500000000 : ℝ)|^17 ≤ (1943094623209/2500000000000 : ℝ)^13
        have hw : |(-2061797287/2500000000 : ℝ)|=(2061797287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2182072251/10000000000 : ℝ)|^17 ≤ (13659796907317/100000000000000 : ℝ)^13
        have hw : |(2182072251/10000000000 : ℝ)|=(2182072251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5662062739/10000000000 : ℝ)*x 0 + (164210597/625000000 : ℝ)*x 1 + (897228033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5662062739/10000000000 : ℝ)^17 ≤ (47529898372271/100000000000000 : ℝ)^13 := by
    have hnat : (5662062739 : ℕ)^17*100000000000000^13 ≤ 47529898372271^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662062739 10000000000 47529898372271 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164210597/625000000 : ℝ)^17 ≤ (17414551325921/100000000000000 : ℝ)^13 := by
    have hnat : (164210597 : ℕ)^17*100000000000000^13 ≤ 17414551325921^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164210597 625000000 17414551325921 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897228033/2000000000 : ℝ)^17 ≤ (35055550288227/100000000000000 : ℝ)^13 := by
    have hnat : (897228033 : ℕ)^17*100000000000000^13 ≤ 35055550288227^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897228033 2000000000 35055550288227 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5662062739/10000000000 : ℝ), (164210597/625000000 : ℝ), (897228033/2000000000 : ℝ)] ![(47529898372271/100000000000000 : ℝ), (17414551325921/100000000000000 : ℝ), (35055550288227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5662062739/10000000000 : ℝ)|^17 ≤ (47529898372271/100000000000000 : ℝ)^13
        have hw : |(5662062739/10000000000 : ℝ)|=(5662062739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164210597/625000000 : ℝ)|^17 ≤ (17414551325921/100000000000000 : ℝ)^13
        have hw : |(164210597/625000000 : ℝ)|=(164210597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897228033/2000000000 : ℝ)|^17 ≤ (35055550288227/100000000000000 : ℝ)^13
        have hw : |(897228033/2000000000 : ℝ)|=(897228033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4180368643/10000000000 : ℝ)*x 0 + (-1310651549/5000000000 : ℝ)*x 1 + (-1486570811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180368643/10000000000 : ℝ)^17 ≤ (31964301751647/100000000000000 : ℝ)^13 := by
    have hnat : (4180368643 : ℕ)^17*100000000000000^13 ≤ 31964301751647^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180368643 10000000000 31964301751647 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310651549/5000000000 : ℝ)^17 ≤ (1736198867937/10000000000000 : ℝ)^13 := by
    have hnat : (1310651549 : ℕ)^17*10000000000000^13 ≤ 1736198867937^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310651549 5000000000 1736198867937 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1486570811/2500000000 : ℝ)^17 ≤ (25336854775209/50000000000000 : ℝ)^13 := by
    have hnat : (1486570811 : ℕ)^17*50000000000000^13 ≤ 25336854775209^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486570811 2500000000 25336854775209 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180368643/10000000000 : ℝ), (-1310651549/5000000000 : ℝ), (-1486570811/2500000000 : ℝ)] ![(31964301751647/100000000000000 : ℝ), (1736198867937/10000000000000 : ℝ), (25336854775209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180368643/10000000000 : ℝ)|^17 ≤ (31964301751647/100000000000000 : ℝ)^13
        have hw : |(4180368643/10000000000 : ℝ)|=(4180368643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1310651549/5000000000 : ℝ)|^17 ≤ (1736198867937/10000000000000 : ℝ)^13
        have hw : |(-1310651549/5000000000 : ℝ)|=(1310651549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1486570811/2500000000 : ℝ)|^17 ≤ (25336854775209/50000000000000 : ℝ)^13
        have hw : |(-1486570811/2500000000 : ℝ)|=(1486570811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_11 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (-1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^17 ≤ (1 : ℝ)^13 := by
    have hnat : (1 : ℕ)^17*1^13 ≤ 1^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1 : ℝ)|^17 ≤ (1 : ℝ)^13
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (244204249/400000000 : ℝ)*x 0 + (-156765789/1000000000 : ℝ)*x 1 + (4837170393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (244204249/400000000 : ℝ)^17 ≤ (2622543393539/5000000000000 : ℝ)^13 := by
    have hnat : (244204249 : ℕ)^17*5000000000000^13 ≤ 2622543393539^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244204249 400000000 2622543393539 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156765789/1000000000 : ℝ)^17 ≤ (8864133857099/100000000000000 : ℝ)^13 := by
    have hnat : (156765789 : ℕ)^17*100000000000000^13 ≤ 8864133857099^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156765789 1000000000 8864133857099 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4837170393/10000000000 : ℝ)^17 ≤ (38684998264169/100000000000000 : ℝ)^13 := by
    have hnat : (4837170393 : ℕ)^17*100000000000000^13 ≤ 38684998264169^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837170393 10000000000 38684998264169 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(244204249/400000000 : ℝ), (-156765789/1000000000 : ℝ), (4837170393/10000000000 : ℝ)] ![(2622543393539/5000000000000 : ℝ), (8864133857099/100000000000000 : ℝ), (38684998264169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(244204249/400000000 : ℝ)|^17 ≤ (2622543393539/5000000000000 : ℝ)^13
        have hw : |(244204249/400000000 : ℝ)|=(244204249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156765789/1000000000 : ℝ)|^17 ≤ (8864133857099/100000000000000 : ℝ)^13
        have hw : |(-156765789/1000000000 : ℝ)|=(156765789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4837170393/10000000000 : ℝ)|^17 ≤ (38684998264169/100000000000000 : ℝ)^13
        have hw : |(4837170393/10000000000 : ℝ)|=(4837170393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-940562131/5000000000 : ℝ)*x 0 + (-3760473291/5000000000 : ℝ)*x 1 + (2904249237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940562131/5000000000 : ℝ)^17 ≤ (2812557014539/25000000000000 : ℝ)^13 := by
    have hnat : (940562131 : ℕ)^17*25000000000000^13 ≤ 2812557014539^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940562131 5000000000 2812557014539 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3760473291/5000000000 : ℝ)^17 ≤ (68897347999383/100000000000000 : ℝ)^13 := by
    have hnat : (3760473291 : ℕ)^17*100000000000000^13 ≤ 68897347999383^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760473291 5000000000 68897347999383 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2904249237/10000000000 : ℝ)^17 ≤ (9926211963823/50000000000000 : ℝ)^13 := by
    have hnat : (2904249237 : ℕ)^17*50000000000000^13 ≤ 9926211963823^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2904249237 10000000000 9926211963823 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-940562131/5000000000 : ℝ), (-3760473291/5000000000 : ℝ), (2904249237/10000000000 : ℝ)] ![(2812557014539/25000000000000 : ℝ), (68897347999383/100000000000000 : ℝ), (9926211963823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-940562131/5000000000 : ℝ)|^17 ≤ (2812557014539/25000000000000 : ℝ)^13
        have hw : |(-940562131/5000000000 : ℝ)|=(940562131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3760473291/5000000000 : ℝ)|^17 ≤ (68897347999383/100000000000000 : ℝ)^13
        have hw : |(-3760473291/5000000000 : ℝ)|=(3760473291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2904249237/10000000000 : ℝ)|^17 ≤ (9926211963823/50000000000000 : ℝ)^13
        have hw : |(2904249237/10000000000 : ℝ)|=(2904249237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4696490189/10000000000 : ℝ)*x 0 + (592348303/2000000000 : ℝ)*x 1 + (2594814883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4696490189/10000000000 : ℝ)^17 ≤ (7444072960591/20000000000000 : ℝ)^13 := by
    have hnat : (4696490189 : ℕ)^17*20000000000000^13 ≤ 7444072960591^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696490189 10000000000 7444072960591 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (592348303/2000000000 : ℝ)^17 ≤ (20367901071537/100000000000000 : ℝ)^13 := by
    have hnat : (592348303 : ℕ)^17*100000000000000^13 ≤ 20367901071537^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592348303 2000000000 20367901071537 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594814883/5000000000 : ℝ)^17 ≤ (5301466763517/12500000000000 : ℝ)^13 := by
    have hnat : (2594814883 : ℕ)^17*12500000000000^13 ≤ 5301466763517^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594814883 5000000000 5301466763517 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4696490189/10000000000 : ℝ), (592348303/2000000000 : ℝ), (2594814883/5000000000 : ℝ)] ![(7444072960591/20000000000000 : ℝ), (20367901071537/100000000000000 : ℝ), (5301466763517/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4696490189/10000000000 : ℝ)|^17 ≤ (7444072960591/20000000000000 : ℝ)^13
        have hw : |(4696490189/10000000000 : ℝ)|=(4696490189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(592348303/2000000000 : ℝ)|^17 ≤ (20367901071537/100000000000000 : ℝ)^13
        have hw : |(592348303/2000000000 : ℝ)|=(592348303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594814883/5000000000 : ℝ)|^17 ≤ (5301466763517/12500000000000 : ℝ)^13
        have hw : |(2594814883/5000000000 : ℝ)|=(2594814883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4173504651/10000000000 : ℝ)*x 0 + (-2935394483/10000000000 : ℝ)*x 1 + (-356399133/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173504651/10000000000 : ℝ)^17 ≤ (398696076203/1250000000000 : ℝ)^13 := by
    have hnat : (4173504651 : ℕ)^17*1250000000000^13 ≤ 398696076203^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173504651 10000000000 398696076203 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2935394483/10000000000 : ℝ)^17 ≤ (2013128709721/10000000000000 : ℝ)^13 := by
    have hnat : (2935394483 : ℕ)^17*10000000000000^13 ≤ 2013128709721^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935394483 10000000000 2013128709721 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356399133/625000000 : ℝ)^17 ≤ (23986513391501/50000000000000 : ℝ)^13 := by
    have hnat : (356399133 : ℕ)^17*50000000000000^13 ≤ 23986513391501^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356399133 625000000 23986513391501 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173504651/10000000000 : ℝ), (-2935394483/10000000000 : ℝ), (-356399133/625000000 : ℝ)] ![(398696076203/1250000000000 : ℝ), (2013128709721/10000000000000 : ℝ), (23986513391501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173504651/10000000000 : ℝ)|^17 ≤ (398696076203/1250000000000 : ℝ)^13
        have hw : |(4173504651/10000000000 : ℝ)|=(4173504651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2935394483/10000000000 : ℝ)|^17 ≤ (2013128709721/10000000000000 : ℝ)^13
        have hw : |(-2935394483/10000000000 : ℝ)|=(2935394483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356399133/625000000 : ℝ)|^17 ≤ (23986513391501/50000000000000 : ℝ)^13
        have hw : |(-356399133/625000000 : ℝ)|=(356399133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1051989981/1250000000 : ℝ)*x 0 + (-1456395853/10000000000 : ℝ)*x 1 + (498457179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051989981/1250000000 : ℝ)^17 ≤ (9976218195429/12500000000000 : ℝ)^13 := by
    have hnat : (1051989981 : ℕ)^17*12500000000000^13 ≤ 9976218195429^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051989981 1250000000 9976218195429 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1456395853/10000000000 : ℝ)^17 ≤ (1610115190501/20000000000000 : ℝ)^13 := by
    have hnat : (1456395853 : ℕ)^17*20000000000000^13 ≤ 1610115190501^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456395853 10000000000 1610115190501 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (498457179/2500000000 : ℝ)^17 ≤ (1517459808063/12500000000000 : ℝ)^13 := by
    have hnat : (498457179 : ℕ)^17*12500000000000^13 ≤ 1517459808063^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498457179 2500000000 1517459808063 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051989981/1250000000 : ℝ), (-1456395853/10000000000 : ℝ), (498457179/2500000000 : ℝ)] ![(9976218195429/12500000000000 : ℝ), (1610115190501/20000000000000 : ℝ), (1517459808063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051989981/1250000000 : ℝ)|^17 ≤ (9976218195429/12500000000000 : ℝ)^13
        have hw : |(1051989981/1250000000 : ℝ)|=(1051989981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1456395853/10000000000 : ℝ)|^17 ≤ (1610115190501/20000000000000 : ℝ)^13
        have hw : |(-1456395853/10000000000 : ℝ)|=(1456395853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(498457179/2500000000 : ℝ)|^17 ≤ (1517459808063/12500000000000 : ℝ)^13
        have hw : |(498457179/2500000000 : ℝ)|=(498457179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1315531479/10000000000 : ℝ)*x 0 + (-8166286269/10000000000 : ℝ)*x 1 + (248886673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315531479/10000000000 : ℝ)^17 ≤ (1409566174721/20000000000000 : ℝ)^13 := by
    have hnat : (1315531479 : ℕ)^17*20000000000000^13 ≤ 1409566174721^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315531479 10000000000 1409566174721 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8166286269/10000000000 : ℝ)^17 ≤ (38364120863819/50000000000000 : ℝ)^13 := by
    have hnat : (8166286269 : ℕ)^17*50000000000000^13 ≤ 38364120863819^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8166286269 10000000000 38364120863819 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248886673/1000000000 : ℝ)^17 ≤ (16223927382481/100000000000000 : ℝ)^13 := by
    have hnat : (248886673 : ℕ)^17*100000000000000^13 ≤ 16223927382481^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248886673 1000000000 16223927382481 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1315531479/10000000000 : ℝ), (-8166286269/10000000000 : ℝ), (248886673/1000000000 : ℝ)] ![(1409566174721/20000000000000 : ℝ), (38364120863819/50000000000000 : ℝ), (16223927382481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1315531479/10000000000 : ℝ)|^17 ≤ (1409566174721/20000000000000 : ℝ)^13
        have hw : |(-1315531479/10000000000 : ℝ)|=(1315531479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8166286269/10000000000 : ℝ)|^17 ≤ (38364120863819/50000000000000 : ℝ)^13
        have hw : |(-8166286269/10000000000 : ℝ)|=(8166286269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(248886673/1000000000 : ℝ)|^17 ≤ (16223927382481/100000000000000 : ℝ)^13
        have hw : |(248886673/1000000000 : ℝ)|=(248886673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6332279763/10000000000 : ℝ)*x 0 + (2550366911/10000000000 : ℝ)*x 1 + (118804191/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6332279763/10000000000 : ℝ)^17 ≤ (13754400627439/25000000000000 : ℝ)^13 := by
    have hnat : (6332279763 : ℕ)^17*25000000000000^13 ≤ 13754400627439^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6332279763 10000000000 13754400627439 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2550366911/10000000000 : ℝ)^17 ≤ (3350031305301/20000000000000 : ℝ)^13 := by
    have hnat : (2550366911 : ℕ)^17*20000000000000^13 ≤ 3350031305301^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550366911 10000000000 3350031305301 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118804191/312500000 : ℝ)^17 ≤ (3529030118359/12500000000000 : ℝ)^13 := by
    have hnat : (118804191 : ℕ)^17*12500000000000^13 ≤ 3529030118359^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118804191 312500000 3529030118359 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6332279763/10000000000 : ℝ), (2550366911/10000000000 : ℝ), (118804191/312500000 : ℝ)] ![(13754400627439/25000000000000 : ℝ), (3350031305301/20000000000000 : ℝ), (3529030118359/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6332279763/10000000000 : ℝ)|^17 ≤ (13754400627439/25000000000000 : ℝ)^13
        have hw : |(6332279763/10000000000 : ℝ)|=(6332279763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2550366911/10000000000 : ℝ)|^17 ≤ (3350031305301/20000000000000 : ℝ)^13
        have hw : |(2550366911/10000000000 : ℝ)|=(2550366911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118804191/312500000 : ℝ)|^17 ≤ (3529030118359/12500000000000 : ℝ)^13
        have hw : |(118804191/312500000 : ℝ)|=(118804191/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3480835443/10000000000 : ℝ)*x 0 + (-336522811/1000000000 : ℝ)*x 1 + (-2977573621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3480835443/10000000000 : ℝ)^17 ≤ (6289310515779/25000000000000 : ℝ)^13 := by
    have hnat : (3480835443 : ℕ)^17*25000000000000^13 ≤ 6289310515779^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3480835443 10000000000 6289310515779 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336522811/1000000000 : ℝ)^17 ≤ (12035122489403/50000000000000 : ℝ)^13 := by
    have hnat : (336522811 : ℕ)^17*50000000000000^13 ≤ 12035122489403^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336522811 1000000000 12035122489403 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2977573621/5000000000 : ℝ)^17 ≤ (2030900517903/4000000000000 : ℝ)^13 := by
    have hnat : (2977573621 : ℕ)^17*4000000000000^13 ≤ 2030900517903^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2977573621 5000000000 2030900517903 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3480835443/10000000000 : ℝ), (-336522811/1000000000 : ℝ), (-2977573621/5000000000 : ℝ)] ![(6289310515779/25000000000000 : ℝ), (12035122489403/50000000000000 : ℝ), (2030900517903/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3480835443/10000000000 : ℝ)|^17 ≤ (6289310515779/25000000000000 : ℝ)^13
        have hw : |(3480835443/10000000000 : ℝ)|=(3480835443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336522811/1000000000 : ℝ)|^17 ≤ (12035122489403/50000000000000 : ℝ)^13
        have hw : |(-336522811/1000000000 : ℝ)|=(336522811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2977573621/5000000000 : ℝ)|^17 ≤ (2030900517903/4000000000000 : ℝ)^13
        have hw : |(-2977573621/5000000000 : ℝ)|=(2977573621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s0_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1044189773/1250000000 : ℝ)*x 0 + (-730958807/10000000000 : ℝ)*x 1 + (2659655837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044189773/1250000000 : ℝ)^17 ≤ (4939798818479/6250000000000 : ℝ)^13 := by
    have hnat : (1044189773 : ℕ)^17*6250000000000^13 ≤ 4939798818479^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044189773 1250000000 4939798818479 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730958807/10000000000 : ℝ)^17 ≤ (817074199871/25000000000000 : ℝ)^13 := by
    have hnat : (730958807 : ℕ)^17*25000000000000^13 ≤ 817074199871^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730958807 10000000000 817074199871 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2659655837/10000000000 : ℝ)^17 ≤ (8847461047127/50000000000000 : ℝ)^13 := by
    have hnat : (2659655837 : ℕ)^17*50000000000000^13 ≤ 8847461047127^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659655837 10000000000 8847461047127 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044189773/1250000000 : ℝ), (-730958807/10000000000 : ℝ), (2659655837/10000000000 : ℝ)] ![(4939798818479/6250000000000 : ℝ), (817074199871/25000000000000 : ℝ), (8847461047127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044189773/1250000000 : ℝ)|^17 ≤ (4939798818479/6250000000000 : ℝ)^13
        have hw : |(1044189773/1250000000 : ℝ)|=(1044189773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-730958807/10000000000 : ℝ)|^17 ≤ (817074199871/25000000000000 : ℝ)^13
        have hw : |(-730958807/10000000000 : ℝ)|=(730958807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2659655837/10000000000 : ℝ)|^17 ≤ (8847461047127/50000000000000 : ℝ)^13
        have hw : |(2659655837/10000000000 : ℝ)|=(2659655837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-415430333/1250000000 : ℝ)*x 0 + (-2760251701/5000000000 : ℝ)*x 1 + (4016715483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415430333/1250000000 : ℝ)^17 ≤ (23680155891291/100000000000000 : ℝ)^13 := by
    have hnat : (415430333 : ℕ)^17*100000000000000^13 ≤ 23680155891291^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415430333 1250000000 23680155891291 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760251701/5000000000 : ℝ)^17 ≤ (9196392587079/20000000000000 : ℝ)^13 := by
    have hnat : (2760251701 : ℕ)^17*20000000000000^13 ≤ 9196392587079^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760251701 5000000000 9196392587079 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016715483/10000000000 : ℝ)^17 ≤ (15168940581511/50000000000000 : ℝ)^13 := by
    have hnat : (4016715483 : ℕ)^17*50000000000000^13 ≤ 15168940581511^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016715483 10000000000 15168940581511 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415430333/1250000000 : ℝ), (-2760251701/5000000000 : ℝ), (4016715483/10000000000 : ℝ)] ![(23680155891291/100000000000000 : ℝ), (9196392587079/20000000000000 : ℝ), (15168940581511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415430333/1250000000 : ℝ)|^17 ≤ (23680155891291/100000000000000 : ℝ)^13
        have hw : |(-415430333/1250000000 : ℝ)|=(415430333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2760251701/5000000000 : ℝ)|^17 ≤ (9196392587079/20000000000000 : ℝ)^13
        have hw : |(-2760251701/5000000000 : ℝ)|=(2760251701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016715483/10000000000 : ℝ)|^17 ≤ (15168940581511/50000000000000 : ℝ)^13
        have hw : |(4016715483/10000000000 : ℝ)|=(4016715483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5269542797/10000000000 : ℝ)*x 0 + (683781909/2000000000 : ℝ)*x 1 + (2099895349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5269542797/10000000000 : ℝ)^17 ≤ (10816944895847/25000000000000 : ℝ)^13 := by
    have hnat : (5269542797 : ℕ)^17*25000000000000^13 ≤ 10816944895847^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5269542797 10000000000 10816944895847 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683781909/2000000000 : ℝ)^17 ≤ (12286789512027/50000000000000 : ℝ)^13 := by
    have hnat : (683781909 : ℕ)^17*50000000000000^13 ≤ 12286789512027^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683781909 2000000000 12286789512027 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099895349/5000000000 : ℝ)^17 ≤ (32158641379907/100000000000000 : ℝ)^13 := by
    have hnat : (2099895349 : ℕ)^17*100000000000000^13 ≤ 32158641379907^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099895349 5000000000 32158641379907 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5269542797/10000000000 : ℝ), (683781909/2000000000 : ℝ), (2099895349/5000000000 : ℝ)] ![(10816944895847/25000000000000 : ℝ), (12286789512027/50000000000000 : ℝ), (32158641379907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5269542797/10000000000 : ℝ)|^17 ≤ (10816944895847/25000000000000 : ℝ)^13
        have hw : |(5269542797/10000000000 : ℝ)|=(5269542797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683781909/2000000000 : ℝ)|^17 ≤ (12286789512027/50000000000000 : ℝ)^13
        have hw : |(683781909/2000000000 : ℝ)|=(683781909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2099895349/5000000000 : ℝ)|^17 ≤ (32158641379907/100000000000000 : ℝ)^13
        have hw : |(2099895349/5000000000 : ℝ)|=(2099895349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4059281077/10000000000 : ℝ)*x 0 + (-793121569/2000000000 : ℝ)*x 1 + (-4906050381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4059281077/10000000000 : ℝ)^17 ≤ (30758980140287/100000000000000 : ℝ)^13 := by
    have hnat : (4059281077 : ℕ)^17*100000000000000^13 ≤ 30758980140287^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4059281077 10000000000 30758980140287 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (793121569/2000000000 : ℝ)^17 ≤ (14917044112141/50000000000000 : ℝ)^13 := by
    have hnat : (793121569 : ℕ)^17*50000000000000^13 ≤ 14917044112141^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793121569 2000000000 14917044112141 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4906050381/10000000000 : ℝ)^17 ≤ (39406931617547/100000000000000 : ℝ)^13 := by
    have hnat : (4906050381 : ℕ)^17*100000000000000^13 ≤ 39406931617547^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906050381 10000000000 39406931617547 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4059281077/10000000000 : ℝ), (-793121569/2000000000 : ℝ), (-4906050381/10000000000 : ℝ)] ![(30758980140287/100000000000000 : ℝ), (14917044112141/50000000000000 : ℝ), (39406931617547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4059281077/10000000000 : ℝ)|^17 ≤ (30758980140287/100000000000000 : ℝ)^13
        have hw : |(4059281077/10000000000 : ℝ)|=(4059281077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-793121569/2000000000 : ℝ)|^17 ≤ (14917044112141/50000000000000 : ℝ)^13
        have hw : |(-793121569/2000000000 : ℝ)|=(793121569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4906050381/10000000000 : ℝ)|^17 ≤ (39406931617547/100000000000000 : ℝ)^13
        have hw : |(-4906050381/10000000000 : ℝ)|=(4906050381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307085_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (962300379/2000000000 : ℝ)*x 0 + (-857309019/2000000000 : ℝ)*x 1 + (766947027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962300379/2000000000 : ℝ)^17 ≤ (19208385756631/50000000000000 : ℝ)^13 := by
    have hnat : (962300379 : ℕ)^17*50000000000000^13 ≤ 19208385756631^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962300379 2000000000 19208385756631 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (857309019/2000000000 : ℝ)^17 ≤ (3303008359939/10000000000000 : ℝ)^13 := by
    have hnat : (857309019 : ℕ)^17*10000000000000^13 ≤ 3303008359939^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857309019 2000000000 3303008359939 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766947027/2000000000 : ℝ)^17 ≤ (28553144869577/100000000000000 : ℝ)^13 := by
    have hnat : (766947027 : ℕ)^17*100000000000000^13 ≤ 28553144869577^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766947027 2000000000 28553144869577 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(962300379/2000000000 : ℝ), (-857309019/2000000000 : ℝ), (766947027/2000000000 : ℝ)] ![(19208385756631/50000000000000 : ℝ), (3303008359939/10000000000000 : ℝ), (28553144869577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(962300379/2000000000 : ℝ)|^17 ≤ (19208385756631/50000000000000 : ℝ)^13
        have hw : |(962300379/2000000000 : ℝ)|=(962300379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-857309019/2000000000 : ℝ)|^17 ≤ (3303008359939/10000000000000 : ℝ)^13
        have hw : |(-857309019/2000000000 : ℝ)|=(857309019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(766947027/2000000000 : ℝ)|^17 ≤ (28553144869577/100000000000000 : ℝ)^13
        have hw : |(766947027/2000000000 : ℝ)|=(766947027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307085 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1003584589/5000000000 : ℝ)*X 0 0+(-3724642889/5000000000 : ℝ)*X 0 1+(1444366533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3378071951/5000000000 : ℝ)*X 0 0+(-1138096167/5000000000 : ℝ)*X 0 1+(141450399/400000000 : ℝ)*X 0 2+(3378071951/5000000000 : ℝ)*X 1 0+(-1138096167/5000000000 : ℝ)*X 1 1+(141450399/400000000 : ℝ)*X 1 2+(3378071951/5000000000 : ℝ)*X 2 0+(-1138096167/5000000000 : ℝ)*X 2 1+(141450399/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1534045057/10000000000 : ℝ)*X 0 0+(-2061797287/2500000000 : ℝ)*X 0 1+(2182072251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5662062739/10000000000 : ℝ)*X 1 0+(164210597/625000000 : ℝ)*X 1 1+(897228033/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4180368643/10000000000 : ℝ)*X 2 0+(-1310651549/5000000000 : ℝ)*X 2 1+(-1486570811/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_11 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_11 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((244204249/400000000 : ℝ)*X 0 0+(-156765789/1000000000 : ℝ)*X 0 1+(4837170393/10000000000 : ℝ)*X 0 2+(244204249/400000000 : ℝ)*X 1 0+(-156765789/1000000000 : ℝ)*X 1 1+(4837170393/10000000000 : ℝ)*X 1 2+(244204249/400000000 : ℝ)*X 2 0+(-156765789/1000000000 : ℝ)*X 2 1+(4837170393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-940562131/5000000000 : ℝ)*X 0 0+(-3760473291/5000000000 : ℝ)*X 0 1+(2904249237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4696490189/10000000000 : ℝ)*X 1 0+(592348303/2000000000 : ℝ)*X 1 1+(2594814883/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4173504651/10000000000 : ℝ)*X 2 0+(-2935394483/10000000000 : ℝ)*X 2 1+(-356399133/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1051989981/1250000000 : ℝ)*X 0 0+(-1456395853/10000000000 : ℝ)*X 0 1+(498457179/2500000000 : ℝ)*X 0 2+(1051989981/1250000000 : ℝ)*X 1 0+(-1456395853/10000000000 : ℝ)*X 1 1+(498457179/2500000000 : ℝ)*X 1 2+(1051989981/1250000000 : ℝ)*X 2 0+(-1456395853/10000000000 : ℝ)*X 2 1+(498457179/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1315531479/10000000000 : ℝ)*X 0 0+(-8166286269/10000000000 : ℝ)*X 0 1+(248886673/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6332279763/10000000000 : ℝ)*X 1 0+(2550366911/10000000000 : ℝ)*X 1 1+(118804191/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3480835443/10000000000 : ℝ)*X 2 0+(-336522811/1000000000 : ℝ)*X 2 1+(-2977573621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1044189773/1250000000 : ℝ)*X 0 0+(-730958807/10000000000 : ℝ)*X 0 1+(2659655837/10000000000 : ℝ)*X 0 2+(1044189773/1250000000 : ℝ)*X 1 0+(-730958807/10000000000 : ℝ)*X 1 1+(2659655837/10000000000 : ℝ)*X 1 2+(1044189773/1250000000 : ℝ)*X 2 0+(-730958807/10000000000 : ℝ)*X 2 1+(2659655837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((18907/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18907/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18866158604725185109881/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2635056284193/1000000000000 : ℝ)*(base3) + (113497691669/125000000000 : ℝ)*(base40) + (1051690557421/500000000000 : ℝ)*(base50) + (1024039945287/250000000000 : ℝ)*(major_s0_0) + (2184419877361/500000000000 : ℝ)*(major_s0_1) + (1024039945287/250000000000 : ℝ)*(major_s0_2) + (977349/125000000000 : ℝ)*(sp_s0_6) + (173664047257/31250000000 : ℝ)*(sp_s0_7) + (8192278237631/1000000000000 : ℝ)*(sp_s0_8) + (5557215653213/1000000000000 : ℝ)*(sp_s0_9) + (136339986787/500000000000 : ℝ)*(sp_s0_11) + (428949/125000000000 : ℝ)*(sp_s0_13) + (13779393/500000000000 : ℝ)*(sp_s0_15) + (8464753/250000000000 : ℝ)*(sp_s0_23) + (164691720911/62500000000 : ℝ)*(f.failure) + (173664047257/31250000000 : ℝ)*(f.sum) + (2703504498145823/5000000000000000000000000000 : ℝ)*base62 + (57265290084241/500000000000000000000000000 : ℝ)*base65 + (795058291796219/2500000000000000000000000000 : ℝ)*base66 + (653264542052427/1250000000000000000000000000 : ℝ)*base68 + (1514745164566351/2500000000000000000000000000 : ℝ)*base71 + (340161914434241/500000000000000000000000000 : ℝ)*base72 + (920628014987223/1000000000000000000000000000 : ℝ)*base74 + (1058051839072573/1250000000000000000000000000 : ℝ)*base77 + (21762317326089/156250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (117/390625000000000 : ℝ)*base86 + (117/390625000000000 : ℝ)*base88 + (117/390625000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-14917/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-14917/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (962145126668498980863/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (995434273649/1000000000000 : ℝ)*(base40) + (39178995777/1000000000000 : ℝ)*(base50) + (132358916939/1000000000000 : ℝ)*(base59) + (694758321053/200000000000 : ℝ)*(major_s0_0) + (694758321053/200000000000 : ℝ)*(major_s0_1) + (694758321053/200000000000 : ℝ)*(major_s0_2) + (5680223/62500000000 : ℝ)*(sp_s0_0) + (7157983/1000000000000 : ℝ)*(sp_s0_7) + (1519623/200000000000 : ℝ)*(sp_s0_8) + (139356013/1000000000000 : ℝ)*(sp_s0_9) + (1178196671471/250000000000 : ℝ)*(sp_s0_14) + (117821928233/25000000000 : ℝ)*(sp_s0_15) + (4712745371423/1000000000000 : ℝ)*(sp_s0_16) + (2234696879513/1000000000000 : ℝ)*(sp_s0_20) + (2234696879513/1000000000000 : ℝ)*(f.failure) + (1178221181859/250000000000 : ℝ)*(f.sum) + (444364320640679/2000000000000000000000000000 : ℝ)*base63 + (203250659926379/400000000000000000000000000 : ℝ)*base65 + (179098004563713/1000000000000000000000000000 : ℝ)*base67 + (169688757163713/1000000000000000000000000000 : ℝ)*base68 + (1294760851904469/2000000000000000000000000000 : ℝ)*base71 + (113964697446379/400000000000000000000000000 : ℝ)*base72 + (93898271566379/400000000000000000000000000 : ℝ)*base74 + (535251208936287/1000000000000000000000000000 : ℝ)*base77 + (1278522411495531/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (4603/12500000000000000 : ℝ)*base87 + (4603/12500000000000000 : ℝ)*base89 + (4603/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5157/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5157/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4560100327525534440183/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85505873673/62500000000 : ℝ)*(base3) + (1961940531411/1000000000000 : ℝ)*(base40) + (1782921740949/1000000000000 : ℝ)*(base50) + (55579240939/500000000000 : ℝ)*(base59) + (1464490465557/250000000000 : ℝ)*(major_s0_0) + (1464490465557/250000000000 : ℝ)*(major_s0_1) + (1464490465557/250000000000 : ℝ)*(major_s0_2) + (123629197/1000000000000 : ℝ)*(sp_s0_7) + (174087/25000000000 : ℝ)*(sp_s0_14) + (6708691/200000000000 : ℝ)*(sp_s0_20) + (3973676234071/500000000000 : ℝ)*(sp_s0_21) + (9315577039587/1000000000000 : ℝ)*(sp_s0_22) + (7947483060819/1000000000000 : ℝ)*(sp_s0_23) + (1200155354679/500000000000 : ℝ)*(sp_s0_27) + (3768438231581/1000000000000 : ℝ)*(f.failure) + (7947483060819/1000000000000 : ℝ)*(f.sum) + (1034638492431551/2500000000000000000000000000 : ℝ)*base63 + (58990839954851/500000000000000000000000000 : ℝ)*base65 + (302831496022097/1250000000000000000000000000 : ℝ)*base67 + (303794981772097/1250000000000000000000000000 : ℝ)*base68 + (1154807983269939/2500000000000000000000000000 : ℝ)*base70 + (8912238295149/500000000000000000000000000 : ℝ)*base73 + (94092220345149/500000000000000000000000000 : ℝ)*base75 + (22536393772097/1250000000000000000000000000 : ℝ)*base76 + (1890017242269939/2500000000000000000000000000 : ℝ)*base79 + (411/12500000000000000 : ℝ)*base87 + (411/12500000000000000 : ℝ)*base89 + (411/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (18907/100000 : ℝ) ^ (135/32 : ℝ) ≤ (3550681253243623/4000000000000000000 : ℝ) := by
    have hpowers : (18907/100000 : ℝ)^135 ≤ (3550681253243623/4000000000000000000 : ℝ)^32 := by
      have hnat : (18907 : ℕ)^135*4000000000000000000^32 ≤ 3550681253243623^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18907 100000 3550681253243623 4000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18907/100000 : ℝ)) (X := (3550681253243623/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (4003550681253243623/4000000000000000000 : ℝ) ≤ (5001051697633669/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (4003550681253243623/4000000000000000000 : ℝ)^32 ≤ (5001051697633669/5000000000000000 : ℝ)^135 := by
      have hnat : (4003550681253243623 : ℕ)^32*5000000000000000^135 ≤ 5001051697633669^135*4000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4003550681253243623 4000000000000000000 5001051697633669 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001051697633669/5000000000000000 : ℝ)) (X := (4003550681253243623/4000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2003550681253243623/2000000000000000000 : ℝ) ≤ (625262835483417/625000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2003550681253243623/2000000000000000000 : ℝ)^32 ≤ (625262835483417/625000000000000 : ℝ)^135 := by
      have hnat : (2003550681253243623 : ℕ)^32*625000000000000^135 ≤ 625262835483417^135*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2003550681253243623 2000000000000000000 625262835483417 625000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625262835483417/625000000000000 : ℝ)) (X := (2003550681253243623/2000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1051697633669/945350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1050986233667/945350000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (18907/100000 : ℝ)) (alpha := (1051697633669/945350000000000 : ℝ)) (beta := (1050986233667/945350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18907/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1051697633669/945350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1050986233667/945350000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (14917/100000 : ℝ) ^ (135/32 : ℝ) ≤ (6531287185915129/20000000000000000000 : ℝ) := by
    have hpowers : (14917/100000 : ℝ)^135 ≤ (6531287185915129/20000000000000000000 : ℝ)^32 := by
      have hnat : (14917 : ℕ)^135*20000000000000000000^32 ≤ 6531287185915129^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14917 100000 6531287185915129 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14917/100000 : ℝ)) (X := (6531287185915129/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20006531287185915129/20000000000000000000 : ℝ) ≤ (10000773982066449/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (20006531287185915129/20000000000000000000 : ℝ)^32 ≤ (10000773982066449/10000000000000000 : ℝ)^135 := by
      have hnat : (20006531287185915129 : ℕ)^32*10000000000000000^135 ≤ 10000773982066449^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006531287185915129 20000000000000000000 10000773982066449 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000773982066449/10000000000000000 : ℝ)) (X := (20006531287185915129/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10006531287185915129/10000000000000000000 : ℝ) ≤ (10001547771377183/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (10006531287185915129/10000000000000000000 : ℝ)^32 ≤ (10001547771377183/10000000000000000 : ℝ)^135 := by
      have hnat : (10006531287185915129 : ℕ)^32*10000000000000000^135 ≤ 10001547771377183^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006531287185915129 10000000000000000000 10001547771377183 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001547771377183/10000000000000000 : ℝ)) (X := (10006531287185915129/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(773982066449/1491700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(386894655367/745850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (14917/100000 : ℝ)) (alpha := (773982066449/1491700000000000 : ℝ)) (beta := (386894655367/745850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (14917/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(773982066449/1491700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(386894655367/745850000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5157/12500 : ℝ) ^ (135/32 : ℝ) ≤ (2386911301390501407/100000000000000000000 : ℝ) := by
    have hpowers : (5157/12500 : ℝ)^135 ≤ (2386911301390501407/100000000000000000000 : ℝ)^32 := by
      have hnat : (5157 : ℕ)^135*100000000000000000000^32 ≤ 2386911301390501407^32*12500^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5157 12500 2386911301390501407 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5157/12500 : ℝ)) (X := (2386911301390501407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (102386911301390501407/100000000000000000000 : ℝ) ≤ (402242822549839/400000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (102386911301390501407/100000000000000000000 : ℝ)^32 ≤ (402242822549839/400000000000000 : ℝ)^135 := by
      have hnat : (102386911301390501407 : ℕ)^32*400000000000000^135 ≤ 402242822549839^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102386911301390501407 100000000000000000000 402242822549839 400000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402242822549839/400000000000000 : ℝ)) (X := (102386911301390501407/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (52386911301390501407/50000000000000000000 : ℝ) ≤ (40444610047331/40000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (52386911301390501407/50000000000000000000 : ℝ)^32 ≤ (40444610047331/40000000000000 : ℝ)^135 := by
      have hnat : (52386911301390501407 : ℕ)^32*40000000000000^135 ≤ 40444610047331^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52386911301390501407 50000000000000000000 40444610047331 40000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40444610047331/40000000000000 : ℝ)) (X := (52386911301390501407/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(747607516613/55008000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2203277923471/165024000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (5157/12500 : ℝ)) (alpha := (747607516613/55008000000000 : ℝ)) (beta := (2203277923471/165024000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5157/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(747607516613/55008000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2203277923471/165024000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-415430333/1250000000 : ℝ)*X 0 0+(-2760251701/5000000000 : ℝ)*X 0 1+(4016715483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5269542797/10000000000 : ℝ)*X 1 0+(683781909/2000000000 : ℝ)*X 1 1+(2099895349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4059281077/10000000000 : ℝ)*X 2 0+(-793121569/2000000000 : ℝ)*X 2 1+(-4906050381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((962300379/2000000000 : ℝ)*X 0 0+(-857309019/2000000000 : ℝ)*X 0 1+(766947027/2000000000 : ℝ)*X 0 2+(962300379/2000000000 : ℝ)*X 1 0+(-857309019/2000000000 : ℝ)*X 1 1+(766947027/2000000000 : ℝ)*X 1 2+(962300379/2000000000 : ℝ)*X 2 0+(-857309019/2000000000 : ℝ)*X 2 1+(766947027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307085_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-39543/6250 : ℝ) < ((-19431/12500 : ℝ)*P 0+(-19431/12500 : ℝ)*P 1+(-19431/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-39543/6250 : ℝ) < (-5890327926276521710472062131/945350000000000000000000000 : ℝ) := by norm_num
    linear_combination (1011/40000000000 : ℝ)*(base21) + (18091/500000000000 : ℝ)*(base22) + (19859/500000000000 : ℝ)*(base33) + (14191/1000000000000 : ℝ)*(base39) + (150230038507/500000000000 : ℝ)*(base40) + (104904440573/1000000000000 : ℝ)*(base49) + (167974537587/500000000000 : ℝ)*(base50) + (9239/1000000000000 : ℝ)*(base59) + (777239980141/500000000000 : ℝ)*(major_s1_0) + (19431/12500 : ℝ)*(major_s1_1) + (19431/12500 : ℝ)*(major_s1_2) + (415389568327/200000000000 : ℝ)*(sp_s1_0) + (2076947801917/1000000000000 : ℝ)*(sp_s1_1) + (103847387023/50000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (415389568327/200000000000 : ℝ)*(f.sum) + (69137667478977/712286750000000000000000000 : ℝ)*base63 + (61810232071/573000000000000000000000 : ℝ)*base65 + (11611408038897/29834000000000000000000000 : ℝ)*base66 + (504962093159/1910000000000000000000000 : ℝ)*base68 + (335979219540720541/541685550000000000000000000000 : ℝ)*base70 + (7531997470231/14771093750000000000000000 : ℝ)*base73 + (2055196072007/7458500000000000000000000 : ℝ)*base74 + (33368062555421/472675000000000000000000000 : ℝ)*base76 + (340352614687535707/1007270425000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p007_b039 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c307085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c307086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b039 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

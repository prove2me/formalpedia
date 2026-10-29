-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b038
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:01:52.257928+00:00
-- url     : https://prove2.me/submissions/7378be9b-1ce5-4312-8691-b2153ebe34fe

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309086_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309086_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309086_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309086_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c309086 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c309086_s0 p hpa hpb X hX
  have h1 := collision_c309086_s1 p hpa hpb X hX h0
  have h2 := collision_c309086_s2 p hpa hpb X hX h1
  exact collision_c309086_s3 p hpa hpb X hX h2

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
theorem collision_support_c309085_s0_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010280579/10000000000 : ℝ)*x 0 + (-7379138307/10000000000 : ℝ)*x 1 + (579334693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010280579/10000000000 : ℝ)^35 ≤ (12497242899507/100000000000000 : ℝ)^27 := by
    have hnat : (2010280579 : ℕ)^35*100000000000000^27 ≤ 12497242899507^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010280579 10000000000 12497242899507 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7379138307/10000000000 : ℝ)^35 ≤ (67436685006027/100000000000000 : ℝ)^27 := by
    have hnat : (7379138307 : ℕ)^35*100000000000000^27 ≤ 67436685006027^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7379138307 10000000000 67436685006027 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579334693/2000000000 : ℝ)^35 ≤ (20066072080017/100000000000000 : ℝ)^27 := by
    have hnat : (579334693 : ℕ)^35*100000000000000^27 ≤ 20066072080017^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579334693 2000000000 20066072080017 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010280579/10000000000 : ℝ), (-7379138307/10000000000 : ℝ), (579334693/2000000000 : ℝ)] ![(12497242899507/100000000000000 : ℝ), (67436685006027/100000000000000 : ℝ), (20066072080017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010280579/10000000000 : ℝ)|^35 ≤ (12497242899507/100000000000000 : ℝ)^27
        have hw : |(-2010280579/10000000000 : ℝ)|=(2010280579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7379138307/10000000000 : ℝ)|^35 ≤ (67436685006027/100000000000000 : ℝ)^27
        have hw : |(-7379138307/10000000000 : ℝ)|=(7379138307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(579334693/2000000000 : ℝ)|^35 ≤ (20066072080017/100000000000000 : ℝ)^27
        have hw : |(579334693/2000000000 : ℝ)|=(579334693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (559731239/1000000000 : ℝ)*x 0 + (348555527/1250000000 : ℝ)*x 1 + (270501117/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559731239/1000000000 : ℝ)^35 ≤ (47131017823389/100000000000000 : ℝ)^27 := by
    have hnat : (559731239 : ℕ)^35*100000000000000^27 ≤ 47131017823389^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559731239 1000000000 47131017823389 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348555527/1250000000 : ℝ)^35 ≤ (19099621630911/100000000000000 : ℝ)^27 := by
    have hnat : (348555527 : ℕ)^35*100000000000000^27 ≤ 19099621630911^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348555527 1250000000 19099621630911 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270501117/625000000 : ℝ)^35 ≤ (16884680264011/50000000000000 : ℝ)^27 := by
    have hnat : (270501117 : ℕ)^35*50000000000000^27 ≤ 16884680264011^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270501117 625000000 16884680264011 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(559731239/1000000000 : ℝ), (348555527/1250000000 : ℝ), (270501117/625000000 : ℝ)] ![(47131017823389/100000000000000 : ℝ), (19099621630911/100000000000000 : ℝ), (16884680264011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(559731239/1000000000 : ℝ)|^35 ≤ (47131017823389/100000000000000 : ℝ)^27
        have hw : |(559731239/1000000000 : ℝ)|=(559731239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(348555527/1250000000 : ℝ)|^35 ≤ (19099621630911/100000000000000 : ℝ)^27
        have hw : |(348555527/1250000000 : ℝ)|=(348555527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270501117/625000000 : ℝ)|^35 ≤ (16884680264011/50000000000000 : ℝ)^27
        have hw : |(270501117/625000000 : ℝ)|=(270501117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6752601923/10000000000 : ℝ)*x 0 + (-1117220023/5000000000 : ℝ)*x 1 + (3490954167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6752601923/10000000000 : ℝ)^35 ≤ (30054816810267/50000000000000 : ℝ)^27 := by
    have hnat : (6752601923 : ℕ)^35*50000000000000^27 ≤ 30054816810267^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6752601923 10000000000 30054816810267 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117220023/5000000000 : ℝ)^35 ≤ (14332759197289/100000000000000 : ℝ)^27 := by
    have hnat : (1117220023 : ℕ)^35*100000000000000^27 ≤ 14332759197289^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117220023 5000000000 14332759197289 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3490954167/10000000000 : ℝ)^35 ≤ (25557607165707/100000000000000 : ℝ)^27 := by
    have hnat : (3490954167 : ℕ)^35*100000000000000^27 ≤ 25557607165707^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3490954167 10000000000 25557607165707 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6752601923/10000000000 : ℝ), (-1117220023/5000000000 : ℝ), (3490954167/10000000000 : ℝ)] ![(30054816810267/50000000000000 : ℝ), (14332759197289/100000000000000 : ℝ), (25557607165707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6752601923/10000000000 : ℝ)|^35 ≤ (30054816810267/50000000000000 : ℝ)^27
        have hw : |(6752601923/10000000000 : ℝ)|=(6752601923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1117220023/5000000000 : ℝ)|^35 ≤ (14332759197289/100000000000000 : ℝ)^27
        have hw : |(-1117220023/5000000000 : ℝ)|=(1117220023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3490954167/10000000000 : ℝ)|^35 ≤ (25557607165707/100000000000000 : ℝ)^27
        have hw : |(3490954167/10000000000 : ℝ)|=(3490954167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1574164429/10000000000 : ℝ)*x 0 + (-1626437303/2000000000 : ℝ)*x 1 + (280441519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1574164429/10000000000 : ℝ)^35 ≤ (4551022847079/50000000000000 : ℝ)^27 := by
    have hnat : (1574164429 : ℕ)^35*50000000000000^27 ≤ 4551022847079^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574164429 10000000000 4551022847079 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1626437303/2000000000 : ℝ)^35 ≤ (19122387040969/25000000000000 : ℝ)^27 := by
    have hnat : (1626437303 : ℕ)^35*25000000000000^27 ≤ 19122387040969^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626437303 2000000000 19122387040969 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280441519/1250000000 : ℝ)^35 ≤ (3602101533427/25000000000000 : ℝ)^27 := by
    have hnat : (280441519 : ℕ)^35*25000000000000^27 ≤ 3602101533427^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280441519 1250000000 3602101533427 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1574164429/10000000000 : ℝ), (-1626437303/2000000000 : ℝ), (280441519/1250000000 : ℝ)] ![(4551022847079/50000000000000 : ℝ), (19122387040969/25000000000000 : ℝ), (3602101533427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1574164429/10000000000 : ℝ)|^35 ≤ (4551022847079/50000000000000 : ℝ)^27
        have hw : |(-1574164429/10000000000 : ℝ)|=(1574164429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1626437303/2000000000 : ℝ)|^35 ≤ (19122387040969/25000000000000 : ℝ)^27
        have hw : |(-1626437303/2000000000 : ℝ)|=(1626437303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280441519/1250000000 : ℝ)|^35 ≤ (3602101533427/25000000000000 : ℝ)^27
        have hw : |(280441519/1250000000 : ℝ)|=(280441519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5658558079/10000000000 : ℝ)*x 0 + (1302815297/5000000000 : ℝ)*x 1 + (2210213903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5658558079/10000000000 : ℝ)^35 ≤ (47800607452303/100000000000000 : ℝ)^27 := by
    have hnat : (5658558079 : ℕ)^35*100000000000000^27 ≤ 47800607452303^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658558079 10000000000 47800607452303 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302815297/5000000000 : ℝ)^35 ≤ (4373105882961/25000000000000 : ℝ)^27 := by
    have hnat : (1302815297 : ℕ)^35*25000000000000^27 ≤ 4373105882961^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302815297 5000000000 4373105882961 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210213903/5000000000 : ℝ)^35 ≤ (4338371125329/12500000000000 : ℝ)^27 := by
    have hnat : (2210213903 : ℕ)^35*12500000000000^27 ≤ 4338371125329^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210213903 5000000000 4338371125329 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5658558079/10000000000 : ℝ), (1302815297/5000000000 : ℝ), (2210213903/5000000000 : ℝ)] ![(47800607452303/100000000000000 : ℝ), (4373105882961/25000000000000 : ℝ), (4338371125329/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5658558079/10000000000 : ℝ)|^35 ≤ (47800607452303/100000000000000 : ℝ)^27
        have hw : |(5658558079/10000000000 : ℝ)|=(5658558079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302815297/5000000000 : ℝ)|^35 ≤ (4373105882961/25000000000000 : ℝ)^27
        have hw : |(1302815297/5000000000 : ℝ)|=(1302815297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210213903/5000000000 : ℝ)|^35 ≤ (4338371125329/12500000000000 : ℝ)^27
        have hw : |(2210213903/5000000000 : ℝ)|=(2210213903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1033118761/2500000000 : ℝ)*x 0 + (-1323213287/5000000000 : ℝ)*x 1 + (-2944845043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033118761/2500000000 : ℝ)^35 ≤ (15902476384271/50000000000000 : ℝ)^27 := by
    have hnat : (1033118761 : ℕ)^35*50000000000000^27 ≤ 15902476384271^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033118761 2500000000 15902476384271 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1323213287/5000000000 : ℝ)^35 ≤ (8924134450019/50000000000000 : ℝ)^27 := by
    have hnat : (1323213287 : ℕ)^35*50000000000000^27 ≤ 8924134450019^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323213287 5000000000 8924134450019 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2944845043/5000000000 : ℝ)^35 ≤ (50346778309117/100000000000000 : ℝ)^27 := by
    have hnat : (2944845043 : ℕ)^35*100000000000000^27 ≤ 50346778309117^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2944845043 5000000000 50346778309117 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033118761/2500000000 : ℝ), (-1323213287/5000000000 : ℝ), (-2944845043/5000000000 : ℝ)] ![(15902476384271/50000000000000 : ℝ), (8924134450019/50000000000000 : ℝ), (50346778309117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033118761/2500000000 : ℝ)|^35 ≤ (15902476384271/50000000000000 : ℝ)^27
        have hw : |(1033118761/2500000000 : ℝ)|=(1033118761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1323213287/5000000000 : ℝ)|^35 ≤ (8924134450019/50000000000000 : ℝ)^27
        have hw : |(-1323213287/5000000000 : ℝ)|=(1323213287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2944845043/5000000000 : ℝ)|^35 ≤ (50346778309117/100000000000000 : ℝ)^27
        have hw : |(-2944845043/5000000000 : ℝ)|=(2944845043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1882932281/10000000000 : ℝ)*x 0 + (-3729143959/5000000000 : ℝ)*x 1 + (1452640793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1882932281/10000000000 : ℝ)^35 ≤ (11480767149563/100000000000000 : ℝ)^27 := by
    have hnat : (1882932281 : ℕ)^35*100000000000000^27 ≤ 11480767149563^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882932281 10000000000 11480767149563 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3729143959/5000000000 : ℝ)^35 ≤ (68375827459539/100000000000000 : ℝ)^27 := by
    have hnat : (3729143959 : ℕ)^35*100000000000000^27 ≤ 68375827459539^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729143959 5000000000 68375827459539 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1452640793/5000000000 : ℝ)^35 ≤ (10071702685799/50000000000000 : ℝ)^27 := by
    have hnat : (1452640793 : ℕ)^35*50000000000000^27 ≤ 10071702685799^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452640793 5000000000 10071702685799 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1882932281/10000000000 : ℝ), (-3729143959/5000000000 : ℝ), (1452640793/5000000000 : ℝ)] ![(11480767149563/100000000000000 : ℝ), (68375827459539/100000000000000 : ℝ), (10071702685799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1882932281/10000000000 : ℝ)|^35 ≤ (11480767149563/100000000000000 : ℝ)^27
        have hw : |(-1882932281/10000000000 : ℝ)|=(1882932281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3729143959/5000000000 : ℝ)|^35 ≤ (68375827459539/100000000000000 : ℝ)^27
        have hw : |(-3729143959/5000000000 : ℝ)|=(3729143959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1452640793/5000000000 : ℝ)|^35 ≤ (10071702685799/50000000000000 : ℝ)^27
        have hw : |(1452640793/5000000000 : ℝ)|=(1452640793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2350031477/5000000000 : ℝ)*x 0 + (1459603831/5000000000 : ℝ)*x 1 + (3209623/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2350031477/5000000000 : ℝ)^35 ≤ (1503173807669/4000000000000 : ℝ)^27 := by
    have hnat : (2350031477 : ℕ)^35*4000000000000^27 ≤ 1503173807669^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350031477 5000000000 1503173807669 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1459603831/5000000000 : ℝ)^35 ≤ (5067164413739/25000000000000 : ℝ)^27 := by
    have hnat : (1459603831 : ℕ)^35*25000000000000^27 ≤ 5067164413739^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459603831 5000000000 5067164413739 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3209623/6250000 : ℝ)^35 ≤ (42151997140943/100000000000000 : ℝ)^27 := by
    have hnat : (3209623 : ℕ)^35*100000000000000^27 ≤ 42151997140943^27*6250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3209623 6250000 42151997140943 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2350031477/5000000000 : ℝ), (1459603831/5000000000 : ℝ), (3209623/6250000 : ℝ)] ![(1503173807669/4000000000000 : ℝ), (5067164413739/25000000000000 : ℝ), (42151997140943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2350031477/5000000000 : ℝ)|^35 ≤ (1503173807669/4000000000000 : ℝ)^27
        have hw : |(2350031477/5000000000 : ℝ)|=(2350031477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1459603831/5000000000 : ℝ)|^35 ≤ (5067164413739/25000000000000 : ℝ)^27
        have hw : |(1459603831/5000000000 : ℝ)|=(1459603831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3209623/6250000 : ℝ)|^35 ≤ (42151997140943/100000000000000 : ℝ)^27
        have hw : |(3209623/6250000 : ℝ)|=(3209623/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2067299999/5000000000 : ℝ)*x 0 + (-2924807151/10000000000 : ℝ)*x 1 + (-2831752049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067299999/5000000000 : ℝ)^35 ≤ (3978269312977/12500000000000 : ℝ)^27 := by
    have hnat : (2067299999 : ℕ)^35*12500000000000^27 ≤ 3978269312977^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067299999 5000000000 3978269312977 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2924807151/10000000000 : ℝ)^35 ≤ (10159534948571/50000000000000 : ℝ)^27 := by
    have hnat : (2924807151 : ℕ)^35*50000000000000^27 ≤ 10159534948571^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2924807151 10000000000 10159534948571 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831752049/5000000000 : ℝ)^35 ≤ (23927387796033/50000000000000 : ℝ)^27 := by
    have hnat : (2831752049 : ℕ)^35*50000000000000^27 ≤ 23927387796033^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831752049 5000000000 23927387796033 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067299999/5000000000 : ℝ), (-2924807151/10000000000 : ℝ), (-2831752049/5000000000 : ℝ)] ![(3978269312977/12500000000000 : ℝ), (10159534948571/50000000000000 : ℝ), (23927387796033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067299999/5000000000 : ℝ)|^35 ≤ (3978269312977/12500000000000 : ℝ)^27
        have hw : |(2067299999/5000000000 : ℝ)|=(2067299999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2924807151/10000000000 : ℝ)|^35 ≤ (10159534948571/50000000000000 : ℝ)^27
        have hw : |(-2924807151/10000000000 : ℝ)|=(2924807151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2831752049/5000000000 : ℝ)|^35 ≤ (23927387796033/50000000000000 : ℝ)^27
        have hw : |(-2831752049/5000000000 : ℝ)|=(2831752049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4216047469/5000000000 : ℝ)*x 0 + (-723867243/5000000000 : ℝ)*x 1 + (1906584099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216047469/5000000000 : ℝ)^35 ≤ (80166042935913/100000000000000 : ℝ)^27 := by
    have hnat : (4216047469 : ℕ)^35*100000000000000^27 ≤ 80166042935913^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216047469 5000000000 80166042935913 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (723867243/5000000000 : ℝ)^35 ≤ (8165901841681/100000000000000 : ℝ)^27 := by
    have hnat : (723867243 : ℕ)^35*100000000000000^27 ≤ 8165901841681^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723867243 5000000000 8165901841681 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906584099/10000000000 : ℝ)^35 ≤ (11668055207073/100000000000000 : ℝ)^27 := by
    have hnat : (1906584099 : ℕ)^35*100000000000000^27 ≤ 11668055207073^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906584099 10000000000 11668055207073 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216047469/5000000000 : ℝ), (-723867243/5000000000 : ℝ), (1906584099/10000000000 : ℝ)] ![(80166042935913/100000000000000 : ℝ), (8165901841681/100000000000000 : ℝ), (11668055207073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216047469/5000000000 : ℝ)|^35 ≤ (80166042935913/100000000000000 : ℝ)^27
        have hw : |(4216047469/5000000000 : ℝ)|=(4216047469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-723867243/5000000000 : ℝ)|^35 ≤ (8165901841681/100000000000000 : ℝ)^27
        have hw : |(-723867243/5000000000 : ℝ)|=(723867243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1906584099/10000000000 : ℝ)|^35 ≤ (11668055207073/100000000000000 : ℝ)^27
        have hw : |(1906584099/10000000000 : ℝ)|=(1906584099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1302834877/10000000000 : ℝ)*x 0 + (-8134638783/10000000000 : ℝ)*x 1 + (123714161/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1302834877/10000000000 : ℝ)^35 ≤ (7122531465049/100000000000000 : ℝ)^27 := by
    have hnat : (1302834877 : ℕ)^35*100000000000000^27 ≤ 7122531465049^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302834877 10000000000 7122531465049 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8134638783/10000000000 : ℝ)^35 ≤ (76519449209513/100000000000000 : ℝ)^27 := by
    have hnat : (8134638783 : ℕ)^35*100000000000000^27 ≤ 76519449209513^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8134638783 10000000000 76519449209513 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123714161/500000000 : ℝ)^35 ≤ (16358019308679/100000000000000 : ℝ)^27 := by
    have hnat : (123714161 : ℕ)^35*100000000000000^27 ≤ 16358019308679^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123714161 500000000 16358019308679 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1302834877/10000000000 : ℝ), (-8134638783/10000000000 : ℝ), (123714161/500000000 : ℝ)] ![(7122531465049/100000000000000 : ℝ), (76519449209513/100000000000000 : ℝ), (16358019308679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1302834877/10000000000 : ℝ)|^35 ≤ (7122531465049/100000000000000 : ℝ)^27
        have hw : |(-1302834877/10000000000 : ℝ)|=(1302834877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8134638783/10000000000 : ℝ)|^35 ≤ (76519449209513/100000000000000 : ℝ)^27
        have hw : |(-8134638783/10000000000 : ℝ)|=(8134638783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(123714161/500000000 : ℝ)|^35 ≤ (16358019308679/100000000000000 : ℝ)^27
        have hw : |(123714161/500000000 : ℝ)|=(123714161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3174110047/5000000000 : ℝ)*x 0 + (498668579/2000000000 : ℝ)*x 1 + (93622261/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3174110047/5000000000 : ℝ)^35 ≤ (55485370026831/100000000000000 : ℝ)^27 := by
    have hnat : (3174110047 : ℕ)^35*100000000000000^27 ≤ 55485370026831^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174110047 5000000000 55485370026831 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498668579/2000000000 : ℝ)^35 ≤ (16521548587333/100000000000000 : ℝ)^27 := by
    have hnat : (498668579 : ℕ)^35*100000000000000^27 ≤ 16521548587333^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498668579 2000000000 16521548587333 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93622261/250000000 : ℝ)^35 ≤ (5598616275311/20000000000000 : ℝ)^27 := by
    have hnat : (93622261 : ℕ)^35*20000000000000^27 ≤ 5598616275311^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93622261 250000000 5598616275311 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3174110047/5000000000 : ℝ), (498668579/2000000000 : ℝ), (93622261/250000000 : ℝ)] ![(55485370026831/100000000000000 : ℝ), (16521548587333/100000000000000 : ℝ), (5598616275311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3174110047/5000000000 : ℝ)|^35 ≤ (55485370026831/100000000000000 : ℝ)^27
        have hw : |(3174110047/5000000000 : ℝ)|=(3174110047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(498668579/2000000000 : ℝ)|^35 ≤ (16521548587333/100000000000000 : ℝ)^27
        have hw : |(498668579/2000000000 : ℝ)|=(498668579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(93622261/250000000 : ℝ)|^35 ≤ (5598616275311/20000000000000 : ℝ)^27
        have hw : |(93622261/250000000 : ℝ)|=(93622261/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (859632187/2500000000 : ℝ)*x 0 + (-33317169/100000000 : ℝ)*x 1 + (-5937940573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859632187/2500000000 : ℝ)^35 ≤ (25061184617943/100000000000000 : ℝ)^27 := by
    have hnat : (859632187 : ℕ)^35*100000000000000^27 ≤ 25061184617943^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859632187 2500000000 25061184617943 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33317169/100000000 : ℝ)^35 ≤ (1503545006453/6250000000000 : ℝ)^27 := by
    have hnat : (33317169 : ℕ)^35*6250000000000^27 ≤ 1503545006453^27*100000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33317169 100000000 1503545006453 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5937940573/10000000000 : ℝ)^35 ≤ (25441047627767/50000000000000 : ℝ)^27 := by
    have hnat : (5937940573 : ℕ)^35*50000000000000^27 ≤ 25441047627767^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5937940573 10000000000 25441047627767 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859632187/2500000000 : ℝ), (-33317169/100000000 : ℝ), (-5937940573/10000000000 : ℝ)] ![(25061184617943/100000000000000 : ℝ), (1503545006453/6250000000000 : ℝ), (25441047627767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859632187/2500000000 : ℝ)|^35 ≤ (25061184617943/100000000000000 : ℝ)^27
        have hw : |(859632187/2500000000 : ℝ)|=(859632187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33317169/100000000 : ℝ)|^35 ≤ (1503545006453/6250000000000 : ℝ)^27
        have hw : |(-33317169/100000000 : ℝ)|=(33317169/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5937940573/10000000000 : ℝ)|^35 ≤ (25441047627767/50000000000000 : ℝ)^27
        have hw : |(-5937940573/10000000000 : ℝ)|=(5937940573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s0_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (521300631/625000000 : ℝ)*x 0 + (-698362169/10000000000 : ℝ)*x 1 + (659748451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521300631/625000000 : ℝ)^35 ≤ (395214189623/500000000000 : ℝ)^27 := by
    have hnat : (521300631 : ℕ)^35*500000000000^27 ≤ 395214189623^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521300631 625000000 395214189623 500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698362169/10000000000 : ℝ)^35 ≤ (317384781967/10000000000000 : ℝ)^27 := by
    have hnat : (698362169 : ℕ)^35*10000000000000^27 ≤ 317384781967^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698362169 10000000000 317384781967 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659748451/2500000000 : ℝ)^35 ≤ (3556662846521/20000000000000 : ℝ)^27 := by
    have hnat : (659748451 : ℕ)^35*20000000000000^27 ≤ 3556662846521^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659748451 2500000000 3556662846521 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521300631/625000000 : ℝ), (-698362169/10000000000 : ℝ), (659748451/2500000000 : ℝ)] ![(395214189623/500000000000 : ℝ), (317384781967/10000000000000 : ℝ), (3556662846521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521300631/625000000 : ℝ)|^35 ≤ (395214189623/500000000000 : ℝ)^27
        have hw : |(521300631/625000000 : ℝ)|=(521300631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698362169/10000000000 : ℝ)|^35 ≤ (317384781967/10000000000000 : ℝ)^27
        have hw : |(-698362169/10000000000 : ℝ)|=(698362169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659748451/2500000000 : ℝ)|^35 ≤ (3556662846521/20000000000000 : ℝ)^27
        have hw : |(659748451/2500000000 : ℝ)|=(659748451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1642442281/5000000000 : ℝ)*x 0 + (-5498411133/10000000000 : ℝ)*x 1 + (3983470571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1642442281/5000000000 : ℝ)^35 ≤ (2361928855817/10000000000000 : ℝ)^27 := by
    have hnat : (1642442281 : ℕ)^35*10000000000000^27 ≤ 2361928855817^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642442281 5000000000 2361928855817 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498411133/10000000000 : ℝ)^35 ≤ (23027164425923/50000000000000 : ℝ)^27 := by
    have hnat : (5498411133 : ℕ)^35*50000000000000^27 ≤ 23027164425923^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498411133 10000000000 23027164425923 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983470571/10000000000 : ℝ)^35 ≤ (15163191290703/50000000000000 : ℝ)^27 := by
    have hnat : (3983470571 : ℕ)^35*50000000000000^27 ≤ 15163191290703^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983470571 10000000000 15163191290703 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1642442281/5000000000 : ℝ), (-5498411133/10000000000 : ℝ), (3983470571/10000000000 : ℝ)] ![(2361928855817/10000000000000 : ℝ), (23027164425923/50000000000000 : ℝ), (15163191290703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1642442281/5000000000 : ℝ)|^35 ≤ (2361928855817/10000000000000 : ℝ)^27
        have hw : |(-1642442281/5000000000 : ℝ)|=(1642442281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5498411133/10000000000 : ℝ)|^35 ≤ (23027164425923/50000000000000 : ℝ)^27
        have hw : |(-5498411133/10000000000 : ℝ)|=(5498411133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983470571/10000000000 : ℝ)|^35 ≤ (15163191290703/50000000000000 : ℝ)^27
        have hw : |(3983470571/10000000000 : ℝ)|=(3983470571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (656751439/1250000000 : ℝ)*x 0 + (33773463/100000000 : ℝ)*x 1 + (104042819/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656751439/1250000000 : ℝ)^35 ≤ (43418372920831/100000000000000 : ℝ)^27 := by
    have hnat : (656751439 : ℕ)^35*100000000000000^27 ≤ 43418372920831^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656751439 1250000000 43418372920831 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33773463/100000000 : ℝ)^35 ≤ (4896934374327/20000000000000 : ℝ)^27 := by
    have hnat : (33773463 : ℕ)^35*20000000000000^27 ≤ 4896934374327^27*100000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33773463 100000000 4896934374327 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104042819/250000000 : ℝ)^35 ≤ (16048477597429/50000000000000 : ℝ)^27 := by
    have hnat : (104042819 : ℕ)^35*50000000000000^27 ≤ 16048477597429^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104042819 250000000 16048477597429 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656751439/1250000000 : ℝ), (33773463/100000000 : ℝ), (104042819/250000000 : ℝ)] ![(43418372920831/100000000000000 : ℝ), (4896934374327/20000000000000 : ℝ), (16048477597429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656751439/1250000000 : ℝ)|^35 ≤ (43418372920831/100000000000000 : ℝ)^27
        have hw : |(656751439/1250000000 : ℝ)|=(656751439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33773463/100000000 : ℝ)|^35 ≤ (4896934374327/20000000000000 : ℝ)^27
        have hw : |(33773463/100000000 : ℝ)|=(33773463/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104042819/250000000 : ℝ)|^35 ≤ (16048477597429/50000000000000 : ℝ)^27
        have hw : |(104042819/250000000 : ℝ)|=(104042819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (125743783/312500000 : ℝ)*x 0 + (-122893229/312500000 : ℝ)*x 1 + (-2439765049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125743783/312500000 : ℝ)^35 ≤ (3840623833173/12500000000000 : ℝ)^27 := by
    have hnat : (125743783 : ℕ)^35*12500000000000^27 ≤ 3840623833173^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125743783 312500000 3840623833173 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122893229/312500000 : ℝ)^35 ≤ (1864071317507/6250000000000 : ℝ)^27 := by
    have hnat : (122893229 : ℕ)^35*6250000000000^27 ≤ 1864071317507^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122893229 312500000 1864071317507 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2439765049/5000000000 : ℝ)^35 ≤ (19724934121709/50000000000000 : ℝ)^27 := by
    have hnat : (2439765049 : ℕ)^35*50000000000000^27 ≤ 19724934121709^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439765049 5000000000 19724934121709 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(125743783/312500000 : ℝ), (-122893229/312500000 : ℝ), (-2439765049/5000000000 : ℝ)] ![(3840623833173/12500000000000 : ℝ), (1864071317507/6250000000000 : ℝ), (19724934121709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(125743783/312500000 : ℝ)|^35 ≤ (3840623833173/12500000000000 : ℝ)^27
        have hw : |(125743783/312500000 : ℝ)|=(125743783/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122893229/312500000 : ℝ)|^35 ≤ (1864071317507/6250000000000 : ℝ)^27
        have hw : |(-122893229/312500000 : ℝ)|=(122893229/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2439765049/5000000000 : ℝ)|^35 ≤ (19724934121709/50000000000000 : ℝ)^27
        have hw : |(-2439765049/5000000000 : ℝ)|=(2439765049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309085_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (957452981/2000000000 : ℝ)*x 0 + (-532263209/1250000000 : ℝ)*x 1 + (1896000931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957452981/2000000000 : ℝ)^35 ≤ (38485626366447/100000000000000 : ℝ)^27 := by
    have hnat : (957452981 : ℕ)^35*100000000000000^27 ≤ 38485626366447^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957452981 2000000000 38485626366447 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532263209/1250000000 : ℝ)^35 ≤ (8265985642561/25000000000000 : ℝ)^27 := by
    have hnat : (532263209 : ℕ)^35*25000000000000^27 ≤ 8265985642561^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532263209 1250000000 8265985642561 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896000931/5000000000 : ℝ)^35 ≤ (28450431043271/100000000000000 : ℝ)^27 := by
    have hnat : (1896000931 : ℕ)^35*100000000000000^27 ≤ 28450431043271^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896000931 5000000000 28450431043271 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(957452981/2000000000 : ℝ), (-532263209/1250000000 : ℝ), (1896000931/5000000000 : ℝ)] ![(38485626366447/100000000000000 : ℝ), (8265985642561/25000000000000 : ℝ), (28450431043271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(957452981/2000000000 : ℝ)|^35 ≤ (38485626366447/100000000000000 : ℝ)^27
        have hw : |(957452981/2000000000 : ℝ)|=(957452981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532263209/1250000000 : ℝ)|^35 ≤ (8265985642561/25000000000000 : ℝ)^27
        have hw : |(-532263209/1250000000 : ℝ)|=(532263209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1896000931/5000000000 : ℝ)|^35 ≤ (28450431043271/100000000000000 : ℝ)^27
        have hw : |(1896000931/5000000000 : ℝ)|=(1896000931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309085 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2010280579/10000000000 : ℝ)*X 0 0+(-7379138307/10000000000 : ℝ)*X 0 1+(579334693/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((559731239/1000000000 : ℝ)*X 1 0+(348555527/1250000000 : ℝ)*X 1 1+(270501117/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((6752601923/10000000000 : ℝ)*X 0 0+(-1117220023/5000000000 : ℝ)*X 0 1+(3490954167/10000000000 : ℝ)*X 0 2+(6752601923/10000000000 : ℝ)*X 1 0+(-1117220023/5000000000 : ℝ)*X 1 1+(3490954167/10000000000 : ℝ)*X 1 2+(6752601923/10000000000 : ℝ)*X 2 0+(-1117220023/5000000000 : ℝ)*X 2 1+(3490954167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1574164429/10000000000 : ℝ)*X 0 0+(-1626437303/2000000000 : ℝ)*X 0 1+(280441519/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5658558079/10000000000 : ℝ)*X 1 0+(1302815297/5000000000 : ℝ)*X 1 1+(2210213903/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1033118761/2500000000 : ℝ)*X 2 0+(-1323213287/5000000000 : ℝ)*X 2 1+(-2944845043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1882932281/10000000000 : ℝ)*X 0 0+(-3729143959/5000000000 : ℝ)*X 0 1+(1452640793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2350031477/5000000000 : ℝ)*X 1 0+(1459603831/5000000000 : ℝ)*X 1 1+(3209623/6250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2067299999/5000000000 : ℝ)*X 2 0+(-2924807151/10000000000 : ℝ)*X 2 1+(-2831752049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4216047469/5000000000 : ℝ)*X 0 0+(-723867243/5000000000 : ℝ)*X 0 1+(1906584099/10000000000 : ℝ)*X 0 2+(4216047469/5000000000 : ℝ)*X 1 0+(-723867243/5000000000 : ℝ)*X 1 1+(1906584099/10000000000 : ℝ)*X 1 2+(4216047469/5000000000 : ℝ)*X 2 0+(-723867243/5000000000 : ℝ)*X 2 1+(1906584099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1302834877/10000000000 : ℝ)*X 0 0+(-8134638783/10000000000 : ℝ)*X 0 1+(123714161/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3174110047/5000000000 : ℝ)*X 1 0+(498668579/2000000000 : ℝ)*X 1 1+(93622261/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((859632187/2500000000 : ℝ)*X 2 0+(-33317169/100000000 : ℝ)*X 2 1+(-5937940573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((521300631/625000000 : ℝ)*X 0 0+(-698362169/10000000000 : ℝ)*X 0 1+(659748451/2500000000 : ℝ)*X 0 2+(521300631/625000000 : ℝ)*X 1 0+(-698362169/10000000000 : ℝ)*X 1 1+(659748451/2500000000 : ℝ)*X 1 2+(521300631/625000000 : ℝ)*X 2 0+(-698362169/10000000000 : ℝ)*X 2 1+(659748451/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((18479/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18479/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27478913110637203573611/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1360126138509/500000000000 : ℝ)*(base3) + (250913612499/250000000000 : ℝ)*(base40) + (12658947157/250000000000 : ℝ)*(base49) + (560778405279/250000000000 : ℝ)*(base50) + (4331941047541/1000000000000 : ℝ)*(major_s0_0) + (4331941047541/1000000000000 : ℝ)*(major_s0_1) + (4331941047541/1000000000000 : ℝ)*(major_s0_2) + (204181427/1000000000000 : ℝ)*(sp_s0_1) + (410211/31250000000 : ℝ)*(sp_s0_6) + (371464890609/62500000000 : ℝ)*(sp_s0_7) + (8663609490069/1000000000000 : ℝ)*(sp_s0_8) + (742951628431/125000000000 : ℝ)*(sp_s0_9) + (51632969/1000000000000 : ℝ)*(sp_s0_15) + (21847213/125000000000 : ℝ)*(sp_s0_21) + (2720265403769/1000000000000 : ℝ)*(f.failure) + (742951628431/125000000000 : ℝ)*(f.sum) + (221749022711101/10000000000000000000000000000 : ℝ)*base62 + (1559493115007181/10000000000000000000000000000 : ℝ)*base64 + (231386028859141/5000000000000000000000000000 : ℝ)*base67 + (2335741943640859/5000000000000000000000000000 : ℝ)*base69 + (2218988812725463/10000000000000000000000000000 : ℝ)*base70 + (9577703357007181/10000000000000000000000000000 : ℝ)*base73 + (1678348291007181/10000000000000000000000000000 : ℝ)*base75 + (3121064932859141/5000000000000000000000000000 : ℝ)*base76 + (3524648652725463/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (98057/100000000000000000 : ℝ)*base86 + (98057/100000000000000000 : ℝ)*base88 + (98057/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-14561/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-14561/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8564469304457507423181/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (505458754589/500000000000 : ℝ)*(base40) + (257291071/3906250000 : ℝ)*(base50) + (5609119361/40000000000 : ℝ)*(base59) + (867147370347/250000000000 : ℝ)*(major_s0_0) + (867147370347/250000000000 : ℝ)*(major_s0_1) + (867147370347/250000000000 : ℝ)*(major_s0_2) + (86134853/250000000000 : ℝ)*(sp_s0_0) + (1971167/50000000000 : ℝ)*(sp_s0_7) + (4963117/200000000000 : ℝ)*(sp_s0_8) + (478101253/1000000000000 : ℝ)*(sp_s0_9) + (4758671232951/1000000000000 : ℝ)*(sp_s0_14) + (2379515190059/500000000000 : ℝ)*(sp_s0_15) + (4758577094449/1000000000000 : ℝ)*(sp_s0_16) + (43562383987/20000000000 : ℝ)*(sp_s0_20) + (43562383987/20000000000 : ℝ)*(f.failure) + (4759055195703/1000000000000 : ℝ)*(f.sum) + (1087404322394867/2500000000000000000000000000 : ℝ)*base62 + (981775323629773/2500000000000000000000000000 : ℝ)*base65 + (633931394992453/1250000000000000000000000000 : ℝ)*base66 + (975931890382547/1250000000000000000000000000 : ℝ)*base68 + (152306737385321/2500000000000000000000000000 : ℝ)*base70 + (1592482538129773/2500000000000000000000000000 : ℝ)*base72 + (1072136781629773/2500000000000000000000000000 : ℝ)*base74 + (252566385617453/1250000000000000000000000000 : ℝ)*base77 + (1746841611614679/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (1789/2000000000000000 : ℝ)*base87 + (1789/2000000000000000 : ℝ)*base89 + (1789/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40301/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40301/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4565546285156172329367/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1298572726753/1000000000000 : ℝ)*(base3) + (1944829388767/1000000000000 : ℝ)*(base40) + (884871829801/500000000000 : ℝ)*(base50) + (161693390193/1000000000000 : ℝ)*(base59) + (1427794793909/250000000000 : ℝ)*(major_s0_0) + (1427794793909/250000000000 : ℝ)*(major_s0_1) + (1427794793909/250000000000 : ℝ)*(major_s0_2) + (5146013/250000000000 : ℝ)*(sp_s0_1) + (35494347/125000000000 : ℝ)*(sp_s0_7) + (67277751/1000000000000 : ℝ)*(sp_s0_20) + (783570421003/100000000000 : ℝ)*(sp_s0_21) + (2283635076877/250000000000 : ℝ)*(sp_s0_22) + (3917994082403/500000000000 : ℝ)*(sp_s0_23) + (2287725312039/1000000000000 : ℝ)*(sp_s0_27) + (3586365316543/1000000000000 : ℝ)*(f.failure) + (3917994082403/500000000000 : ℝ)*(f.sum) + (82264323412349/2500000000000000000000000000 : ℝ)*base62 + (504581856157731/2500000000000000000000000000 : ℝ)*base65 + (132311331122691/1250000000000000000000000000 : ℝ)*base66 + (270773977752309/1250000000000000000000000000 : ℝ)*base68 + (1015159448653113/2500000000000000000000000000 : ℝ)*base71 + (1197225821657731/2500000000000000000000000000 : ℝ)*base72 + (48468053092269/2500000000000000000000000000 : ℝ)*base75 + (224955421122691/1250000000000000000000000000 : ℝ)*base77 + (1192594244153113/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (76879/100000000000000000 : ℝ)*base86 + (76879/100000000000000000 : ℝ)*base88 + (76879/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (18479/100000 : ℝ) ^ (69/16 : ℝ) ≤ (6879405072904079/10000000000000000000 : ℝ) := by
    have hpowers : (18479/100000 : ℝ)^69 ≤ (6879405072904079/10000000000000000000 : ℝ)^16 := by
      have hnat : (18479 : ℕ)^69*10000000000000000000^16 ≤ 6879405072904079^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18479 100000 6879405072904079 10000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18479/100000 : ℝ)) (X := (6879405072904079/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10006879405072904079/10000000000000000000 : ℝ) ≤ (10001594803062847/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10006879405072904079/10000000000000000000 : ℝ)^16 ≤ (10001594803062847/10000000000000000 : ℝ)^69 := by
      have hnat : (10006879405072904079 : ℕ)^16*10000000000000000^69 ≤ 10001594803062847^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006879405072904079 10000000000000000000 10001594803062847 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001594803062847/10000000000000000 : ℝ)) (X := (10006879405072904079/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5006879405072904079/5000000000000000000 : ℝ) ≤ (10003188764204499/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (5006879405072904079/5000000000000000000 : ℝ)^16 ≤ (10003188764204499/10000000000000000 : ℝ)^69 := by
      have hnat : (5006879405072904079 : ℕ)^16*10000000000000000^69 ≤ 10003188764204499^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5006879405072904079 5000000000000000000 10003188764204499 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003188764204499/10000000000000000 : ℝ)) (X := (5006879405072904079/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1594803062847/1847900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(398490285413/461975000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (18479/100000 : ℝ)) (alpha := (1594803062847/1847900000000000 : ℝ)) (beta := (398490285413/461975000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18479/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1594803062847/1847900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(398490285413/461975000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (14561/100000 : ℝ) ^ (69/16 : ℝ) ≤ (6154631662557597/25000000000000000000 : ℝ) := by
    have hpowers : (14561/100000 : ℝ)^69 ≤ (6154631662557597/25000000000000000000 : ℝ)^16 := by
      have hnat : (14561 : ℕ)^69*25000000000000000000^16 ≤ 6154631662557597^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14561 100000 6154631662557597 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14561/100000 : ℝ)) (X := (6154631662557597/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25006154631662557597/25000000000000000000 : ℝ) ≤ (1000057081041903/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25006154631662557597/25000000000000000000 : ℝ)^16 ≤ (1000057081041903/1000000000000000 : ℝ)^69 := by
      have hnat : (25006154631662557597 : ℕ)^16*1000000000000000^69 ≤ 1000057081041903^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006154631662557597 25000000000000000000 1000057081041903 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000057081041903/1000000000000000 : ℝ)) (X := (25006154631662557597/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12506154631662557597/12500000000000000000 : ℝ) ≤ (10001141512935243/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (12506154631662557597/12500000000000000000 : ℝ)^16 ≤ (10001141512935243/10000000000000000 : ℝ)^69 := by
      have hnat : (12506154631662557597 : ℕ)^16*10000000000000000^69 ≤ 10001141512935243^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506154631662557597 12500000000000000000 10001141512935243 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001141512935243/10000000000000000 : ℝ)) (X := (12506154631662557597/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(57081041903/145610000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(570702516213/1456100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (14561/100000 : ℝ)) (alpha := (57081041903/145610000000000 : ℝ)) (beta := (570702516213/1456100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (14561/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(57081041903/145610000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(570702516213/1456100000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (40301/100000 : ℝ) ^ (69/16 : ℝ) ≤ (496437401129271613/25000000000000000000 : ℝ) := by
    have hpowers : (40301/100000 : ℝ)^69 ≤ (496437401129271613/25000000000000000000 : ℝ)^16 := by
      have hnat : (40301 : ℕ)^69*25000000000000000000^16 ≤ 496437401129271613^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40301 100000 496437401129271613 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40301/100000 : ℝ)) (X := (496437401129271613/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25496437401129271613/25000000000000000000 : ℝ) ≤ (2511424813126491/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25496437401129271613/25000000000000000000 : ℝ)^16 ≤ (2511424813126491/2500000000000000 : ℝ)^69 := by
      have hnat : (25496437401129271613 : ℕ)^16*2500000000000000^69 ≤ 2511424813126491^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25496437401129271613 25000000000000000000 2511424813126491 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511424813126491/2500000000000000 : ℝ)) (X := (25496437401129271613/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12996437401129271613/12500000000000000000 : ℝ) ≤ (10090720059472979/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (12996437401129271613/12500000000000000000 : ℝ)^16 ≤ (10090720059472979/10000000000000000 : ℝ)^69 := by
      have hnat : (12996437401129271613 : ℕ)^16*10000000000000000^69 ≤ 10090720059472979^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12996437401129271613 12500000000000000000 10090720059472979 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10090720059472979/10000000000000000 : ℝ)) (X := (12996437401129271613/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(11424813126491/1007525000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(9004161393403/806020000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (40301/100000 : ℝ)) (alpha := (11424813126491/1007525000000000 : ℝ)) (beta := (9004161393403/806020000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (40301/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(11424813126491/1007525000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(9004161393403/806020000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1642442281/5000000000 : ℝ)*X 0 0+(-5498411133/10000000000 : ℝ)*X 0 1+(3983470571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((656751439/1250000000 : ℝ)*X 1 0+(33773463/100000000 : ℝ)*X 1 1+(104042819/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((125743783/312500000 : ℝ)*X 2 0+(-122893229/312500000 : ℝ)*X 2 1+(-2439765049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((957452981/2000000000 : ℝ)*X 0 0+(-532263209/1250000000 : ℝ)*X 0 1+(1896000931/5000000000 : ℝ)*X 0 2+(957452981/2000000000 : ℝ)*X 1 0+(-532263209/1250000000 : ℝ)*X 1 1+(1896000931/5000000000 : ℝ)*X 1 2+(957452981/2000000000 : ℝ)*X 2 0+(-532263209/1250000000 : ℝ)*X 2 1+(1896000931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309085_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-327741/50000 : ℝ) < ((-159247/100000 : ℝ)*P 0+(-159247/100000 : ℝ)*P 1+(-159247/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-327741/50000 : ℝ) < (-875983570439497653431290398522300543/135548745605237500000000000000000000 : ℝ) := by norm_num
    linear_combination (101259/500000000000 : ℝ)*(base1) + (66127/1000000000000 : ℝ)*(base3) + (116799/1000000000000 : ℝ)*(base22) + (322777/1000000000000 : ℝ)*(base24) + (159070716417/500000000000 : ℝ)*(base40) + (19937/1000000000000 : ℝ)*(base43) + (106965456119/1000000000000 : ℝ)*(base49) + (354539815513/1000000000000 : ℝ)*(base50) + (159247/100000 : ℝ)*(major_s1_0) + (1592469980063/1000000000000 : ℝ)*(major_s1_1) + (159247/100000 : ℝ)*(major_s1_2) + (8616665449/4000000000 : ℝ)*(sp_s1_0) + (538541561449/250000000000 : ℝ)*(sp_s1_1) + (2154165720157/1000000000000 : ℝ)*(sp_s1_2) + (199999946271/200000000000 : ℝ)*(sp_s1_6) + (2154166179669/1000000000000 : ℝ)*(f.sum) + (13607109540682435631/58682286100000000000000000000000 : ℝ)*base62 + (1753619748219/40301000000000000000000000 : ℝ)*base64 + (3625797893249/145610000000000000000000000 : ℝ)*base66 + (45374329772073/403010000000000000000000000 : ℝ)*base69 + (87603452567538349/186180544750000000000000000000 : ℝ)*base70 + (5601481069437/18479000000000000000000000 : ℝ)*base73 + (601592431514451/1456100000000000000000000000 : ℝ)*base74 + (2343583151647/23098750000000000000000000 : ℝ)*base76 + (2119951607975011513/2690727190000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p009_b038 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c309085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c309086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b038 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

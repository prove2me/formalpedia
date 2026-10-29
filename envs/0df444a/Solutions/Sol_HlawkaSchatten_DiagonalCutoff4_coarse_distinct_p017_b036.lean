-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b036
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:14:21.718282+00:00
-- url     : https://prove2.me/submissions/11962b33-85d1-428a-8899-93f36e8d38ca

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317083_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317083_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317083_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c317083 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c317083_s0 p hpa hpb X hX
  have h1 := collision_c317083_s1 p hpa hpb X hX h0
  exact collision_c317083_s2 p hpa hpb X hX h1

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
theorem collision_support_c317082_s0_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2071801021/5000000000 : ℝ)*x 0 + (-2795552013/10000000000 : ℝ)*x 1 + (34220873/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071801021/5000000000 : ℝ)^39 ≤ (2063083968807/6250000000000 : ℝ)^31 := by
    have hnat : (2071801021 : ℕ)^39*6250000000000^31 ≤ 2063083968807^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071801021 5000000000 2063083968807 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2795552013/10000000000 : ℝ)^39 ≤ (5029913410239/25000000000000 : ℝ)^31 := by
    have hnat : (2795552013 : ℕ)^39*25000000000000^31 ≤ 5029913410239^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795552013 10000000000 5029913410239 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34220873/62500000 : ℝ)^39 ≤ (11717750713559/25000000000000 : ℝ)^31 := by
    have hnat : (34220873 : ℕ)^39*25000000000000^31 ≤ 11717750713559^31*62500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34220873 62500000 11717750713559 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2071801021/5000000000 : ℝ), (-2795552013/10000000000 : ℝ), (34220873/62500000 : ℝ)] ![(2063083968807/6250000000000 : ℝ), (5029913410239/25000000000000 : ℝ), (11717750713559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2071801021/5000000000 : ℝ)|^39 ≤ (2063083968807/6250000000000 : ℝ)^31
        have hw : |(2071801021/5000000000 : ℝ)|=(2071801021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2795552013/10000000000 : ℝ)|^39 ≤ (5029913410239/25000000000000 : ℝ)^31
        have hw : |(-2795552013/10000000000 : ℝ)|=(2795552013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34220873/62500000 : ℝ)|^39 ≤ (11717750713559/25000000000000 : ℝ)^31
        have hw : |(34220873/62500000 : ℝ)|=(34220873/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2961116707/10000000000 : ℝ)*x 0 + (286391763/2000000000 : ℝ)*x 1 + (7505531339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2961116707/10000000000 : ℝ)^39 ≤ (1081501073113/5000000000000 : ℝ)^31 := by
    have hnat : (2961116707 : ℕ)^39*5000000000000^31 ≤ 1081501073113^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961116707 10000000000 1081501073113 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286391763/2000000000 : ℝ)^39 ≤ (4335868992061/50000000000000 : ℝ)^31 := by
    have hnat : (286391763 : ℕ)^39*50000000000000^31 ≤ 4335868992061^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286391763 2000000000 4335868992061 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7505531339/10000000000 : ℝ)^39 ≤ (6969824054857/10000000000000 : ℝ)^31 := by
    have hnat : (7505531339 : ℕ)^39*10000000000000^31 ≤ 6969824054857^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7505531339 10000000000 6969824054857 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2961116707/10000000000 : ℝ), (286391763/2000000000 : ℝ), (7505531339/10000000000 : ℝ)] ![(1081501073113/5000000000000 : ℝ), (4335868992061/50000000000000 : ℝ), (6969824054857/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2961116707/10000000000 : ℝ)|^39 ≤ (1081501073113/5000000000000 : ℝ)^31
        have hw : |(-2961116707/10000000000 : ℝ)|=(2961116707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(286391763/2000000000 : ℝ)|^39 ≤ (4335868992061/50000000000000 : ℝ)^31
        have hw : |(286391763/2000000000 : ℝ)|=(286391763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7505531339/10000000000 : ℝ)|^39 ≤ (6969824054857/10000000000000 : ℝ)^31
        have hw : |(7505531339/10000000000 : ℝ)|=(7505531339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4180666031/10000000000 : ℝ)*x 0 + (-297778221/5000000000 : ℝ)*x 1 + (3495571471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180666031/10000000000 : ℝ)^39 ≤ (16690616442191/50000000000000 : ℝ)^31 := by
    have hnat : (4180666031 : ℕ)^39*50000000000000^31 ≤ 16690616442191^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180666031 10000000000 16690616442191 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297778221/5000000000 : ℝ)^39 ≤ (57518029629/2000000000000 : ℝ)^31 := by
    have hnat : (297778221 : ℕ)^39*2000000000000^31 ≤ 57518029629^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297778221 5000000000 57518029629 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3495571471/5000000000 : ℝ)^39 ≤ (2549714624541/4000000000000 : ℝ)^31 := by
    have hnat : (3495571471 : ℕ)^39*4000000000000^31 ≤ 2549714624541^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3495571471 5000000000 2549714624541 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180666031/10000000000 : ℝ), (-297778221/5000000000 : ℝ), (3495571471/5000000000 : ℝ)] ![(16690616442191/50000000000000 : ℝ), (57518029629/2000000000000 : ℝ), (2549714624541/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180666031/10000000000 : ℝ)|^39 ≤ (16690616442191/50000000000000 : ℝ)^31
        have hw : |(4180666031/10000000000 : ℝ)|=(4180666031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297778221/5000000000 : ℝ)|^39 ≤ (57518029629/2000000000000 : ℝ)^31
        have hw : |(-297778221/5000000000 : ℝ)|=(297778221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3495571471/5000000000 : ℝ)|^39 ≤ (2549714624541/4000000000000 : ℝ)^31
        have hw : |(3495571471/5000000000 : ℝ)|=(3495571471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3760547553/10000000000 : ℝ)*x 0 + (7533152517/10000000000 : ℝ)*x 1 + (-103578891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3760547553/10000000000 : ℝ)^39 ≤ (7304297781519/25000000000000 : ℝ)^31 := by
    have hnat : (3760547553 : ℕ)^39*25000000000000^31 ≤ 7304297781519^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760547553 10000000000 7304297781519 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7533152517/10000000000 : ℝ)^39 ≤ (14004216724213/20000000000000 : ℝ)^31 := by
    have hnat : (7533152517 : ℕ)^39*20000000000000^31 ≤ 14004216724213^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7533152517 10000000000 14004216724213 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103578891/5000000000 : ℝ)^39 ≤ (380862623119/50000000000000 : ℝ)^31 := by
    have hnat : (103578891 : ℕ)^39*50000000000000^31 ≤ 380862623119^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103578891 5000000000 380862623119 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3760547553/10000000000 : ℝ), (7533152517/10000000000 : ℝ), (-103578891/5000000000 : ℝ)] ![(7304297781519/25000000000000 : ℝ), (14004216724213/20000000000000 : ℝ), (380862623119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3760547553/10000000000 : ℝ)|^39 ≤ (7304297781519/25000000000000 : ℝ)^31
        have hw : |(3760547553/10000000000 : ℝ)|=(3760547553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7533152517/10000000000 : ℝ)|^39 ≤ (14004216724213/20000000000000 : ℝ)^31
        have hw : |(7533152517/10000000000 : ℝ)|=(7533152517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103578891/5000000000 : ℝ)|^39 ≤ (380862623119/50000000000000 : ℝ)^31
        have hw : |(-103578891/5000000000 : ℝ)|=(103578891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (18406741/5000000000 : ℝ)*x 0 + (341456167/400000000 : ℝ)*x 1 + (638715533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18406741/5000000000 : ℝ)^39 ≤ (86672164943/100000000000000 : ℝ)^31 := by
    have hnat : (18406741 : ℕ)^39*100000000000000^31 ≤ 86672164943^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18406741 5000000000 86672164943 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341456167/400000000 : ℝ)^39 ≤ (10243526394339/12500000000000 : ℝ)^31 := by
    have hnat : (341456167 : ℕ)^39*12500000000000^31 ≤ 10243526394339^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341456167 400000000 10243526394339 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638715533/2500000000 : ℝ)^39 ≤ (8982558335463/50000000000000 : ℝ)^31 := by
    have hnat : (638715533 : ℕ)^39*50000000000000^31 ≤ 8982558335463^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638715533 2500000000 8982558335463 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(18406741/5000000000 : ℝ), (341456167/400000000 : ℝ), (638715533/2500000000 : ℝ)] ![(86672164943/100000000000000 : ℝ), (10243526394339/12500000000000 : ℝ), (8982558335463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(18406741/5000000000 : ℝ)|^39 ≤ (86672164943/100000000000000 : ℝ)^31
        have hw : |(18406741/5000000000 : ℝ)|=(18406741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341456167/400000000 : ℝ)|^39 ≤ (10243526394339/12500000000000 : ℝ)^31
        have hw : |(341456167/400000000 : ℝ)|=(341456167/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638715533/2500000000 : ℝ)|^39 ≤ (8982558335463/50000000000000 : ℝ)^31
        have hw : |(638715533/2500000000 : ℝ)|=(638715533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2664758873/10000000000 : ℝ)*x 0 + (886035447/5000000000 : ℝ)*x 1 + (7507329109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2664758873/10000000000 : ℝ)^39 ≤ (9471322170889/50000000000000 : ℝ)^31 := by
    have hnat : (2664758873 : ℕ)^39*50000000000000^31 ≤ 9471322170889^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664758873 10000000000 9471322170889 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (886035447/5000000000 : ℝ)^39 ≤ (5669055823091/50000000000000 : ℝ)^31 := by
    have hnat : (886035447 : ℕ)^39*50000000000000^31 ≤ 5669055823091^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886035447 5000000000 5669055823091 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7507329109/10000000000 : ℝ)^39 ≤ (69719244008181/100000000000000 : ℝ)^31 := by
    have hnat : (7507329109 : ℕ)^39*100000000000000^31 ≤ 69719244008181^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7507329109 10000000000 69719244008181 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2664758873/10000000000 : ℝ), (886035447/5000000000 : ℝ), (7507329109/10000000000 : ℝ)] ![(9471322170889/50000000000000 : ℝ), (5669055823091/50000000000000 : ℝ), (69719244008181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2664758873/10000000000 : ℝ)|^39 ≤ (9471322170889/50000000000000 : ℝ)^31
        have hw : |(-2664758873/10000000000 : ℝ)|=(2664758873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(886035447/5000000000 : ℝ)|^39 ≤ (5669055823091/50000000000000 : ℝ)^31
        have hw : |(886035447/5000000000 : ℝ)|=(886035447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7507329109/10000000000 : ℝ)|^39 ≤ (69719244008181/100000000000000 : ℝ)^31
        have hw : |(7507329109/10000000000 : ℝ)|=(7507329109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7445408173/10000000000 : ℝ)*x 0 + (-1068346607/5000000000 : ℝ)*x 1 + (2405745849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7445408173/10000000000 : ℝ)^39 ≤ (3449828349701/5000000000000 : ℝ)^31 := by
    have hnat : (7445408173 : ℕ)^39*5000000000000^31 ≤ 3449828349701^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7445408173 10000000000 3449828349701 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1068346607/5000000000 : ℝ)^39 ≤ (7173686816773/50000000000000 : ℝ)^31 := by
    have hnat : (1068346607 : ℕ)^39*50000000000000^31 ≤ 7173686816773^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068346607 5000000000 7173686816773 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405745849/10000000000 : ℝ)^39 ≤ (520501855051/3125000000000 : ℝ)^31 := by
    have hnat : (2405745849 : ℕ)^39*3125000000000^31 ≤ 520501855051^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405745849 10000000000 520501855051 3125000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7445408173/10000000000 : ℝ), (-1068346607/5000000000 : ℝ), (2405745849/10000000000 : ℝ)] ![(3449828349701/5000000000000 : ℝ), (7173686816773/50000000000000 : ℝ), (520501855051/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7445408173/10000000000 : ℝ)|^39 ≤ (3449828349701/5000000000000 : ℝ)^31
        have hw : |(7445408173/10000000000 : ℝ)|=(7445408173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1068346607/5000000000 : ℝ)|^39 ≤ (7173686816773/50000000000000 : ℝ)^31
        have hw : |(-1068346607/5000000000 : ℝ)|=(1068346607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405745849/10000000000 : ℝ)|^39 ≤ (520501855051/3125000000000 : ℝ)^31
        have hw : |(2405745849/10000000000 : ℝ)|=(2405745849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1663534677/2000000000 : ℝ)*x 0 + (1351154879/5000000000 : ℝ)*x 1 + (-337120297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1663534677/2000000000 : ℝ)^39 ≤ (79315338503583/100000000000000 : ℝ)^31 := by
    have hnat : (1663534677 : ℕ)^39*100000000000000^31 ≤ 79315338503583^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663534677 2000000000 79315338503583 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351154879/5000000000 : ℝ)^39 ≤ (19279072237829/100000000000000 : ℝ)^31 := by
    have hnat : (1351154879 : ℕ)^39*100000000000000^31 ≤ 19279072237829^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351154879 5000000000 19279072237829 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337120297/10000000000 : ℝ)^39 ≤ (702794619629/50000000000000 : ℝ)^31 := by
    have hnat : (337120297 : ℕ)^39*50000000000000^31 ≤ 702794619629^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337120297 10000000000 702794619629 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1663534677/2000000000 : ℝ), (1351154879/5000000000 : ℝ), (-337120297/10000000000 : ℝ)] ![(79315338503583/100000000000000 : ℝ), (19279072237829/100000000000000 : ℝ), (702794619629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1663534677/2000000000 : ℝ)|^39 ≤ (79315338503583/100000000000000 : ℝ)^31
        have hw : |(1663534677/2000000000 : ℝ)|=(1663534677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351154879/5000000000 : ℝ)|^39 ≤ (19279072237829/100000000000000 : ℝ)^31
        have hw : |(1351154879/5000000000 : ℝ)|=(1351154879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337120297/10000000000 : ℝ)|^39 ≤ (702794619629/50000000000000 : ℝ)^31
        have hw : |(-337120297/10000000000 : ℝ)|=(337120297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-193/5000000000 : ℝ)*x 0 + (483619793/1250000000 : ℝ)*x 1 + (7507329109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193/5000000000 : ℝ)^39 ≤ (47147/100000000000000 : ℝ)^31 := by
    have hnat : (193 : ℕ)^39*100000000000000^31 ≤ 47147^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193 5000000000 47147 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483619793/1250000000 : ℝ)^39 ≤ (15140377970581/50000000000000 : ℝ)^31 := by
    have hnat : (483619793 : ℕ)^39*50000000000000^31 ≤ 15140377970581^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483619793 1250000000 15140377970581 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7507329109/10000000000 : ℝ)^39 ≤ (69719244008181/100000000000000 : ℝ)^31 := by
    have hnat : (7507329109 : ℕ)^39*100000000000000^31 ≤ 69719244008181^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7507329109 10000000000 69719244008181 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-193/5000000000 : ℝ), (483619793/1250000000 : ℝ), (7507329109/10000000000 : ℝ)] ![(47147/100000000000000 : ℝ), (15140377970581/50000000000000 : ℝ), (69719244008181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-193/5000000000 : ℝ)|^39 ≤ (47147/100000000000000 : ℝ)^31
        have hw : |(-193/5000000000 : ℝ)|=(193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(483619793/1250000000 : ℝ)|^39 ≤ (15140377970581/50000000000000 : ℝ)^31
        have hw : |(483619793/1250000000 : ℝ)|=(483619793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7507329109/10000000000 : ℝ)|^39 ≤ (69719244008181/100000000000000 : ℝ)^31
        have hw : |(7507329109/10000000000 : ℝ)|=(7507329109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1127811437/2000000000 : ℝ)*x 0 + (692787391/2500000000 : ℝ)*x 1 + (797652999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127811437/2000000000 : ℝ)^39 ≤ (48640913681099/100000000000000 : ℝ)^31 := by
    have hnat : (1127811437 : ℕ)^39*100000000000000^31 ≤ 48640913681099^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127811437 2000000000 48640913681099 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692787391/2500000000 : ℝ)^39 ≤ (19898955458801/100000000000000 : ℝ)^31 := by
    have hnat : (692787391 : ℕ)^39*100000000000000^31 ≤ 19898955458801^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692787391 2500000000 19898955458801 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797652999/2000000000 : ℝ)^39 ≤ (15730065423639/50000000000000 : ℝ)^31 := by
    have hnat : (797652999 : ℕ)^39*50000000000000^31 ≤ 15730065423639^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797652999 2000000000 15730065423639 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1127811437/2000000000 : ℝ), (692787391/2500000000 : ℝ), (797652999/2000000000 : ℝ)] ![(48640913681099/100000000000000 : ℝ), (19898955458801/100000000000000 : ℝ), (15730065423639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1127811437/2000000000 : ℝ)|^39 ≤ (48640913681099/100000000000000 : ℝ)^31
        have hw : |(-1127811437/2000000000 : ℝ)|=(1127811437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692787391/2500000000 : ℝ)|^39 ≤ (19898955458801/100000000000000 : ℝ)^31
        have hw : |(692787391/2500000000 : ℝ)|=(692787391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(797652999/2000000000 : ℝ)|^39 ≤ (15730065423639/50000000000000 : ℝ)^31
        have hw : |(797652999/2000000000 : ℝ)|=(797652999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3864847471/10000000000 : ℝ)*x 0 + (-855317607/2500000000 : ℝ)*x 1 + (5190026779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3864847471/10000000000 : ℝ)^39 ≤ (189001777309/625000000000 : ℝ)^31 := by
    have hnat : (3864847471 : ℕ)^39*625000000000^31 ≤ 189001777309^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3864847471 10000000000 189001777309 625000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855317607/2500000000 : ℝ)^39 ≤ (25940461679153/100000000000000 : ℝ)^31 := by
    have hnat : (855317607 : ℕ)^39*100000000000000^31 ≤ 25940461679153^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855317607 2500000000 25940461679153 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190026779/10000000000 : ℝ)^39 ≤ (43819253933493/100000000000000 : ℝ)^31 := by
    have hnat : (5190026779 : ℕ)^39*100000000000000^31 ≤ 43819253933493^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190026779 10000000000 43819253933493 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3864847471/10000000000 : ℝ), (-855317607/2500000000 : ℝ), (5190026779/10000000000 : ℝ)] ![(189001777309/625000000000 : ℝ), (25940461679153/100000000000000 : ℝ), (43819253933493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3864847471/10000000000 : ℝ)|^39 ≤ (189001777309/625000000000 : ℝ)^31
        have hw : |(3864847471/10000000000 : ℝ)|=(3864847471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855317607/2500000000 : ℝ)|^39 ≤ (25940461679153/100000000000000 : ℝ)^31
        have hw : |(-855317607/2500000000 : ℝ)|=(855317607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190026779/10000000000 : ℝ)|^39 ≤ (43819253933493/100000000000000 : ℝ)^31
        have hw : |(5190026779/10000000000 : ℝ)|=(5190026779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (313298569/400000000 : ℝ)*x 0 + (3373533699/10000000000 : ℝ)*x 1 + (-252093177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (313298569/400000000 : ℝ)^39 ≤ (73538940233451/100000000000000 : ℝ)^31 := by
    have hnat : (313298569 : ℕ)^39*100000000000000^31 ≤ 73538940233451^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313298569 400000000 73538940233451 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3373533699/10000000000 : ℝ)^39 ≤ (12742966887797/50000000000000 : ℝ)^31 := by
    have hnat : (3373533699 : ℕ)^39*50000000000000^31 ≤ 12742966887797^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3373533699 10000000000 12742966887797 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252093177/10000000000 : ℝ)^39 ≤ (975125981401/100000000000000 : ℝ)^31 := by
    have hnat : (252093177 : ℕ)^39*100000000000000^31 ≤ 975125981401^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252093177 10000000000 975125981401 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(313298569/400000000 : ℝ), (3373533699/10000000000 : ℝ), (-252093177/10000000000 : ℝ)] ![(73538940233451/100000000000000 : ℝ), (12742966887797/50000000000000 : ℝ), (975125981401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(313298569/400000000 : ℝ)|^39 ≤ (73538940233451/100000000000000 : ℝ)^31
        have hw : |(313298569/400000000 : ℝ)|=(313298569/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3373533699/10000000000 : ℝ)|^39 ≤ (12742966887797/50000000000000 : ℝ)^31
        have hw : |(3373533699/10000000000 : ℝ)|=(3373533699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-252093177/10000000000 : ℝ)|^39 ≤ (975125981401/100000000000000 : ℝ)^31
        have hw : |(-252093177/10000000000 : ℝ)|=(252093177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s0_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-21015773/10000000000 : ℝ)*x 0 + (1480506173/2000000000 : ℝ)*x 1 + (797652999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21015773/10000000000 : ℝ)^39 ≤ (21407174011/50000000000000 : ℝ)^31 := by
    have hnat : (21015773 : ℕ)^39*50000000000000^31 ≤ 21407174011^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21015773 10000000000 21407174011 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1480506173/2000000000 : ℝ)^39 ≤ (68497054797359/100000000000000 : ℝ)^31 := by
    have hnat : (1480506173 : ℕ)^39*100000000000000^31 ≤ 68497054797359^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480506173 2000000000 68497054797359 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797652999/2000000000 : ℝ)^39 ≤ (15730065423639/50000000000000 : ℝ)^31 := by
    have hnat : (797652999 : ℕ)^39*50000000000000^31 ≤ 15730065423639^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797652999 2000000000 15730065423639 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21015773/10000000000 : ℝ), (1480506173/2000000000 : ℝ), (797652999/2000000000 : ℝ)] ![(21407174011/50000000000000 : ℝ), (68497054797359/100000000000000 : ℝ), (15730065423639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21015773/10000000000 : ℝ)|^39 ≤ (21407174011/50000000000000 : ℝ)^31
        have hw : |(-21015773/10000000000 : ℝ)|=(21015773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1480506173/2000000000 : ℝ)|^39 ≤ (68497054797359/100000000000000 : ℝ)^31
        have hw : |(1480506173/2000000000 : ℝ)|=(1480506173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(797652999/2000000000 : ℝ)|^39 ≤ (15730065423639/50000000000000 : ℝ)^31
        have hw : |(797652999/2000000000 : ℝ)|=(797652999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-790280033/2000000000 : ℝ)*x 0 + (3333448933/10000000000 : ℝ)*x 1 + (1297047119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (790280033/2000000000 : ℝ)^39 ≤ (3109472777907/10000000000000 : ℝ)^31 := by
    have hnat : (790280033 : ℕ)^39*10000000000000^31 ≤ 3109472777907^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790280033 2000000000 3109472777907 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3333448933/10000000000 : ℝ)^39 ≤ (25105543477413/100000000000000 : ℝ)^31 := by
    have hnat : (3333448933 : ℕ)^39*100000000000000^31 ≤ 25105543477413^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3333448933 10000000000 25105543477413 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297047119/2500000000 : ℝ)^39 ≤ (43799728731357/100000000000000 : ℝ)^31 := by
    have hnat : (1297047119 : ℕ)^39*100000000000000^31 ≤ 43799728731357^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297047119 2500000000 43799728731357 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-790280033/2000000000 : ℝ), (3333448933/10000000000 : ℝ), (1297047119/2500000000 : ℝ)] ![(3109472777907/10000000000000 : ℝ), (25105543477413/100000000000000 : ℝ), (43799728731357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-790280033/2000000000 : ℝ)|^39 ≤ (3109472777907/10000000000000 : ℝ)^31
        have hw : |(-790280033/2000000000 : ℝ)|=(790280033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3333448933/10000000000 : ℝ)|^39 ≤ (25105543477413/100000000000000 : ℝ)^31
        have hw : |(3333448933/10000000000 : ℝ)|=(3333448933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297047119/2500000000 : ℝ)|^39 ≤ (43799728731357/100000000000000 : ℝ)^31
        have hw : |(1297047119/2500000000 : ℝ)|=(1297047119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s1_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (129458317/312500000 : ℝ)*x 0 + (-3369622049/10000000000 : ℝ)*x 1 + (4975347883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129458317/312500000 : ℝ)^39 ≤ (32999964045503/100000000000000 : ℝ)^31 := by
    have hnat : (129458317 : ℕ)^39*100000000000000^31 ≤ 32999964045503^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129458317 312500000 32999964045503 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3369622049/10000000000 : ℝ)^39 ≤ (25448761992071/100000000000000 : ℝ)^31 := by
    have hnat : (3369622049 : ℕ)^39*100000000000000^31 ≤ 25448761992071^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3369622049 10000000000 25448761992071 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4975347883/10000000000 : ℝ)^39 ≤ (4155127394253/10000000000000 : ℝ)^31 := by
    have hnat : (4975347883 : ℕ)^39*10000000000000^31 ≤ 4155127394253^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4975347883 10000000000 4155127394253 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129458317/312500000 : ℝ), (-3369622049/10000000000 : ℝ), (4975347883/10000000000 : ℝ)] ![(32999964045503/100000000000000 : ℝ), (25448761992071/100000000000000 : ℝ), (4155127394253/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129458317/312500000 : ℝ)|^39 ≤ (32999964045503/100000000000000 : ℝ)^31
        have hw : |(129458317/312500000 : ℝ)|=(129458317/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3369622049/10000000000 : ℝ)|^39 ≤ (25448761992071/100000000000000 : ℝ)^31
        have hw : |(-3369622049/10000000000 : ℝ)|=(3369622049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4975347883/10000000000 : ℝ)|^39 ≤ (4155127394253/10000000000000 : ℝ)^31
        have hw : |(4975347883/10000000000 : ℝ)|=(4975347883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (668494147/1250000000 : ℝ)*x 0 + (5301577759/10000000000 : ℝ)*x 1 + (-769137741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668494147/1250000000 : ℝ)^39 ≤ (22751627256767/50000000000000 : ℝ)^31 := by
    have hnat : (668494147 : ℕ)^39*50000000000000^31 ≤ 22751627256767^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668494147 1250000000 22751627256767 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5301577759/10000000000 : ℝ)^39 ≤ (22503697674173/50000000000000 : ℝ)^31 := by
    have hnat : (5301577759 : ℕ)^39*50000000000000^31 ≤ 22503697674173^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301577759 10000000000 22503697674173 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769137741/5000000000 : ℝ)^39 ≤ (9489350128277/100000000000000 : ℝ)^31 := by
    have hnat : (769137741 : ℕ)^39*100000000000000^31 ≤ 9489350128277^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769137741 5000000000 9489350128277 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668494147/1250000000 : ℝ), (5301577759/10000000000 : ℝ), (-769137741/5000000000 : ℝ)] ![(22751627256767/50000000000000 : ℝ), (22503697674173/50000000000000 : ℝ), (9489350128277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668494147/1250000000 : ℝ)|^39 ≤ (22751627256767/50000000000000 : ℝ)^31
        have hw : |(668494147/1250000000 : ℝ)|=(668494147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5301577759/10000000000 : ℝ)|^39 ≤ (22503697674173/50000000000000 : ℝ)^31
        have hw : |(5301577759/10000000000 : ℝ)|=(5301577759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-769137741/5000000000 : ℝ)|^39 ≤ (9489350128277/100000000000000 : ℝ)^31
        have hw : |(-769137741/5000000000 : ℝ)|=(769137741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317082_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1020397/7812500 : ℝ)*x 0 + (100260779/200000000 : ℝ)*x 1 + (1158801103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020397/7812500 : ℝ)^39 ≤ (3862021901301/50000000000000 : ℝ)^31 := by
    have hnat : (1020397 : ℕ)^39*50000000000000^31 ≤ 3862021901301^31*7812500^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020397 7812500 3862021901301 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100260779/200000000 : ℝ)^39 ≤ (20973833370801/50000000000000 : ℝ)^31 := by
    have hnat : (100260779 : ℕ)^39*50000000000000^31 ≤ 20973833370801^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100260779 200000000 20973833370801 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158801103/2000000000 : ℝ)^39 ≤ (5032828944383/10000000000000 : ℝ)^31 := by
    have hnat : (1158801103 : ℕ)^39*10000000000000^31 ≤ 5032828944383^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158801103 2000000000 5032828944383 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020397/7812500 : ℝ), (100260779/200000000 : ℝ), (1158801103/2000000000 : ℝ)] ![(3862021901301/50000000000000 : ℝ), (20973833370801/50000000000000 : ℝ), (5032828944383/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020397/7812500 : ℝ)|^39 ≤ (3862021901301/50000000000000 : ℝ)^31
        have hw : |(1020397/7812500 : ℝ)|=(1020397/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100260779/200000000 : ℝ)|^39 ≤ (20973833370801/50000000000000 : ℝ)^31
        have hw : |(100260779/200000000 : ℝ)|=(100260779/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1158801103/2000000000 : ℝ)|^39 ≤ (5032828944383/10000000000000 : ℝ)^31
        have hw : |(1158801103/2000000000 : ℝ)|=(1158801103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317082 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (34473/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((2071801021/5000000000 : ℝ)*X 1 0+(-2795552013/10000000000 : ℝ)*X 1 1+(34220873/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2961116707/10000000000 : ℝ)*X 0 0+(286391763/2000000000 : ℝ)*X 0 1+(7505531339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4180666031/10000000000 : ℝ)*X 1 0+(-297778221/5000000000 : ℝ)*X 1 1+(3495571471/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3760547553/10000000000 : ℝ)*X 2 0+(7533152517/10000000000 : ℝ)*X 2 1+(-103578891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((18406741/5000000000 : ℝ)*X 0 0+(341456167/400000000 : ℝ)*X 0 1+(638715533/2500000000 : ℝ)*X 0 2+(18406741/5000000000 : ℝ)*X 1 0+(341456167/400000000 : ℝ)*X 1 1+(638715533/2500000000 : ℝ)*X 1 2+(18406741/5000000000 : ℝ)*X 2 0+(341456167/400000000 : ℝ)*X 2 1+(638715533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2664758873/10000000000 : ℝ)*X 0 0+(886035447/5000000000 : ℝ)*X 0 1+(7507329109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((7445408173/10000000000 : ℝ)*X 1 0+(-1068346607/5000000000 : ℝ)*X 1 1+(2405745849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1663534677/2000000000 : ℝ)*X 2 0+(1351154879/5000000000 : ℝ)*X 2 1+(-337120297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-193/5000000000 : ℝ)*X 0 0+(483619793/1250000000 : ℝ)*X 0 1+(7507329109/10000000000 : ℝ)*X 0 2+(-193/5000000000 : ℝ)*X 1 0+(483619793/1250000000 : ℝ)*X 1 1+(7507329109/10000000000 : ℝ)*X 1 2+(-193/5000000000 : ℝ)*X 2 0+(483619793/1250000000 : ℝ)*X 2 1+(7507329109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1127811437/2000000000 : ℝ)*X 0 0+(692787391/2500000000 : ℝ)*X 0 1+(797652999/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3864847471/10000000000 : ℝ)*X 1 0+(-855317607/2500000000 : ℝ)*X 1 1+(5190026779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((313298569/400000000 : ℝ)*X 2 0+(3373533699/10000000000 : ℝ)*X 2 1+(-252093177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-21015773/10000000000 : ℝ)*X 0 0+(1480506173/2000000000 : ℝ)*X 0 1+(797652999/2000000000 : ℝ)*X 0 2+(-21015773/10000000000 : ℝ)*X 1 0+(1480506173/2000000000 : ℝ)*X 1 1+(797652999/2000000000 : ℝ)*X 1 2+(-21015773/10000000000 : ℝ)*X 2 0+(1480506173/2000000000 : ℝ)*X 2 1+(797652999/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((65251/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65251/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15564829112714638782429/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106305606619/125000000000 : ℝ)*(base7) + (84992981523/1000000000000 : ℝ)*(base49) + (6041828013/40000000000 : ℝ)*(base53) + (12328544593/1000000000000 : ℝ)*(base60) + (1575781153201/1000000000000 : ℝ)*(major_s0_0) + (1575781153201/1000000000000 : ℝ)*(major_s0_1) + (356183863219/250000000000 : ℝ)*(major_s0_2) + (1626229/500000000000 : ℝ)*(sp_s0_1) + (327138000593/200000000000 : ℝ)*(sp_s0_7) + (817891266519/500000000000 : ℝ)*(sp_s0_8) + (1786831485821/1000000000000 : ℝ)*(sp_s0_9) + (1726546649707/1000000000000 : ℝ)*(sp_s0_13) + (95782531/1000000000000 : ℝ)*(sp_s0_14) + (482281/125000000000 : ℝ)*(sp_s0_27) + (876105655003/1000000000000 : ℝ)*(f.failure) + (1786831485821/1000000000000 : ℝ)*(f.sum) + (3854682690385061/10000000000000000000000000000 : ℝ)*base62 + (1518695080729053/2500000000000000000000000000 : ℝ)*base64 + (4067842945045477/10000000000000000000000000000 : ℝ)*base66 + (1327214419201137/2500000000000000000000000000 : ℝ)*base68 + (5084116230961689/10000000000000000000000000000 : ℝ)*base70 + (4004415074419487/10000000000000000000000000000 : ℝ)*base72 + (1760210328580513/10000000000000000000000000000 : ℝ)*base74 + (3141916549045477/10000000000000000000000000000 : ℝ)*base76 + (136239665866241/2500000000000000000000000000 : ℝ)*base78 + (24793/50000000000000000 : ℝ)*base87 + (24793/50000000000000000 : ℝ)*base89 + (24793/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((75911/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(75911/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (56939898748826831594493/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16100055969/250000000000 : ℝ)*(base1) + (230765063249/200000000000 : ℝ)*(base7) + (22398246423/500000000000 : ℝ)*(base39) + (1084319/200000000000 : ℝ)*(base53) + (14878746759/200000000000 : ℝ)*(base60) + (1822181706153/1000000000000 : ℝ)*(major_s0_0) + (1822181706153/1000000000000 : ℝ)*(major_s0_1) + (911088142279/500000000000 : ℝ)*(major_s0_2) + (19002993/200000000000 : ℝ)*(sp_s0_7) + (2032629188183/1000000000000 : ℝ)*(sp_s0_14) + (246040497409/125000000000 : ℝ)*(sp_s0_15) + (492077407307/250000000000 : ℝ)*(sp_s0_16) + (2102524972361/1000000000000 : ℝ)*(sp_s0_20) + (9885819/500000000000 : ℝ)*(sp_s0_23) + (1013099879993/1000000000000 : ℝ)*(f.failure) + (984164700433/500000000000 : ℝ)*(f.sum) + (137089905211277/10000000000000000000000000000 : ℝ)*base63 + (1889530562532727/5000000000000000000000000000 : ℝ)*base65 + (2291902731929219/10000000000000000000000000000 : ℝ)*base67 + (406455684226483/5000000000000000000000000000 : ℝ)*base69 + (2573699572994673/10000000000000000000000000000 : ℝ)*base71 + (1912068743758311/10000000000000000000000000000 : ℝ)*base72 + (4361254482758311/10000000000000000000000000000 : ℝ)*base75 + (4479700192929219/10000000000000000000000000000 : ℝ)*base77 + (352248497292727/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (483/50000000000000000 : ℝ)*base87 + (483/50000000000000000 : ℝ)*base89 + (483/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4317/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4317/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (53820510518271182666259/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135156109159/1000000000000 : ℝ)*(base1) + (261950701649/250000000000 : ℝ)*(base7) + (6936945933/50000000000 : ℝ)*(base39) + (345884905493/1000000000000 : ℝ)*(base44) + (2194851457961/1000000000000 : ℝ)*(major_s0_0) + (462241638117/250000000000 : ℝ)*(major_s0_1) + (2194851457961/1000000000000 : ℝ)*(major_s0_2) + (4485883/31250000000 : ℝ)*(sp_s0_1) + (3880977/1000000000000 : ℝ)*(sp_s0_15) + (1529211/100000000000 : ℝ)*(sp_s0_16) + (2702542852019/1000000000000 : ℝ)*(sp_s0_21) + (1110677204067/500000000000 : ℝ)*(sp_s0_22) + (10269485803/4000000000 : ℝ)*(sp_s0_23) + (1787059274437/1000000000000 : ℝ)*(sp_s0_27) + (1220297482493/1000000000000 : ℝ)*(f.failure) + (128369337143/50000000000 : ℝ)*(f.sum) + (1800696568804713/10000000000000000000000000000 : ℝ)*base63 + (6135894053093607/10000000000000000000000000000 : ℝ)*base64 + (1728026237668009/2500000000000000000000000000 : ℝ)*base66 + (7688674628248003/10000000000000000000000000000 : ℝ)*base68 + (495039259211401/2500000000000000000000000000 : ℝ)*base70 + (6689792086093607/10000000000000000000000000000 : ℝ)*base72 + (1889361125986821/2500000000000000000000000000 : ℝ)*base74 + (7267755092751997/10000000000000000000000000000 : ℝ)*base76 + (707366957765643/10000000000000000000000000000 : ℝ)*base78 + (27983/50000000000000000 : ℝ)*base87 + (27983/50000000000000000 : ℝ)*base89 + (27983/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (65251/100000 : ℝ) ^ (77/16 : ℝ) ≤ (1281447341273173457/10000000000000000000 : ℝ) := by
    have hpowers : (65251/100000 : ℝ)^77 ≤ (1281447341273173457/10000000000000000000 : ℝ)^16 := by
      have hnat : (65251 : ℕ)^77*10000000000000000000^16 ≤ 1281447341273173457^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65251 100000 1281447341273173457 10000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65251/100000 : ℝ)) (X := (1281447341273173457/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (11281447341273173457/10000000000000000000 : ℝ) ≤ (10253709322605077/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (11281447341273173457/10000000000000000000 : ℝ)^16 ≤ (10253709322605077/10000000000000000 : ℝ)^77 := by
      have hnat : (11281447341273173457 : ℕ)^16*10000000000000000^77 ≤ 10253709322605077^77*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11281447341273173457 10000000000000000000 10253709322605077 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10253709322605077/10000000000000000 : ℝ)) (X := (11281447341273173457/10000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6281447341273173457/5000000000000000000 : ℝ) ≤ (10485522378825001/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (6281447341273173457/5000000000000000000 : ℝ)^16 ≤ (10485522378825001/10000000000000000 : ℝ)^77 := by
      have hnat : (6281447341273173457 : ℕ)^16*10000000000000000^77 ≤ 10485522378825001^77*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6281447341273173457 5000000000000000000 10485522378825001 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10485522378825001/10000000000000000 : ℝ)) (X := (6281447341273173457/5000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(253709322605077/6525100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(57953264054981/1631275000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (65251/100000 : ℝ)) (alpha := (253709322605077/6525100000000000 : ℝ)) (beta := (57953264054981/1631275000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (65251/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(253709322605077/6525100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(57953264054981/1631275000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (75911/100000 : ℝ) ^ (77/16 : ℝ) ≤ (26544003699890988277/100000000000000000000 : ℝ) := by
    have hpowers : (75911/100000 : ℝ)^77 ≤ (26544003699890988277/100000000000000000000 : ℝ)^16 := by
      have hnat : (75911 : ℕ)^77*100000000000000000000^16 ≤ 26544003699890988277^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75911 100000 26544003699890988277 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75911/100000 : ℝ)) (X := (26544003699890988277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (126544003699890988277/100000000000000000000 : ℝ) ≤ (5250673408961089/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (126544003699890988277/100000000000000000000 : ℝ)^16 ≤ (5250673408961089/5000000000000000 : ℝ)^77 := by
      have hnat : (126544003699890988277 : ℕ)^16*5000000000000000^77 ≤ 5250673408961089^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        126544003699890988277 100000000000000000000 5250673408961089 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5250673408961089/5000000000000000 : ℝ)) (X := (126544003699890988277/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (76544003699890988277/50000000000000000000 : ℝ) ≤ (2731299610368401/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (76544003699890988277/50000000000000000000 : ℝ)^16 ≤ (2731299610368401/2500000000000000 : ℝ)^77 := by
      have hnat : (76544003699890988277 : ℕ)^16*2500000000000000^77 ≤ 2731299610368401^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76544003699890988277 50000000000000000000 2731299610368401 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2731299610368401/2500000000000000 : ℝ)) (X := (76544003699890988277/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(250673408961089/3795550000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(211925811775713/3795550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (75911/100000 : ℝ)) (alpha := (250673408961089/3795550000000000 : ℝ)) (beta := (211925811775713/3795550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (75911/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(250673408961089/3795550000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(211925811775713/3795550000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (4317/6250 : ℝ) ^ (77/16 : ℝ) ≤ (16851595490993589639/100000000000000000000 : ℝ) := by
    have hpowers : (4317/6250 : ℝ)^77 ≤ (16851595490993589639/100000000000000000000 : ℝ)^16 := by
      have hnat : (4317 : ℕ)^77*100000000000000000000^16 ≤ 16851595490993589639^16*6250^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4317 6250 16851595490993589639 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4317/6250 : ℝ)) (X := (16851595490993589639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (116851595490993589639/100000000000000000000 : ℝ) ≤ (5164448570085901/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (116851595490993589639/100000000000000000000 : ℝ)^16 ≤ (5164448570085901/5000000000000000 : ℝ)^77 := by
      have hnat : (116851595490993589639 : ℕ)^16*5000000000000000^77 ≤ 5164448570085901^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116851595490993589639 100000000000000000000 5164448570085901 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5164448570085901/5000000000000000 : ℝ)) (X := (116851595490993589639/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (66851595490993589639/50000000000000000000 : ℝ) ≤ (5311060904385717/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (66851595490993589639/50000000000000000000 : ℝ)^16 ≤ (5311060904385717/5000000000000000 : ℝ)^77 := by
      have hnat : (66851595490993589639 : ℕ)^16*5000000000000000^77 ≤ 5311060904385717^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66851595490993589639 50000000000000000000 5311060904385717 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5311060904385717/5000000000000000 : ℝ)) (X := (66851595490993589639/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(164448570085901/3453600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(18326541787477/431700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (4317/6250 : ℝ)) (alpha := (164448570085901/3453600000000000 : ℝ)) (beta := (18326541787477/431700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (4317/6250 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(164448570085901/3453600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(18326541787477/431700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-790280033/2000000000 : ℝ)*X 0 0+(3333448933/10000000000 : ℝ)*X 0 1+(1297047119/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((129458317/312500000 : ℝ)*X 1 0+(-3369622049/10000000000 : ℝ)*X 1 1+(4975347883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((668494147/1250000000 : ℝ)*X 2 0+(5301577759/10000000000 : ℝ)*X 2 1+(-769137741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1020397/7812500 : ℝ)*X 0 0+(100260779/200000000 : ℝ)*X 0 1+(1158801103/2000000000 : ℝ)*X 0 2+(1020397/7812500 : ℝ)*X 1 0+(100260779/200000000 : ℝ)*X 1 1+(1158801103/2000000000 : ℝ)*X 1 2+(1020397/7812500 : ℝ)*X 2 0+(100260779/200000000 : ℝ)*X 2 1+(1158801103/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317082_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-172332364025846537224493490812782023/22274230009934375000000000000000000 : ℝ) := by norm_num
    linear_combination (2345227/1000000000000 : ℝ)*(base15) + (2247743/500000000000 : ℝ)*(base19) + (146319/500000000000 : ℝ)*(base33) + (335167/1000000000000 : ℝ)*(base39) + (23546552877/125000000000 : ℝ)*(base49) + (213111/1000000000000 : ℝ)*(base50) + (1159879/1000000000000 : ℝ)*(base59) + (513992586311/1000000000000 : ℝ)*(base60) + (899309853681/500000000000 : ℝ)*(major_s1_0) + (89931/50000 : ℝ)*(major_s1_1) + (89931/50000 : ℝ)*(major_s1_2) + (2578949814033/1000000000000 : ℝ)*(sp_s1_0) + (1289471340341/500000000000 : ℝ)*(sp_s1_1) + (644737380349/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2578949814033/1000000000000 : ℝ)*(f.sum) + (290709421811265319/218471858000000000000000000000 : ℝ)*base62 + (3417631700629/14390000000000000000000000 : ℝ)*base65 + (13471761989497/189777500000000000000000000 : ℝ)*base66 + (33533532457/899375000000000000000000 : ℝ)*base68 + (306947907969989147/4694809450000000000000000000000 : ℝ)*base70 + (693956670625857/1631275000000000000000000000 : ℝ)*base73 + (26074333663033/23722187500000000000000000 : ℝ)*base74 + (601246571174383/3262550000000000000000000000 : ℝ)*base76 + (3298856480786971061/61915858262500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c317084_s0_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2062175327/5000000000 : ℝ)*x 0 + (-99647299/200000000 : ℝ)*x 1 + (676232651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062175327/5000000000 : ℝ)^39 ≤ (32816518618397/100000000000000 : ℝ)^31 := by
    have hnat : (2062175327 : ℕ)^39*100000000000000^31 ≤ 32816518618397^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062175327 5000000000 32816518618397 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99647299/200000000 : ℝ)^39 ≤ (2081250657171/5000000000000 : ℝ)^31 := by
    have hnat : (99647299 : ℕ)^39*5000000000000^31 ≤ 2081250657171^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99647299 200000000 2081250657171 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676232651/2000000000 : ℝ)^39 ≤ (25558468225459/100000000000000 : ℝ)^31 := by
    have hnat : (676232651 : ℕ)^39*100000000000000^31 ≤ 25558468225459^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676232651 2000000000 25558468225459 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2062175327/5000000000 : ℝ), (-99647299/200000000 : ℝ), (676232651/2000000000 : ℝ)] ![(32816518618397/100000000000000 : ℝ), (2081250657171/5000000000000 : ℝ), (25558468225459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2062175327/5000000000 : ℝ)|^39 ≤ (32816518618397/100000000000000 : ℝ)^31
        have hw : |(-2062175327/5000000000 : ℝ)|=(2062175327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99647299/200000000 : ℝ)|^39 ≤ (2081250657171/5000000000000 : ℝ)^31
        have hw : |(-99647299/200000000 : ℝ)|=(99647299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676232651/2000000000 : ℝ)|^39 ≤ (25558468225459/100000000000000 : ℝ)^31
        have hw : |(676232651/2000000000 : ℝ)|=(676232651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317084_s0_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (676232651/2000000000 : ℝ)*x 0 + (2062175327/5000000000 : ℝ)*x 1 + (99647299/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676232651/2000000000 : ℝ)^39 ≤ (25558468225459/100000000000000 : ℝ)^31 := by
    have hnat : (676232651 : ℕ)^39*100000000000000^31 ≤ 25558468225459^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676232651 2000000000 25558468225459 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062175327/5000000000 : ℝ)^39 ≤ (32816518618397/100000000000000 : ℝ)^31 := by
    have hnat : (2062175327 : ℕ)^39*100000000000000^31 ≤ 32816518618397^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062175327 5000000000 32816518618397 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99647299/200000000 : ℝ)^39 ≤ (2081250657171/5000000000000 : ℝ)^31 := by
    have hnat : (99647299 : ℕ)^39*5000000000000^31 ≤ 2081250657171^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99647299 200000000 2081250657171 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676232651/2000000000 : ℝ), (2062175327/5000000000 : ℝ), (99647299/200000000 : ℝ)] ![(25558468225459/100000000000000 : ℝ), (32816518618397/100000000000000 : ℝ), (2081250657171/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676232651/2000000000 : ℝ)|^39 ≤ (25558468225459/100000000000000 : ℝ)^31
        have hw : |(676232651/2000000000 : ℝ)|=(676232651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062175327/5000000000 : ℝ)|^39 ≤ (32816518618397/100000000000000 : ℝ)^31
        have hw : |(2062175327/5000000000 : ℝ)|=(2062175327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(99647299/200000000 : ℝ)|^39 ≤ (2081250657171/5000000000000 : ℝ)^31
        have hw : |(99647299/200000000 : ℝ)|=(99647299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317084_s0_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (99647299/200000000 : ℝ)*x 0 + (-676232651/2000000000 : ℝ)*x 1 + (-2062175327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99647299/200000000 : ℝ)^39 ≤ (2081250657171/5000000000000 : ℝ)^31 := by
    have hnat : (99647299 : ℕ)^39*5000000000000^31 ≤ 2081250657171^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99647299 200000000 2081250657171 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676232651/2000000000 : ℝ)^39 ≤ (25558468225459/100000000000000 : ℝ)^31 := by
    have hnat : (676232651 : ℕ)^39*100000000000000^31 ≤ 25558468225459^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676232651 2000000000 25558468225459 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062175327/5000000000 : ℝ)^39 ≤ (32816518618397/100000000000000 : ℝ)^31 := by
    have hnat : (2062175327 : ℕ)^39*100000000000000^31 ≤ 32816518618397^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062175327 5000000000 32816518618397 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(99647299/200000000 : ℝ), (-676232651/2000000000 : ℝ), (-2062175327/5000000000 : ℝ)] ![(2081250657171/5000000000000 : ℝ), (25558468225459/100000000000000 : ℝ), (32816518618397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(99647299/200000000 : ℝ)|^39 ≤ (2081250657171/5000000000000 : ℝ)^31
        have hw : |(99647299/200000000 : ℝ)|=(99647299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-676232651/2000000000 : ℝ)|^39 ≤ (25558468225459/100000000000000 : ℝ)^31
        have hw : |(-676232651/2000000000 : ℝ)|=(676232651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2062175327/5000000000 : ℝ)|^39 ≤ (32816518618397/100000000000000 : ℝ)^31
        have hw : |(-2062175327/5000000000 : ℝ)|=(2062175327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317084_s0_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (208794847/500000000 : ℝ)*x 0 + (-208794847/500000000 : ℝ)*x 1 + (208794847/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208794847/500000000 : ℝ)^39 ≤ (33333333330181/100000000000000 : ℝ)^31 := by
    have hnat : (208794847 : ℕ)^39*100000000000000^31 ≤ 33333333330181^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208794847 500000000 33333333330181 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208794847/500000000 : ℝ)^39 ≤ (33333333330181/100000000000000 : ℝ)^31 := by
    have hnat : (208794847 : ℕ)^39*100000000000000^31 ≤ 33333333330181^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208794847 500000000 33333333330181 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208794847/500000000 : ℝ)^39 ≤ (33333333330181/100000000000000 : ℝ)^31 := by
    have hnat : (208794847 : ℕ)^39*100000000000000^31 ≤ 33333333330181^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208794847 500000000 33333333330181 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208794847/500000000 : ℝ), (-208794847/500000000 : ℝ), (208794847/500000000 : ℝ)] ![(33333333330181/100000000000000 : ℝ), (33333333330181/100000000000000 : ℝ), (33333333330181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208794847/500000000 : ℝ)|^39 ≤ (33333333330181/100000000000000 : ℝ)^31
        have hw : |(208794847/500000000 : ℝ)|=(208794847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208794847/500000000 : ℝ)|^39 ≤ (33333333330181/100000000000000 : ℝ)^31
        have hw : |(-208794847/500000000 : ℝ)|=(208794847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208794847/500000000 : ℝ)|^39 ≤ (33333333330181/100000000000000 : ℝ)^31
        have hw : |(208794847/500000000 : ℝ)|=(208794847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317084 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2062175327/5000000000 : ℝ)*X 0 0+(-99647299/200000000 : ℝ)*X 0 1+(676232651/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317084_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((676232651/2000000000 : ℝ)*X 1 0+(2062175327/5000000000 : ℝ)*X 1 1+(99647299/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317084_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((99647299/200000000 : ℝ)*X 2 0+(-676232651/2000000000 : ℝ)*X 2 1+(-2062175327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317084_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((208794847/500000000 : ℝ)*X 0 0+(-208794847/500000000 : ℝ)*X 0 1+(208794847/500000000 : ℝ)*X 0 2+(208794847/500000000 : ℝ)*X 1 0+(-208794847/500000000 : ℝ)*X 1 1+(208794847/500000000 : ℝ)*X 1 2+(208794847/500000000 : ℝ)*X 2 0+(-208794847/500000000 : ℝ)*X 2 1+(208794847/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317084_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-19104389588148640366071/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (19999999881/20000000000 : ℝ)*(base6) + (54600590543/100000000000 : ℝ)*(base40) + (54600590543/100000000000 : ℝ)*(base50) + (54600590543/100000000000 : ℝ)*(base60) + (89931/50000 : ℝ)*(major_s0_0) + (89931/50000 : ℝ)*(major_s0_1) + (89931/50000 : ℝ)*(major_s0_2) + (720146319109/250000000000 : ℝ)*(sp_s0_0) + (720146319109/250000000000 : ℝ)*(sp_s0_1) + (720146319109/250000000000 : ℝ)*(sp_s0_2) + (119/20000000000 : ℝ)*(sp_s0_6) + (720146319109/250000000000 : ℝ)*(f.sum) + (28428757/1250000000000000000000 : ℝ)*base62 + (42949443/500000000000000000000 : ℝ)*base64 + (13288039/250000000000000000000 : ℝ)*base67 + (13288039/250000000000000000000 : ℝ)*base69 + (28428757/1250000000000000000000 : ℝ)*base71 + (42949443/500000000000000000000 : ℝ)*base73 + (42949443/500000000000000000000 : ℝ)*base75 + (13288039/250000000000000000000 : ℝ)*base76 + (28428757/1250000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p017_b036 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 82 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=82 ∨ c=83 ∨ c=84 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c317082 p hpa (by linarith only [hpb]) X hX
  · exact collision_c317083 p hpa (by linarith only [hpb]) X hX
  · exact collision_c317084 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 82 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b036 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

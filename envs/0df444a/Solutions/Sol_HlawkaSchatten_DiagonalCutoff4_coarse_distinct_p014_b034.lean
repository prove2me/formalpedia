-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:41:07.9029+00:00
-- url     : https://prove2.me/submissions/ed34dbef-a5f3-4bfb-849a-b617a4d1d726

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314083_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314083_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314083_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314083 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c314083_s0 p hpa hpb X hX
  have h1 := collision_c314083_s1 p hpa hpb X hX h0
  exact collision_c314083_s2 p hpa hpb X hX h1

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
theorem collision_support_c314082_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3530333763/10000000000 : ℝ)*x 0 + (1551249351/5000000000 : ℝ)*x 1 + (366816711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3530333763/10000000000 : ℝ)^75 ≤ (13309432487513/50000000000000 : ℝ)^59 := by
    have hnat : (3530333763 : ℕ)^75*50000000000000^59 ≤ 13309432487513^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3530333763 10000000000 13309432487513 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551249351/5000000000 : ℝ)^75 ≤ (45175262459/200000000000 : ℝ)^59 := by
    have hnat : (1551249351 : ℕ)^75*200000000000^59 ≤ 45175262459^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551249351 5000000000 45175262459 200000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366816711/625000000 : ℝ)^75 ≤ (12698375943901/25000000000000 : ℝ)^59 := by
    have hnat : (366816711 : ℕ)^75*25000000000000^59 ≤ 12698375943901^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366816711 625000000 12698375943901 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3530333763/10000000000 : ℝ), (1551249351/5000000000 : ℝ), (366816711/625000000 : ℝ)] ![(13309432487513/50000000000000 : ℝ), (45175262459/200000000000 : ℝ), (12698375943901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3530333763/10000000000 : ℝ)|^75 ≤ (13309432487513/50000000000000 : ℝ)^59
        have hw : |(-3530333763/10000000000 : ℝ)|=(3530333763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551249351/5000000000 : ℝ)|^75 ≤ (45175262459/200000000000 : ℝ)^59
        have hw : |(1551249351/5000000000 : ℝ)|=(1551249351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(366816711/625000000 : ℝ)|^75 ≤ (12698375943901/25000000000000 : ℝ)^59
        have hw : |(366816711/625000000 : ℝ)|=(366816711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4249053809/10000000000 : ℝ)*x 0 + (-2791714697/10000000000 : ℝ)*x 1 + (1370163859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249053809/10000000000 : ℝ)^75 ≤ (4211144433427/12500000000000 : ℝ)^59 := by
    have hnat : (4249053809 : ℕ)^75*12500000000000^59 ≤ 4211144433427^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249053809 10000000000 4211144433427 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2791714697/10000000000 : ℝ)^75 ≤ (987572015537/5000000000000 : ℝ)^59 := by
    have hnat : (2791714697 : ℕ)^75*5000000000000^59 ≤ 987572015537^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791714697 10000000000 987572015537 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370163859/2500000000 : ℝ)^75 ≤ (46559404205933/100000000000000 : ℝ)^59 := by
    have hnat : (1370163859 : ℕ)^75*100000000000000^59 ≤ 46559404205933^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370163859 2500000000 46559404205933 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249053809/10000000000 : ℝ), (-2791714697/10000000000 : ℝ), (1370163859/2500000000 : ℝ)] ![(4211144433427/12500000000000 : ℝ), (987572015537/5000000000000 : ℝ), (46559404205933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249053809/10000000000 : ℝ)|^75 ≤ (4211144433427/12500000000000 : ℝ)^59
        have hw : |(4249053809/10000000000 : ℝ)|=(4249053809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2791714697/10000000000 : ℝ)|^75 ≤ (987572015537/5000000000000 : ℝ)^59
        have hw : |(-2791714697/10000000000 : ℝ)|=(2791714697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370163859/2500000000 : ℝ)|^75 ≤ (46559404205933/100000000000000 : ℝ)^59
        have hw : |(1370163859/2500000000 : ℝ)|=(1370163859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3055134167/10000000000 : ℝ)*x 0 + (730567473/5000000000 : ℝ)*x 1 + (3741731709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3055134167/10000000000 : ℝ)^75 ≤ (22150191417779/100000000000000 : ℝ)^59 := by
    have hnat : (3055134167 : ℕ)^75*100000000000000^59 ≤ 22150191417779^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3055134167 10000000000 22150191417779 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730567473/5000000000 : ℝ)^75 ≤ (8672926603031/100000000000000 : ℝ)^59 := by
    have hnat : (730567473 : ℕ)^75*100000000000000^59 ≤ 8672926603031^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730567473 5000000000 8672926603031 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3741731709/5000000000 : ℝ)^75 ≤ (69176881973207/100000000000000 : ℝ)^59 := by
    have hnat : (3741731709 : ℕ)^75*100000000000000^59 ≤ 69176881973207^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741731709 5000000000 69176881973207 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3055134167/10000000000 : ℝ), (730567473/5000000000 : ℝ), (3741731709/5000000000 : ℝ)] ![(22150191417779/100000000000000 : ℝ), (8672926603031/100000000000000 : ℝ), (69176881973207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3055134167/10000000000 : ℝ)|^75 ≤ (22150191417779/100000000000000 : ℝ)^59
        have hw : |(-3055134167/10000000000 : ℝ)|=(3055134167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(730567473/5000000000 : ℝ)|^75 ≤ (8672926603031/100000000000000 : ℝ)^59
        have hw : |(730567473/5000000000 : ℝ)|=(730567473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3741731709/5000000000 : ℝ)|^75 ≤ (69176881973207/100000000000000 : ℝ)^59
        have hw : |(3741731709/5000000000 : ℝ)|=(3741731709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2198255639/5000000000 : ℝ)*x 0 + (-112121797/2000000000 : ℝ)*x 1 + (6887536111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2198255639/5000000000 : ℝ)^75 ≤ (17591139662813/50000000000000 : ℝ)^59 := by
    have hnat : (2198255639 : ℕ)^75*50000000000000^59 ≤ 17591139662813^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198255639 5000000000 17591139662813 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112121797/2000000000 : ℝ)^75 ≤ (2566336660631/100000000000000 : ℝ)^59 := by
    have hnat : (112121797 : ℕ)^75*100000000000000^59 ≤ 2566336660631^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112121797 2000000000 2566336660631 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6887536111/10000000000 : ℝ)^75 ≤ (62251383992759/100000000000000 : ℝ)^59 := by
    have hnat : (6887536111 : ℕ)^75*100000000000000^59 ≤ 62251383992759^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6887536111 10000000000 62251383992759 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2198255639/5000000000 : ℝ), (-112121797/2000000000 : ℝ), (6887536111/10000000000 : ℝ)] ![(17591139662813/50000000000000 : ℝ), (2566336660631/100000000000000 : ℝ), (62251383992759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2198255639/5000000000 : ℝ)|^75 ≤ (17591139662813/50000000000000 : ℝ)^59
        have hw : |(2198255639/5000000000 : ℝ)|=(2198255639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112121797/2000000000 : ℝ)|^75 ≤ (2566336660631/100000000000000 : ℝ)^59
        have hw : |(-112121797/2000000000 : ℝ)|=(112121797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6887536111/10000000000 : ℝ)|^75 ≤ (62251383992759/100000000000000 : ℝ)^59
        have hw : |(6887536111/10000000000 : ℝ)|=(6887536111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1777026019/5000000000 : ℝ)*x 0 + (242856157/312500000 : ℝ)*x 1 + (-86503337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1777026019/5000000000 : ℝ)^75 ≤ (26846406637069/100000000000000 : ℝ)^59 := by
    have hnat : (1777026019 : ℕ)^75*100000000000000^59 ≤ 26846406637069^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777026019 5000000000 26846406637069 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242856157/312500000 : ℝ)^75 ≤ (36288911437761/50000000000000 : ℝ)^59 := by
    have hnat : (242856157 : ℕ)^75*50000000000000^59 ≤ 36288911437761^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242856157 312500000 36288911437761 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86503337/5000000000 : ℝ)^75 ≤ (575770479849/100000000000000 : ℝ)^59 := by
    have hnat : (86503337 : ℕ)^75*100000000000000^59 ≤ 575770479849^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86503337 5000000000 575770479849 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1777026019/5000000000 : ℝ), (242856157/312500000 : ℝ), (-86503337/5000000000 : ℝ)] ![(26846406637069/100000000000000 : ℝ), (36288911437761/50000000000000 : ℝ), (575770479849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1777026019/5000000000 : ℝ)|^75 ≤ (26846406637069/100000000000000 : ℝ)^59
        have hw : |(1777026019/5000000000 : ℝ)|=(1777026019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242856157/312500000 : ℝ)|^75 ≤ (36288911437761/50000000000000 : ℝ)^59
        have hw : |(242856157/312500000 : ℝ)|=(242856157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86503337/5000000000 : ℝ)|^75 ≤ (575770479849/100000000000000 : ℝ)^59
        have hw : |(-86503337/5000000000 : ℝ)|=(86503337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9861921/2500000000 : ℝ)*x 0 + (8556329761/10000000000 : ℝ)*x 1 + (1291353023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9861921/2500000000 : ℝ)^75 ≤ (10990188809/12500000000000 : ℝ)^59 := by
    have hnat : (9861921 : ℕ)^75*12500000000000^59 ≤ 10990188809^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9861921 2500000000 10990188809 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8556329761/10000000000 : ℝ)^75 ≤ (41010476009679/50000000000000 : ℝ)^59 := by
    have hnat : (8556329761 : ℕ)^75*50000000000000^59 ≤ 41010476009679^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8556329761 10000000000 41010476009679 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291353023/5000000000 : ℝ)^75 ≤ (17891126459039/100000000000000 : ℝ)^59 := by
    have hnat : (1291353023 : ℕ)^75*100000000000000^59 ≤ 17891126459039^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291353023 5000000000 17891126459039 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9861921/2500000000 : ℝ), (8556329761/10000000000 : ℝ), (1291353023/5000000000 : ℝ)] ![(10990188809/12500000000000 : ℝ), (41010476009679/50000000000000 : ℝ), (17891126459039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9861921/2500000000 : ℝ)|^75 ≤ (10990188809/12500000000000 : ℝ)^59
        have hw : |(9861921/2500000000 : ℝ)|=(9861921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8556329761/10000000000 : ℝ)|^75 ≤ (41010476009679/50000000000000 : ℝ)^59
        have hw : |(8556329761/10000000000 : ℝ)|=(8556329761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291353023/5000000000 : ℝ)|^75 ≤ (17891126459039/100000000000000 : ℝ)^59
        have hw : |(1291353023/5000000000 : ℝ)|=(1291353023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2659657097/10000000000 : ℝ)*x 0 + (347130833/2000000000 : ℝ)*x 1 + (3803581739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2659657097/10000000000 : ℝ)^75 ≤ (18571464922597/100000000000000 : ℝ)^59 := by
    have hnat : (2659657097 : ℕ)^75*100000000000000^59 ≤ 18571464922597^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659657097 10000000000 18571464922597 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347130833/2000000000 : ℝ)^75 ≤ (10794832939687/100000000000000 : ℝ)^59 := by
    have hnat : (347130833 : ℕ)^75*100000000000000^59 ≤ 10794832939687^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347130833 2000000000 10794832939687 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3803581739/5000000000 : ℝ)^75 ≤ (35316851060851/50000000000000 : ℝ)^59 := by
    have hnat : (3803581739 : ℕ)^75*50000000000000^59 ≤ 35316851060851^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3803581739 5000000000 35316851060851 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2659657097/10000000000 : ℝ), (347130833/2000000000 : ℝ), (3803581739/5000000000 : ℝ)] ![(18571464922597/100000000000000 : ℝ), (10794832939687/100000000000000 : ℝ), (35316851060851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2659657097/10000000000 : ℝ)|^75 ≤ (18571464922597/100000000000000 : ℝ)^59
        have hw : |(-2659657097/10000000000 : ℝ)|=(2659657097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(347130833/2000000000 : ℝ)|^75 ≤ (10794832939687/100000000000000 : ℝ)^59
        have hw : |(347130833/2000000000 : ℝ)|=(347130833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3803581739/5000000000 : ℝ)|^75 ≤ (35316851060851/50000000000000 : ℝ)^59
        have hw : |(3803581739/5000000000 : ℝ)|=(3803581739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3860063579/5000000000 : ℝ)*x 0 + (-93873461/500000000 : ℝ)*x 1 + (2377280181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3860063579/5000000000 : ℝ)^75 ≤ (35984853052761/50000000000000 : ℝ)^59 := by
    have hnat : (3860063579 : ℕ)^75*50000000000000^59 ≤ 35984853052761^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3860063579 5000000000 35984853052761 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93873461/500000000 : ℝ)^75 ≤ (596410979997/5000000000000 : ℝ)^59 := by
    have hnat : (93873461 : ℕ)^75*5000000000000^59 ≤ 596410979997^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93873461 500000000 596410979997 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2377280181/10000000000 : ℝ)^75 ≤ (201275928589/1250000000000 : ℝ)^59 := by
    have hnat : (2377280181 : ℕ)^75*1250000000000^59 ≤ 201275928589^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2377280181 10000000000 201275928589 1250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3860063579/5000000000 : ℝ), (-93873461/500000000 : ℝ), (2377280181/10000000000 : ℝ)] ![(35984853052761/50000000000000 : ℝ), (596410979997/5000000000000 : ℝ), (201275928589/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3860063579/5000000000 : ℝ)|^75 ≤ (35984853052761/50000000000000 : ℝ)^59
        have hw : |(3860063579/5000000000 : ℝ)|=(3860063579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93873461/500000000 : ℝ)|^75 ≤ (596410979997/5000000000000 : ℝ)^59
        have hw : |(-93873461/500000000 : ℝ)|=(93873461/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2377280181/10000000000 : ℝ)|^75 ≤ (201275928589/1250000000000 : ℝ)^59
        have hw : |(2377280181/10000000000 : ℝ)|=(2377280181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8477384423/10000000000 : ℝ)*x 0 + (642350599/2500000000 : ℝ)*x 1 + (-150675079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8477384423/10000000000 : ℝ)^75 ≤ (40530081378553/50000000000000 : ℝ)^59 := by
    have hnat : (8477384423 : ℕ)^75*50000000000000^59 ≤ 40530081378553^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8477384423 10000000000 40530081378553 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642350599/2500000000 : ℝ)^75 ≤ (17774058256553/100000000000000 : ℝ)^59 := by
    have hnat : (642350599 : ℕ)^75*100000000000000^59 ≤ 17774058256553^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642350599 2500000000 17774058256553 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150675079/5000000000 : ℝ)^75 ≤ (1165778969191/100000000000000 : ℝ)^59 := by
    have hnat : (150675079 : ℕ)^75*100000000000000^59 ≤ 1165778969191^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150675079 5000000000 1165778969191 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8477384423/10000000000 : ℝ), (642350599/2500000000 : ℝ), (-150675079/5000000000 : ℝ)] ![(40530081378553/50000000000000 : ℝ), (17774058256553/100000000000000 : ℝ), (1165778969191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8477384423/10000000000 : ℝ)|^75 ≤ (40530081378553/50000000000000 : ℝ)^59
        have hw : |(8477384423/10000000000 : ℝ)|=(8477384423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642350599/2500000000 : ℝ)|^75 ≤ (17774058256553/100000000000000 : ℝ)^59
        have hw : |(642350599/2500000000 : ℝ)|=(642350599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150675079/5000000000 : ℝ)|^75 ≤ (1165778969191/100000000000000 : ℝ)^59
        have hw : |(-150675079/5000000000 : ℝ)|=(150675079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19479/10000000000 : ℝ)*x 0 + (953486719/2500000000 : ℝ)*x 1 + (3803581739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19479/10000000000 : ℝ)^75 ≤ (1101551/20000000000000 : ℝ)^59 := by
    have hnat : (19479 : ℕ)^75*20000000000000^59 ≤ 1101551^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19479 10000000000 1101551 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953486719/2500000000 : ℝ)^75 ≤ (5873258470351/20000000000000 : ℝ)^59 := by
    have hnat : (953486719 : ℕ)^75*20000000000000^59 ≤ 5873258470351^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953486719 2500000000 5873258470351 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3803581739/5000000000 : ℝ)^75 ≤ (35316851060851/50000000000000 : ℝ)^59 := by
    have hnat : (3803581739 : ℕ)^75*50000000000000^59 ≤ 35316851060851^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3803581739 5000000000 35316851060851 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19479/10000000000 : ℝ), (953486719/2500000000 : ℝ), (3803581739/5000000000 : ℝ)] ![(1101551/20000000000000 : ℝ), (5873258470351/20000000000000 : ℝ), (35316851060851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19479/10000000000 : ℝ)|^75 ≤ (1101551/20000000000000 : ℝ)^59
        have hw : |(-19479/10000000000 : ℝ)|=(19479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(953486719/2500000000 : ℝ)|^75 ≤ (5873258470351/20000000000000 : ℝ)^59
        have hw : |(953486719/2500000000 : ℝ)|=(953486719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3803581739/5000000000 : ℝ)|^75 ≤ (35316851060851/50000000000000 : ℝ)^59
        have hw : |(3803581739/5000000000 : ℝ)|=(3803581739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5871108417/10000000000 : ℝ)*x 0 + (130295561/500000000 : ℝ)*x 1 + (3988808813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5871108417/10000000000 : ℝ)^75 ≤ (5081595916207/10000000000000 : ℝ)^59 := by
    have hnat : (5871108417 : ℕ)^75*10000000000000^59 ≤ 5081595916207^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5871108417 10000000000 5081595916207 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130295561/500000000 : ℝ)^75 ≤ (9047858231163/50000000000000 : ℝ)^59 := by
    have hnat : (130295561 : ℕ)^75*50000000000000^59 ≤ 9047858231163^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130295561 500000000 9047858231163 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3988808813/10000000000 : ℝ)^75 ≤ (7772081089369/25000000000000 : ℝ)^59 := by
    have hnat : (3988808813 : ℕ)^75*25000000000000^59 ≤ 7772081089369^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3988808813 10000000000 7772081089369 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5871108417/10000000000 : ℝ), (130295561/500000000 : ℝ), (3988808813/10000000000 : ℝ)] ![(5081595916207/10000000000000 : ℝ), (9047858231163/50000000000000 : ℝ), (7772081089369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5871108417/10000000000 : ℝ)|^75 ≤ (5081595916207/10000000000000 : ℝ)^59
        have hw : |(-5871108417/10000000000 : ℝ)|=(5871108417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130295561/500000000 : ℝ)|^75 ≤ (9047858231163/50000000000000 : ℝ)^59
        have hw : |(130295561/500000000 : ℝ)|=(130295561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3988808813/10000000000 : ℝ)|^75 ≤ (7772081089369/25000000000000 : ℝ)^59
        have hw : |(3988808813/10000000000 : ℝ)|=(3988808813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (127635931/312500000 : ℝ)*x 0 + (-1296247749/5000000000 : ℝ)*x 1 + (5795421049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127635931/312500000 : ℝ)^75 ≤ (32037951535841/100000000000000 : ℝ)^59 := by
    have hnat : (127635931 : ℕ)^75*100000000000000^59 ≤ 32037951535841^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127635931 312500000 32037951535841 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296247749/5000000000 : ℝ)^75 ≤ (3595475060601/20000000000000 : ℝ)^59 := by
    have hnat : (1296247749 : ℕ)^75*20000000000000^59 ≤ 3595475060601^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296247749 5000000000 3595475060601 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5795421049/10000000000 : ℝ)^75 ≤ (49984673143431/100000000000000 : ℝ)^59 := by
    have hnat : (5795421049 : ℕ)^75*100000000000000^59 ≤ 49984673143431^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5795421049 10000000000 49984673143431 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127635931/312500000 : ℝ), (-1296247749/5000000000 : ℝ), (5795421049/10000000000 : ℝ)] ![(32037951535841/100000000000000 : ℝ), (3595475060601/20000000000000 : ℝ), (49984673143431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127635931/312500000 : ℝ)|^75 ≤ (32037951535841/100000000000000 : ℝ)^59
        have hw : |(127635931/312500000 : ℝ)|=(127635931/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1296247749/5000000000 : ℝ)|^75 ≤ (3595475060601/20000000000000 : ℝ)^59
        have hw : |(-1296247749/5000000000 : ℝ)|=(1296247749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5795421049/10000000000 : ℝ)|^75 ≤ (49984673143431/100000000000000 : ℝ)^59
        have hw : |(5795421049/10000000000 : ℝ)|=(5795421049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8006975997/10000000000 : ℝ)*x 0 + (1620808477/5000000000 : ℝ)*x 1 + (-208776723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8006975997/10000000000 : ℝ)^75 ≤ (18846491310583/25000000000000 : ℝ)^59 := by
    have hnat : (8006975997 : ℕ)^75*25000000000000^59 ≤ 18846491310583^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8006975997 10000000000 18846491310583 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1620808477/5000000000 : ℝ)^75 ≤ (2388289121943/10000000000000 : ℝ)^59 := by
    have hnat : (1620808477 : ℕ)^75*10000000000000^59 ≤ 2388289121943^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620808477 5000000000 2388289121943 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208776723/10000000000 : ℝ)^75 ≤ (731143527391/100000000000000 : ℝ)^59 := by
    have hnat : (208776723 : ℕ)^75*100000000000000^59 ≤ 731143527391^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208776723 10000000000 731143527391 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8006975997/10000000000 : ℝ), (1620808477/5000000000 : ℝ), (-208776723/10000000000 : ℝ)] ![(18846491310583/25000000000000 : ℝ), (2388289121943/10000000000000 : ℝ), (731143527391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8006975997/10000000000 : ℝ)|^75 ≤ (18846491310583/25000000000000 : ℝ)^59
        have hw : |(8006975997/10000000000 : ℝ)|=(8006975997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1620808477/5000000000 : ℝ)|^75 ≤ (2388289121943/10000000000000 : ℝ)^59
        have hw : |(1620808477/5000000000 : ℝ)|=(1620808477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208776723/10000000000 : ℝ)|^75 ≤ (731143527391/100000000000000 : ℝ)^59
        have hw : |(-208776723/10000000000 : ℝ)|=(208776723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s0_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-45620801/10000000000 : ℝ)*x 0 + (3725937543/5000000000 : ℝ)*x 1 + (3988808813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45620801/10000000000 : ℝ)^75 ≤ (105769299141/100000000000000 : ℝ)^59 := by
    have hnat : (45620801 : ℕ)^75*100000000000000^59 ≤ 105769299141^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45620801 10000000000 105769299141 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3725937543/5000000000 : ℝ)^75 ≤ (3440295316633/5000000000000 : ℝ)^59 := by
    have hnat : (3725937543 : ℕ)^75*5000000000000^59 ≤ 3440295316633^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3725937543 5000000000 3440295316633 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3988808813/10000000000 : ℝ)^75 ≤ (7772081089369/25000000000000 : ℝ)^59 := by
    have hnat : (3988808813 : ℕ)^75*25000000000000^59 ≤ 7772081089369^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3988808813 10000000000 7772081089369 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45620801/10000000000 : ℝ), (3725937543/5000000000 : ℝ), (3988808813/10000000000 : ℝ)] ![(105769299141/100000000000000 : ℝ), (3440295316633/5000000000000 : ℝ), (7772081089369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45620801/10000000000 : ℝ)|^75 ≤ (105769299141/100000000000000 : ℝ)^59
        have hw : |(-45620801/10000000000 : ℝ)|=(45620801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3725937543/5000000000 : ℝ)|^75 ≤ (3440295316633/5000000000000 : ℝ)^59
        have hw : |(3725937543/5000000000 : ℝ)|=(3725937543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3988808813/10000000000 : ℝ)|^75 ≤ (7772081089369/25000000000000 : ℝ)^59
        have hw : |(3988808813/10000000000 : ℝ)|=(3988808813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-981519033/2500000000 : ℝ)*x 0 + (1656562201/5000000000 : ℝ)*x 1 + (2666805129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981519033/2500000000 : ℝ)^75 ≤ (15234065934093/50000000000000 : ℝ)^59 := by
    have hnat : (981519033 : ℕ)^75*50000000000000^59 ≤ 15234065934093^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981519033 2500000000 15234065934093 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1656562201/5000000000 : ℝ)^75 ≤ (24554592119321/100000000000000 : ℝ)^59 := by
    have hnat : (1656562201 : ℕ)^75*100000000000000^59 ≤ 24554592119321^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656562201 5000000000 24554592119321 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2666805129/5000000000 : ℝ)^75 ≤ (44977275989477/100000000000000 : ℝ)^59 := by
    have hnat : (2666805129 : ℕ)^75*100000000000000^59 ≤ 44977275989477^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666805129 5000000000 44977275989477 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981519033/2500000000 : ℝ), (1656562201/5000000000 : ℝ), (2666805129/5000000000 : ℝ)] ![(15234065934093/50000000000000 : ℝ), (24554592119321/100000000000000 : ℝ), (44977275989477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981519033/2500000000 : ℝ)|^75 ≤ (15234065934093/50000000000000 : ℝ)^59
        have hw : |(-981519033/2500000000 : ℝ)|=(981519033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1656562201/5000000000 : ℝ)|^75 ≤ (24554592119321/100000000000000 : ℝ)^59
        have hw : |(1656562201/5000000000 : ℝ)|=(1656562201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2666805129/5000000000 : ℝ)|^75 ≤ (44977275989477/100000000000000 : ℝ)^59
        have hw : |(2666805129/5000000000 : ℝ)|=(2666805129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4178134707/10000000000 : ℝ)*x 0 + (-335980233/1000000000 : ℝ)*x 1 + (5056581679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4178134707/10000000000 : ℝ)^75 ≤ (4122000378577/12500000000000 : ℝ)^59 := by
    have hnat : (4178134707 : ℕ)^75*12500000000000^59 ≤ 4122000378577^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178134707 10000000000 4122000378577 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335980233/1000000000 : ℝ)^75 ≤ (24995189434533/100000000000000 : ℝ)^59 := by
    have hnat : (335980233 : ℕ)^75*100000000000000^59 ≤ 24995189434533^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335980233 1000000000 24995189434533 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5056581679/10000000000 : ℝ)^75 ≤ (42028807518297/100000000000000 : ℝ)^59 := by
    have hnat : (5056581679 : ℕ)^75*100000000000000^59 ≤ 42028807518297^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056581679 10000000000 42028807518297 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4178134707/10000000000 : ℝ), (-335980233/1000000000 : ℝ), (5056581679/10000000000 : ℝ)] ![(4122000378577/12500000000000 : ℝ), (24995189434533/100000000000000 : ℝ), (42028807518297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4178134707/10000000000 : ℝ)|^75 ≤ (4122000378577/12500000000000 : ℝ)^59
        have hw : |(4178134707/10000000000 : ℝ)|=(4178134707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-335980233/1000000000 : ℝ)|^75 ≤ (24995189434533/100000000000000 : ℝ)^59
        have hw : |(-335980233/1000000000 : ℝ)|=(335980233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5056581679/10000000000 : ℝ)|^75 ≤ (42028807518297/100000000000000 : ℝ)^59
        have hw : |(5056581679/10000000000 : ℝ)|=(5056581679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1392948579/2500000000 : ℝ)*x 0 + (210980599/400000000 : ℝ)*x 1 + (-346480599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1392948579/2500000000 : ℝ)^75 ≤ (47545824690363/100000000000000 : ℝ)^59 := by
    have hnat : (1392948579 : ℕ)^75*100000000000000^59 ≤ 47545824690363^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392948579 2500000000 47545824690363 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210980599/400000000 : ℝ)^75 ≤ (22172374382591/50000000000000 : ℝ)^59 := by
    have hnat : (210980599 : ℕ)^75*50000000000000^59 ≤ 22172374382591^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210980599 400000000 22172374382591 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346480599/2500000000 : ℝ)^75 ≤ (4054713264497/50000000000000 : ℝ)^59 := by
    have hnat : (346480599 : ℕ)^75*50000000000000^59 ≤ 4054713264497^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346480599 2500000000 4054713264497 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1392948579/2500000000 : ℝ), (210980599/400000000 : ℝ), (-346480599/2500000000 : ℝ)] ![(47545824690363/100000000000000 : ℝ), (22172374382591/50000000000000 : ℝ), (4054713264497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1392948579/2500000000 : ℝ)|^75 ≤ (47545824690363/100000000000000 : ℝ)^59
        have hw : |(1392948579/2500000000 : ℝ)|=(1392948579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210980599/400000000 : ℝ)|^75 ≤ (22172374382591/50000000000000 : ℝ)^59
        have hw : |(210980599/400000000 : ℝ)|=(210980599/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-346480599/2500000000 : ℝ)|^75 ≤ (4054713264497/50000000000000 : ℝ)^59
        have hw : |(-346480599/2500000000 : ℝ)|=(346480599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314082_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3434639/31250000 : ℝ)*x 0 + (530986097/1000000000 : ℝ)*x 1 + (1145442803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3434639/31250000 : ℝ)^75 ≤ (6039092836591/100000000000000 : ℝ)^59 := by
    have hnat : (3434639 : ℕ)^75*100000000000000^59 ≤ 6039092836591^59*31250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3434639 31250000 6039092836591 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530986097/1000000000 : ℝ)^75 ≤ (44722845506297/100000000000000 : ℝ)^59 := by
    have hnat : (530986097 : ℕ)^75*100000000000000^59 ≤ 44722845506297^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530986097 1000000000 44722845506297 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145442803/2000000000 : ℝ)^75 ≤ (12309515409789/25000000000000 : ℝ)^59 := by
    have hnat : (1145442803 : ℕ)^75*25000000000000^59 ≤ 12309515409789^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145442803 2000000000 12309515409789 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3434639/31250000 : ℝ), (530986097/1000000000 : ℝ), (1145442803/2000000000 : ℝ)] ![(6039092836591/100000000000000 : ℝ), (44722845506297/100000000000000 : ℝ), (12309515409789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3434639/31250000 : ℝ)|^75 ≤ (6039092836591/100000000000000 : ℝ)^59
        have hw : |(3434639/31250000 : ℝ)|=(3434639/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530986097/1000000000 : ℝ)|^75 ≤ (44722845506297/100000000000000 : ℝ)^59
        have hw : |(530986097/1000000000 : ℝ)|=(530986097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1145442803/2000000000 : ℝ)|^75 ≤ (12309515409789/25000000000000 : ℝ)^59
        have hw : |(1145442803/2000000000 : ℝ)|=(1145442803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314082 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3530333763/10000000000 : ℝ)*X 0 0+(1551249351/5000000000 : ℝ)*X 0 1+(366816711/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4249053809/10000000000 : ℝ)*X 1 0+(-2791714697/10000000000 : ℝ)*X 1 1+(1370163859/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3055134167/10000000000 : ℝ)*X 0 0+(730567473/5000000000 : ℝ)*X 0 1+(3741731709/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2198255639/5000000000 : ℝ)*X 1 0+(-112121797/2000000000 : ℝ)*X 1 1+(6887536111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1777026019/5000000000 : ℝ)*X 2 0+(242856157/312500000 : ℝ)*X 2 1+(-86503337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((9861921/2500000000 : ℝ)*X 0 0+(8556329761/10000000000 : ℝ)*X 0 1+(1291353023/5000000000 : ℝ)*X 0 2+(9861921/2500000000 : ℝ)*X 1 0+(8556329761/10000000000 : ℝ)*X 1 1+(1291353023/5000000000 : ℝ)*X 1 2+(9861921/2500000000 : ℝ)*X 2 0+(8556329761/10000000000 : ℝ)*X 2 1+(1291353023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2659657097/10000000000 : ℝ)*X 0 0+(347130833/2000000000 : ℝ)*X 0 1+(3803581739/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3860063579/5000000000 : ℝ)*X 1 0+(-93873461/500000000 : ℝ)*X 1 1+(2377280181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8477384423/10000000000 : ℝ)*X 2 0+(642350599/2500000000 : ℝ)*X 2 1+(-150675079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-19479/10000000000 : ℝ)*X 0 0+(953486719/2500000000 : ℝ)*X 0 1+(3803581739/5000000000 : ℝ)*X 0 2+(-19479/10000000000 : ℝ)*X 1 0+(953486719/2500000000 : ℝ)*X 1 1+(3803581739/5000000000 : ℝ)*X 1 2+(-19479/10000000000 : ℝ)*X 2 0+(953486719/2500000000 : ℝ)*X 2 1+(3803581739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5871108417/10000000000 : ℝ)*X 0 0+(130295561/500000000 : ℝ)*X 0 1+(3988808813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((127635931/312500000 : ℝ)*X 1 0+(-1296247749/5000000000 : ℝ)*X 1 1+(5795421049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8006975997/10000000000 : ℝ)*X 2 0+(1620808477/5000000000 : ℝ)*X 2 1+(-208776723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-45620801/10000000000 : ℝ)*X 0 0+(3725937543/5000000000 : ℝ)*X 0 1+(3988808813/10000000000 : ℝ)*X 0 2+(-45620801/10000000000 : ℝ)*X 1 0+(3725937543/5000000000 : ℝ)*X 1 1+(3988808813/10000000000 : ℝ)*X 1 2+(-45620801/10000000000 : ℝ)*X 2 0+(3725937543/5000000000 : ℝ)*X 2 1+(3988808813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((69993/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69993/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15030452316087981226719/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204019300219/250000000000 : ℝ)*(base7) + (61319159353/1000000000000 : ℝ)*(base49) + (277581348427/1000000000000 : ℝ)*(base53) + (30726708767/20000000000 : ℝ)*(major_s0_0) + (30726708767/20000000000 : ℝ)*(major_s0_1) + (1258754089923/1000000000000 : ℝ)*(major_s0_2) + (996027/250000000000 : ℝ)*(sp_s0_0) + (356037953157/250000000000 : ℝ)*(sp_s0_7) + (712091390269/500000000000 : ℝ)*(sp_s0_8) + (1701768076073/1000000000000 : ℝ)*(sp_s0_9) + (106808492173/62500000000 : ℝ)*(sp_s0_13) + (3093091/100000000000 : ℝ)*(sp_s0_14) + (986777/250000000000 : ℝ)*(sp_s0_22) + (142197/100000000000 : ℝ)*(sp_s0_27) + (892860095863/1000000000000 : ℝ)*(f.failure) + (1701768076073/1000000000000 : ℝ)*(f.sum) + (46375772099417/80000000000000000000000000 : ℝ)*base63 + (4070405428121927/10000000000000000000000000000 : ℝ)*base65 + (2243951280321/8000000000000000000000000 : ℝ)*base67 + (54048632733149/400000000000000000000000000 : ℝ)*base68 + (4450941326523177/10000000000000000000000000000 : ℝ)*base71 + (52964727424883/200000000000000000000000000 : ℝ)*base73 + (106733691295117/200000000000000000000000000 : ℝ)*base75 + (2680799608321/8000000000000000000000000 : ℝ)*base77 + (10790238568227/50000000000000000000000000 : ℝ)*base79 + (50547/100000000000000000 : ℝ)*base87 + (50547/100000000000000000 : ℝ)*base89 + (50547/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((40417/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(40417/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (69712301012597673547539/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83559075031/1000000000000 : ℝ)*(base1) + (70004119877/62500000000 : ℝ)*(base7) + (2767474559/62500000000 : ℝ)*(base39) + (4246329/500000000000 : ℝ)*(base53) + (44209980809/1000000000000 : ℝ)*(base60) + (1798653992479/1000000000000 : ℝ)*(major_s0_0) + (1798653992479/1000000000000 : ℝ)*(major_s0_1) + (1798645499821/1000000000000 : ℝ)*(major_s0_2) + (98193887/1000000000000 : ℝ)*(sp_s0_7) + (989666893231/500000000000 : ℝ)*(sp_s0_14) + (947936452659/500000000000 : ℝ)*(sp_s0_15) + (1895830203677/1000000000000 : ℝ)*(sp_s0_16) + (2081816569029/1000000000000 : ℝ)*(sp_s0_20) + (51194299/1000000000000 : ℝ)*(sp_s0_23) + (261327431507/250000000000 : ℝ)*(f.failure) + (236985174747/125000000000 : ℝ)*(f.sum) + (2412877162607177/5000000000000000000000000000 : ℝ)*base63 + (2094213411025129/10000000000000000000000000000 : ℝ)*base65 + (85563494109823/400000000000000000000000000 : ℝ)*base66 + (203324823515277/400000000000000000000000000 : ℝ)*base69 + (1666155407139777/5000000000000000000000000000 : ℝ)*base71 + (3228774970332429/10000000000000000000000000000 : ℝ)*base72 + (537900967332429/10000000000000000000000000000 : ℝ)*base75 + (27306505229823/400000000000000000000000000 : ℝ)*base76 + (422910789519501/2500000000000000000000000000 : ℝ)*base78 + (2983/25000000000000000 : ℝ)*base87 + (2983/25000000000000000 : ℝ)*base89 + (2983/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(73819/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(73819/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20245717084379937439083/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28972347387/200000000000 : ℝ)*(base1) + (909781749797/1000000000000 : ℝ)*(base7) + (38393015537/1000000000000 : ℝ)*(base39) + (60175141323/100000000000 : ℝ)*(base44) + (512316323693/250000000000 : ℝ)*(major_s0_0) + (723756940771/500000000000 : ℝ)*(major_s0_1) + (512316323693/250000000000 : ℝ)*(major_s0_2) + (117121551/1000000000000 : ℝ)*(sp_s0_1) + (7256737/500000000000 : ℝ)*(sp_s0_13) + (1732727/200000000000 : ℝ)*(sp_s0_16) + (503900425957/200000000000 : ℝ)*(sp_s0_21) + (1772771858069/1000000000000 : ℝ)*(sp_s0_22) + (474926345843/200000000000 : ℝ)*(sp_s0_23) + (677054815011/500000000000 : ℝ)*(sp_s0_27) + (148869442983/125000000000 : ℝ)*(f.failure) + (47492807857/20000000000 : ℝ)*(f.sum) + (784614579269629/5000000000000000000000000000 : ℝ)*base62 + (151590630619657/2500000000000000000000000000 : ℝ)*base65 + (58612123444573/200000000000000000000000000 : ℝ)*base67 + (27970450089341/100000000000000000000000000 : ℝ)*base69 + (50525148653467/625000000000000000000000000 : ℝ)*base70 + (1079984630369657/2500000000000000000000000000 : ℝ)*base73 + (1252299763263321/5000000000000000000000000000 : ℝ)*base75 + (3686268140659/100000000000000000000000000 : ℝ)*base77 + (545374990353639/5000000000000000000000000000 : ℝ)*base79 + (8173/12500000000000000 : ℝ)*base86 + (8173/12500000000000000 : ℝ)*base88 + (8173/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (69993/100000 : ℝ) ^ (37/8 : ℝ) ≤ (600105470135577603/3125000000000000000 : ℝ) := by
    have hpowers : (69993/100000 : ℝ)^37 ≤ (600105470135577603/3125000000000000000 : ℝ)^8 := by
      have hnat : (69993 : ℕ)^37*3125000000000000000^8 ≤ 600105470135577603^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69993 100000 600105470135577603 3125000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69993/100000 : ℝ)) (X := (600105470135577603/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3725105470135577603/3125000000000000000 : ℝ) ≤ (10387112180955653/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3725105470135577603/3125000000000000000 : ℝ)^8 ≤ (10387112180955653/10000000000000000 : ℝ)^37 := by
      have hnat : (3725105470135577603 : ℕ)^8*10000000000000000^37 ≤ 10387112180955653^37*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3725105470135577603 3125000000000000000 10387112180955653 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10387112180955653/10000000000000000 : ℝ)) (X := (3725105470135577603/3125000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2162605470135577603/1562500000000000000 : ℝ) ≤ (5364021320656193/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2162605470135577603/1562500000000000000 : ℝ)^8 ≤ (5364021320656193/5000000000000000 : ℝ)^37 := by
      have hnat : (2162605470135577603 : ℕ)^8*5000000000000000^37 ≤ 5364021320656193^37*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2162605470135577603 1562500000000000000 5364021320656193 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5364021320656193/5000000000000000 : ℝ)) (X := (2162605470135577603/1562500000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(387112180955653/6999300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(340930460356733/6999300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (69993/100000 : ℝ)) (alpha := (387112180955653/6999300000000000 : ℝ)) (beta := (340930460356733/6999300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (69993/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(387112180955653/6999300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(340930460356733/6999300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (40417/50000 : ℝ) ^ (37/8 : ℝ) ≤ (37378560648928352747/100000000000000000000 : ℝ) := by
    have hpowers : (40417/50000 : ℝ)^37 ≤ (37378560648928352747/100000000000000000000 : ℝ)^8 := by
      have hnat : (40417 : ℕ)^37*100000000000000000000^8 ≤ 37378560648928352747^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40417 50000 37378560648928352747 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40417/50000 : ℝ)) (X := (37378560648928352747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (137378560648928352747/100000000000000000000 : ℝ) ≤ (2677690172970769/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (137378560648928352747/100000000000000000000 : ℝ)^8 ≤ (2677690172970769/2500000000000000 : ℝ)^37 := by
      have hnat : (137378560648928352747 : ℕ)^8*2500000000000000^37 ≤ 2677690172970769^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        137378560648928352747 100000000000000000000 2677690172970769 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2677690172970769/2500000000000000 : ℝ)) (X := (137378560648928352747/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (87378560648928352747/50000000000000000000 : ℝ) ≤ (2256567601807679/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (87378560648928352747/50000000000000000000 : ℝ)^8 ≤ (2256567601807679/2000000000000000 : ℝ)^37 := by
      have hnat : (87378560648928352747 : ℕ)^8*2000000000000000^37 ≤ 2256567601807679^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87378560648928352747 50000000000000000000 2256567601807679 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2256567601807679/2000000000000000 : ℝ)) (X := (87378560648928352747/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(177690172970769/2020850000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(572077317155319/8083400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (40417/50000 : ℝ)) (alpha := (177690172970769/2020850000000000 : ℝ)) (beta := (572077317155319/8083400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (40417/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(177690172970769/2020850000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(572077317155319/8083400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (73819/100000 : ℝ) ^ (37/8 : ℝ) ≤ (24562791920910736003/100000000000000000000 : ℝ) := by
    have hpowers : (73819/100000 : ℝ)^37 ≤ (24562791920910736003/100000000000000000000 : ℝ)^8 := by
      have hnat : (73819 : ℕ)^37*100000000000000000000^8 ≤ 24562791920910736003^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73819 100000 24562791920910736003 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73819/100000 : ℝ)) (X := (24562791920910736003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (124562791920910736003/100000000000000000000 : ℝ) ≤ (655397109920311/625000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (124562791920910736003/100000000000000000000 : ℝ)^8 ≤ (655397109920311/625000000000000 : ℝ)^37 := by
      have hnat : (124562791920910736003 : ℕ)^8*625000000000000^37 ≤ 655397109920311^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        124562791920910736003 100000000000000000000 655397109920311 625000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655397109920311/625000000000000 : ℝ)) (X := (124562791920910736003/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (74562791920910736003/50000000000000000000 : ℝ) ≤ (5451233624161263/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (74562791920910736003/50000000000000000000 : ℝ)^8 ≤ (5451233624161263/5000000000000000 : ℝ)^37 := by
      have hnat : (74562791920910736003 : ℕ)^8*5000000000000000^37 ≤ 5451233624161263^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74562791920910736003 50000000000000000000 5451233624161263 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5451233624161263/5000000000000000 : ℝ)) (X := (74562791920910736003/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(30397109920311/461368750000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(8322269791951/147638000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (73819/100000 : ℝ)) (alpha := (30397109920311/461368750000000 : ℝ)) (beta := (8322269791951/147638000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (73819/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(30397109920311/461368750000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(8322269791951/147638000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-981519033/2500000000 : ℝ)*X 0 0+(1656562201/5000000000 : ℝ)*X 0 1+(2666805129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4178134707/10000000000 : ℝ)*X 1 0+(-335980233/1000000000 : ℝ)*X 1 1+(5056581679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1392948579/2500000000 : ℝ)*X 2 0+(210980599/400000000 : ℝ)*X 2 1+(-346480599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3434639/31250000 : ℝ)*X 0 0+(530986097/1000000000 : ℝ)*X 0 1+(1145442803/2000000000 : ℝ)*X 0 2+(3434639/31250000 : ℝ)*X 1 0+(530986097/1000000000 : ℝ)*X 1 1+(1145442803/2000000000 : ℝ)*X 1 2+(3434639/31250000 : ℝ)*X 2 0+(530986097/1000000000 : ℝ)*X 2 1+(1145442803/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314082_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-218037071806535412371699050088931/29835425230000000000000000000000 : ℝ) := by norm_num
    linear_combination (2457/500000000000 : ℝ)*(base7) + (3907/250000000000 : ℝ)*(base15) + (6119/1000000000000 : ℝ)*(base31) + (65858680541/500000000000 : ℝ)*(base49) + (119905478627/250000000000 : ℝ)*(base60) + (430172500381/250000000000 : ℝ)*(major_s1_0) + (172069/100000 : ℝ)*(major_s1_1) + (172069/100000 : ℝ)*(major_s1_2) + (2435997579259/1000000000000 : ℝ)*(sp_s1_0) + (243599756569/100000000000 : ℝ)*(sp_s1_1) + (1217998790141/500000000000 : ℝ)*(sp_s1_2) + (199999999759/200000000000 : ℝ)*(sp_s1_6) + (1217998789379/500000000000 : ℝ)*(f.sum) + (3730891027119748553881/7458856307500000000000000000000 : ℝ)*base63 + (43149521163623/184547500000000000000000000 : ℝ)*base64 + (22038553458501/404170000000000000000000000 : ℝ)*base67 + (15798726158183/73819000000000000000000000 : ℝ)*base69 + (186295104054613397/2018286432421875000000000000000 : ℝ)*base70 + (3624921985621729229/3499650000000000000000000000 : ℝ)*base72 + (19082034799637/50521250000000000000000000 : ℝ)*base75 + (544510466050543/1749825000000000000000000000 : ℝ)*base77 + (21950405675059740217/141445354050000000000000000000000 : ℝ)*base79 + (501/1000000000000 : ℝ)*base81 + (1/390625000 : ℝ)*base83 + (381/250000000000 : ℝ)*base85 + (381/250000000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c314084_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2078427193/5000000000 : ℝ)*x 0 + (-5063323769/10000000000 : ℝ)*x 1 + (3374819929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078427193/5000000000 : ℝ)^75 ≤ (16381324069993/50000000000000 : ℝ)^59 := by
    have hnat : (2078427193 : ℕ)^75*50000000000000^59 ≤ 16381324069993^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078427193 5000000000 16381324069993 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5063323769/10000000000 : ℝ)^75 ≤ (42100055459979/100000000000000 : ℝ)^59 := by
    have hnat : (5063323769 : ℕ)^75*100000000000000^59 ≤ 42100055459979^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5063323769 10000000000 42100055459979 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3374819929/10000000000 : ℝ)^75 ≤ (6284324095461/25000000000000 : ℝ)^59 := by
    have hnat : (3374819929 : ℕ)^75*25000000000000^59 ≤ 6284324095461^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374819929 10000000000 6284324095461 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2078427193/5000000000 : ℝ), (-5063323769/10000000000 : ℝ), (3374819929/10000000000 : ℝ)] ![(16381324069993/50000000000000 : ℝ), (42100055459979/100000000000000 : ℝ), (6284324095461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2078427193/5000000000 : ℝ)|^75 ≤ (16381324069993/50000000000000 : ℝ)^59
        have hw : |(-2078427193/5000000000 : ℝ)|=(2078427193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5063323769/10000000000 : ℝ)|^75 ≤ (42100055459979/100000000000000 : ℝ)^59
        have hw : |(-5063323769/10000000000 : ℝ)|=(5063323769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3374819929/10000000000 : ℝ)|^75 ≤ (6284324095461/25000000000000 : ℝ)^59
        have hw : |(3374819929/10000000000 : ℝ)|=(3374819929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314084_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3374819929/10000000000 : ℝ)*x 0 + (2078427193/5000000000 : ℝ)*x 1 + (5063323769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3374819929/10000000000 : ℝ)^75 ≤ (6284324095461/25000000000000 : ℝ)^59 := by
    have hnat : (3374819929 : ℕ)^75*25000000000000^59 ≤ 6284324095461^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374819929 10000000000 6284324095461 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078427193/5000000000 : ℝ)^75 ≤ (16381324069993/50000000000000 : ℝ)^59 := by
    have hnat : (2078427193 : ℕ)^75*50000000000000^59 ≤ 16381324069993^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078427193 5000000000 16381324069993 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5063323769/10000000000 : ℝ)^75 ≤ (42100055459979/100000000000000 : ℝ)^59 := by
    have hnat : (5063323769 : ℕ)^75*100000000000000^59 ≤ 42100055459979^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5063323769 10000000000 42100055459979 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3374819929/10000000000 : ℝ), (2078427193/5000000000 : ℝ), (5063323769/10000000000 : ℝ)] ![(6284324095461/25000000000000 : ℝ), (16381324069993/50000000000000 : ℝ), (42100055459979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3374819929/10000000000 : ℝ)|^75 ≤ (6284324095461/25000000000000 : ℝ)^59
        have hw : |(3374819929/10000000000 : ℝ)|=(3374819929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2078427193/5000000000 : ℝ)|^75 ≤ (16381324069993/50000000000000 : ℝ)^59
        have hw : |(2078427193/5000000000 : ℝ)|=(2078427193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5063323769/10000000000 : ℝ)|^75 ≤ (42100055459979/100000000000000 : ℝ)^59
        have hw : |(5063323769/10000000000 : ℝ)|=(5063323769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314084_s0_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5063323769/10000000000 : ℝ)*x 0 + (-3374819929/10000000000 : ℝ)*x 1 + (-2078427193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5063323769/10000000000 : ℝ)^75 ≤ (42100055459979/100000000000000 : ℝ)^59 := by
    have hnat : (5063323769 : ℕ)^75*100000000000000^59 ≤ 42100055459979^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5063323769 10000000000 42100055459979 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3374819929/10000000000 : ℝ)^75 ≤ (6284324095461/25000000000000 : ℝ)^59 := by
    have hnat : (3374819929 : ℕ)^75*25000000000000^59 ≤ 6284324095461^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374819929 10000000000 6284324095461 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078427193/5000000000 : ℝ)^75 ≤ (16381324069993/50000000000000 : ℝ)^59 := by
    have hnat : (2078427193 : ℕ)^75*50000000000000^59 ≤ 16381324069993^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078427193 5000000000 16381324069993 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5063323769/10000000000 : ℝ), (-3374819929/10000000000 : ℝ), (-2078427193/5000000000 : ℝ)] ![(42100055459979/100000000000000 : ℝ), (6284324095461/25000000000000 : ℝ), (16381324069993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5063323769/10000000000 : ℝ)|^75 ≤ (42100055459979/100000000000000 : ℝ)^59
        have hw : |(5063323769/10000000000 : ℝ)|=(5063323769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3374819929/10000000000 : ℝ)|^75 ≤ (6284324095461/25000000000000 : ℝ)^59
        have hw : |(-3374819929/10000000000 : ℝ)|=(3374819929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078427193/5000000000 : ℝ)|^75 ≤ (16381324069993/50000000000000 : ℝ)^59
        have hw : |(-2078427193/5000000000 : ℝ)|=(2078427193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314084_s0_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4213709709/10000000000 : ℝ)*x 0 + (-4213709709/10000000000 : ℝ)*x 1 + (4213709709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213709709/10000000000 : ℝ)^75 ≤ (6666666665143/20000000000000 : ℝ)^59 := by
    have hnat : (4213709709 : ℕ)^75*20000000000000^59 ≤ 6666666665143^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213709709 10000000000 6666666665143 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4213709709/10000000000 : ℝ)^75 ≤ (6666666665143/20000000000000 : ℝ)^59 := by
    have hnat : (4213709709 : ℕ)^75*20000000000000^59 ≤ 6666666665143^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213709709 10000000000 6666666665143 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4213709709/10000000000 : ℝ)^75 ≤ (6666666665143/20000000000000 : ℝ)^59 := by
    have hnat : (4213709709 : ℕ)^75*20000000000000^59 ≤ 6666666665143^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213709709 10000000000 6666666665143 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213709709/10000000000 : ℝ), (-4213709709/10000000000 : ℝ), (4213709709/10000000000 : ℝ)] ![(6666666665143/20000000000000 : ℝ), (6666666665143/20000000000000 : ℝ), (6666666665143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213709709/10000000000 : ℝ)|^75 ≤ (6666666665143/20000000000000 : ℝ)^59
        have hw : |(4213709709/10000000000 : ℝ)|=(4213709709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4213709709/10000000000 : ℝ)|^75 ≤ (6666666665143/20000000000000 : ℝ)^59
        have hw : |(-4213709709/10000000000 : ℝ)|=(4213709709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4213709709/10000000000 : ℝ)|^75 ≤ (6666666665143/20000000000000 : ℝ)^59
        have hw : |(4213709709/10000000000 : ℝ)|=(4213709709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314084 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  have s0_pow0 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2078427193/5000000000 : ℝ)*X 0 0+(-5063323769/10000000000 : ℝ)*X 0 1+(3374819929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314084_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3374819929/10000000000 : ℝ)*X 1 0+(2078427193/5000000000 : ℝ)*X 1 1+(5063323769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314084_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5063323769/10000000000 : ℝ)*X 2 0+(-3374819929/10000000000 : ℝ)*X 2 1+(-2078427193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314084_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((4213709709/10000000000 : ℝ)*X 0 0+(-4213709709/10000000000 : ℝ)*X 0 1+(4213709709/10000000000 : ℝ)*X 0 2+(4213709709/10000000000 : ℝ)*X 1 0+(-4213709709/10000000000 : ℝ)*X 1 1+(4213709709/10000000000 : ℝ)*X 1 2+(4213709709/10000000000 : ℝ)*X 2 0+(-4213709709/10000000000 : ℝ)*X 2 1+(4213709709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314084_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-71970159352956548291477/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (999999990061/1000000000000 : ℝ)*(base6) + (130092223587/250000000000 : ℝ)*(base40) + (130092223587/250000000000 : ℝ)*(base50) + (130092223587/250000000000 : ℝ)*(base60) + (172069/100000 : ℝ)*(major_s0_0) + (172069/100000 : ℝ)*(major_s0_1) + (172069/100000 : ℝ)*(major_s0_2) + (546467728357/200000000000 : ℝ)*(sp_s0_0) + (546467728357/200000000000 : ℝ)*(sp_s0_1) + (546467728357/200000000000 : ℝ)*(sp_s0_2) + (9939/1000000000000 : ℝ)*(sp_s0_6) + (546467728357/200000000000 : ℝ)*(f.sum) + (270280681/10000000000000000000000 : ℝ)*base62 + (373200303/5000000000000000000000 : ℝ)*base65 + (411008883/5000000000000000000000 : ℝ)*base66 + (411008883/5000000000000000000000 : ℝ)*base68 + (270280681/10000000000000000000000 : ℝ)*base71 + (373200303/5000000000000000000000 : ℝ)*base72 + (373200303/5000000000000000000000 : ℝ)*base74 + (411008883/5000000000000000000000 : ℝ)*base77 + (270280681/10000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p014_b034 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 82 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=82 ∨ c=83 ∨ c=84 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c314082 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314083 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314084 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 82 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

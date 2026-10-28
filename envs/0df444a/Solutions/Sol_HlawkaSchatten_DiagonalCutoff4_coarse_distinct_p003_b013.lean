-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b013
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:54:09.96626+00:00
-- url     : https://prove2.me/submissions/a2e6b15f-ee64-4649-8cc4-c9cda0f2a82f

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10027
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
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
theorem collision_support_c303026_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2284178081/5000000000 : ℝ)*x 0 + (-528507391/2000000000 : ℝ)*x 1 + (-5594579669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2284178081/5000000000 : ℝ)^135 ≤ (35814122145671/100000000000000 : ℝ)^103 := by
    have hnat : (2284178081 : ℕ)^135*100000000000000^103 ≤ 35814122145671^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284178081 5000000000 35814122145671 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528507391/2000000000 : ℝ)^135 ≤ (17476513621517/100000000000000 : ℝ)^103 := by
    have hnat : (528507391 : ℕ)^135*100000000000000^103 ≤ 17476513621517^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528507391 2000000000 17476513621517 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5594579669/10000000000 : ℝ)^135 ≤ (11677341056693/25000000000000 : ℝ)^103 := by
    have hnat : (5594579669 : ℕ)^135*25000000000000^103 ≤ 11677341056693^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5594579669 10000000000 11677341056693 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2284178081/5000000000 : ℝ), (-528507391/2000000000 : ℝ), (-5594579669/10000000000 : ℝ)] ![(35814122145671/100000000000000 : ℝ), (17476513621517/100000000000000 : ℝ), (11677341056693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2284178081/5000000000 : ℝ)|^135 ≤ (35814122145671/100000000000000 : ℝ)^103
        have hw : |(2284178081/5000000000 : ℝ)|=(2284178081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528507391/2000000000 : ℝ)|^135 ≤ (17476513621517/100000000000000 : ℝ)^103
        have hw : |(-528507391/2000000000 : ℝ)|=(528507391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5594579669/10000000000 : ℝ)|^135 ≤ (11677341056693/25000000000000 : ℝ)^103
        have hw : |(-5594579669/10000000000 : ℝ)|=(5594579669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (445898809/1000000000 : ℝ)*x 0 + (921004153/2000000000 : ℝ)*x 1 + (1950298307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445898809/1000000000 : ℝ)^135 ≤ (1734727209083/5000000000000 : ℝ)^103 := by
    have hnat : (445898809 : ℕ)^135*5000000000000^103 ≤ 1734727209083^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445898809 1000000000 1734727209083 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921004153/2000000000 : ℝ)^135 ≤ (36191327630723/100000000000000 : ℝ)^103 := by
    have hnat : (921004153 : ℕ)^135*100000000000000^103 ≤ 36191327630723^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921004153 2000000000 36191327630723 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950298307/5000000000 : ℝ)^135 ≤ (29114128167119/100000000000000 : ℝ)^103 := by
    have hnat : (1950298307 : ℕ)^135*100000000000000^103 ≤ 29114128167119^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950298307 5000000000 29114128167119 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445898809/1000000000 : ℝ), (921004153/2000000000 : ℝ), (1950298307/5000000000 : ℝ)] ![(1734727209083/5000000000000 : ℝ), (36191327630723/100000000000000 : ℝ), (29114128167119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445898809/1000000000 : ℝ)|^135 ≤ (1734727209083/5000000000000 : ℝ)^103
        have hw : |(445898809/1000000000 : ℝ)|=(445898809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921004153/2000000000 : ℝ)|^135 ≤ (36191327630723/100000000000000 : ℝ)^103
        have hw : |(921004153/2000000000 : ℝ)|=(921004153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1950298307/5000000000 : ℝ)|^135 ≤ (29114128167119/100000000000000 : ℝ)^103
        have hw : |(1950298307/5000000000 : ℝ)|=(1950298307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^135 ≤ (0 : ℝ)^103 := by
    have hnat : (0 : ℕ)^135*1^103 ≤ 0^103*1^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^135 ≤ (1 : ℝ)^103 := by
    have hnat : (1 : ℕ)^135*1^103 ≤ 1^103*1^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^135 ≤ (0 : ℝ)^103 := by
    have hnat : (0 : ℕ)^135*1^103 ≤ 0^103*1^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^135 ≤ (0 : ℝ)^103
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^135 ≤ (1 : ℝ)^103
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^135 ≤ (0 : ℝ)^103
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1511199273/10000000000 : ℝ)*x 0 + (848607181/1000000000 : ℝ)*x 1 + (-1850671101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1511199273/10000000000 : ℝ)^135 ≤ (4200720014199/50000000000000 : ℝ)^103 := by
    have hnat : (1511199273 : ℕ)^135*50000000000000^103 ≤ 4200720014199^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511199273 10000000000 4200720014199 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848607181/1000000000 : ℝ)^135 ≤ (80641264383373/100000000000000 : ℝ)^103 := by
    have hnat : (848607181 : ℕ)^135*100000000000000^103 ≤ 80641264383373^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848607181 1000000000 80641264383373 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1850671101/10000000000 : ℝ)^135 ≤ (2739323895003/25000000000000 : ℝ)^103 := by
    have hnat : (1850671101 : ℕ)^135*25000000000000^103 ≤ 2739323895003^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850671101 10000000000 2739323895003 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1511199273/10000000000 : ℝ), (848607181/1000000000 : ℝ), (-1850671101/10000000000 : ℝ)] ![(4200720014199/50000000000000 : ℝ), (80641264383373/100000000000000 : ℝ), (2739323895003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1511199273/10000000000 : ℝ)|^135 ≤ (4200720014199/50000000000000 : ℝ)^103
        have hw : |(1511199273/10000000000 : ℝ)|=(1511199273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848607181/1000000000 : ℝ)|^135 ≤ (80641264383373/100000000000000 : ℝ)^103
        have hw : |(848607181/1000000000 : ℝ)|=(848607181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1850671101/10000000000 : ℝ)|^135 ≤ (2739323895003/25000000000000 : ℝ)^103
        have hw : |(-1850671101/10000000000 : ℝ)|=(1850671101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5099701849/10000000000 : ℝ)*x 0 + (588529043/2000000000 : ℝ)*x 1 + (-603525301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5099701849/10000000000 : ℝ)^135 ≤ (20684971084069/50000000000000 : ℝ)^103 := by
    have hnat : (5099701849 : ℕ)^135*50000000000000^103 ≤ 20684971084069^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099701849 10000000000 20684971084069 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588529043/2000000000 : ℝ)^135 ≤ (10061334930461/50000000000000 : ℝ)^103 := by
    have hnat : (588529043 : ℕ)^135*50000000000000^103 ≤ 10061334930461^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588529043 2000000000 10061334930461 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603525301/1250000000 : ℝ)^135 ≤ (19253693976629/50000000000000 : ℝ)^103 := by
    have hnat : (603525301 : ℕ)^135*50000000000000^103 ≤ 19253693976629^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603525301 1250000000 19253693976629 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5099701849/10000000000 : ℝ), (588529043/2000000000 : ℝ), (-603525301/1250000000 : ℝ)] ![(20684971084069/50000000000000 : ℝ), (10061334930461/50000000000000 : ℝ), (19253693976629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5099701849/10000000000 : ℝ)|^135 ≤ (20684971084069/50000000000000 : ℝ)^103
        have hw : |(-5099701849/10000000000 : ℝ)|=(5099701849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588529043/2000000000 : ℝ)|^135 ≤ (10061334930461/50000000000000 : ℝ)^103
        have hw : |(588529043/2000000000 : ℝ)|=(588529043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-603525301/1250000000 : ℝ)|^135 ≤ (19253693976629/50000000000000 : ℝ)^103
        have hw : |(-603525301/1250000000 : ℝ)|=(603525301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (229657849/500000000 : ℝ)*x 0 + (-339267619/2000000000 : ℝ)*x 1 + (-782867567/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (229657849/500000000 : ℝ)^135 ≤ (18034585254389/50000000000000 : ℝ)^103 := by
    have hnat : (229657849 : ℕ)^135*50000000000000^103 ≤ 18034585254389^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229657849 500000000 18034585254389 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339267619/2000000000 : ℝ)^135 ≤ (4887734824093/50000000000000 : ℝ)^103 := by
    have hnat : (339267619 : ℕ)^135*50000000000000^103 ≤ 4887734824093^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339267619 2000000000 4887734824093 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (782867567/1250000000 : ℝ)^135 ≤ (27077679914511/50000000000000 : ℝ)^103 := by
    have hnat : (782867567 : ℕ)^135*50000000000000^103 ≤ 27077679914511^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782867567 1250000000 27077679914511 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(229657849/500000000 : ℝ), (-339267619/2000000000 : ℝ), (-782867567/1250000000 : ℝ)] ![(18034585254389/50000000000000 : ℝ), (4887734824093/50000000000000 : ℝ), (27077679914511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(229657849/500000000 : ℝ)|^135 ≤ (18034585254389/50000000000000 : ℝ)^103
        have hw : |(229657849/500000000 : ℝ)|=(229657849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339267619/2000000000 : ℝ)|^135 ≤ (4887734824093/50000000000000 : ℝ)^103
        have hw : |(-339267619/2000000000 : ℝ)|=(339267619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-782867567/1250000000 : ℝ)|^135 ≤ (27077679914511/50000000000000 : ℝ)^103
        have hw : |(-782867567/1250000000 : ℝ)|=(782867567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (473322397/1250000000 : ℝ)*x 0 + (2761612737/5000000000 : ℝ)*x 1 + (71699763/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473322397/1250000000 : ℝ)^135 ≤ (28003801917961/100000000000000 : ℝ)^103 := by
    have hnat : (473322397 : ℕ)^135*100000000000000^103 ≤ 28003801917961^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473322397 1250000000 28003801917961 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761612737/5000000000 : ℝ)^135 ≤ (45930092863363/100000000000000 : ℝ)^103 := by
    have hnat : (2761612737 : ℕ)^135*100000000000000^103 ≤ 45930092863363^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761612737 5000000000 45930092863363 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71699763/200000000 : ℝ)^135 ≤ (3258263150207/12500000000000 : ℝ)^103 := by
    have hnat : (71699763 : ℕ)^135*12500000000000^103 ≤ 3258263150207^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71699763 200000000 3258263150207 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(473322397/1250000000 : ℝ), (2761612737/5000000000 : ℝ), (71699763/200000000 : ℝ)] ![(28003801917961/100000000000000 : ℝ), (45930092863363/100000000000000 : ℝ), (3258263150207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(473322397/1250000000 : ℝ)|^135 ≤ (28003801917961/100000000000000 : ℝ)^103
        have hw : |(473322397/1250000000 : ℝ)|=(473322397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2761612737/5000000000 : ℝ)|^135 ≤ (45930092863363/100000000000000 : ℝ)^103
        have hw : |(2761612737/5000000000 : ℝ)|=(2761612737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71699763/200000000 : ℝ)|^135 ≤ (3258263150207/12500000000000 : ℝ)^103
        have hw : |(71699763/200000000 : ℝ)|=(71699763/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_12 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (223118449/5000000000 : ℝ)*x 0 + (2418554871/2500000000 : ℝ)*x 1 + (-38028789/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223118449/5000000000 : ℝ)^135 ≤ (424573626911/25000000000000 : ℝ)^103 := by
    have hnat : (223118449 : ℕ)^135*25000000000000^103 ≤ 424573626911^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223118449 5000000000 424573626911 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418554871/2500000000 : ℝ)^135 ≤ (95751833960727/100000000000000 : ℝ)^103 := by
    have hnat : (2418554871 : ℕ)^135*100000000000000^103 ≤ 95751833960727^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418554871 2500000000 95751833960727 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38028789/625000000 : ℝ)^135 ≤ (318733939113/12500000000000 : ℝ)^103 := by
    have hnat : (38028789 : ℕ)^135*12500000000000^103 ≤ 318733939113^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38028789 625000000 318733939113 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223118449/5000000000 : ℝ), (2418554871/2500000000 : ℝ), (-38028789/625000000 : ℝ)] ![(424573626911/25000000000000 : ℝ), (95751833960727/100000000000000 : ℝ), (318733939113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223118449/5000000000 : ℝ)|^135 ≤ (424573626911/25000000000000 : ℝ)^103
        have hw : |(223118449/5000000000 : ℝ)|=(223118449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418554871/2500000000 : ℝ)|^135 ≤ (95751833960727/100000000000000 : ℝ)^103
        have hw : |(2418554871/2500000000 : ℝ)|=(2418554871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38028789/625000000 : ℝ)|^135 ≤ (318733939113/12500000000000 : ℝ)^103
        have hw : |(-38028789/625000000 : ℝ)|=(38028789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5810713041/10000000000 : ℝ)*x 0 + (3387258767/10000000000 : ℝ)*x 1 + (-3652703337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5810713041/10000000000 : ℝ)^135 ≤ (49088563008849/100000000000000 : ℝ)^103 := by
    have hnat : (5810713041 : ℕ)^135*100000000000000^103 ≤ 49088563008849^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5810713041 10000000000 49088563008849 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3387258767/10000000000 : ℝ)^135 ≤ (24198132553037/100000000000000 : ℝ)^103 := by
    have hnat : (3387258767 : ℕ)^135*100000000000000^103 ≤ 24198132553037^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3387258767 10000000000 24198132553037 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3652703337/10000000000 : ℝ)^135 ≤ (26713304429129/100000000000000 : ℝ)^103 := by
    have hnat : (3652703337 : ℕ)^135*100000000000000^103 ≤ 26713304429129^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3652703337 10000000000 26713304429129 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5810713041/10000000000 : ℝ), (3387258767/10000000000 : ℝ), (-3652703337/10000000000 : ℝ)] ![(49088563008849/100000000000000 : ℝ), (24198132553037/100000000000000 : ℝ), (26713304429129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5810713041/10000000000 : ℝ)|^135 ≤ (49088563008849/100000000000000 : ℝ)^103
        have hw : |(-5810713041/10000000000 : ℝ)|=(5810713041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3387258767/10000000000 : ℝ)|^135 ≤ (24198132553037/100000000000000 : ℝ)^103
        have hw : |(3387258767/10000000000 : ℝ)|=(3387258767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3652703337/10000000000 : ℝ)|^135 ≤ (26713304429129/100000000000000 : ℝ)^103
        have hw : |(-3652703337/10000000000 : ℝ)|=(3652703337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (199162879/400000000 : ℝ)*x 0 + (-2360731533/10000000000 : ℝ)*x 1 + (-677781151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199162879/400000000 : ℝ)^135 ≤ (40092079984873/100000000000000 : ℝ)^103 := by
    have hnat : (199162879 : ℕ)^135*100000000000000^103 ≤ 40092079984873^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199162879 400000000 40092079984873 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2360731533/10000000000 : ℝ)^135 ≤ (7537632629453/50000000000000 : ℝ)^103 := by
    have hnat : (2360731533 : ℕ)^135*50000000000000^103 ≤ 7537632629453^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360731533 10000000000 7537632629453 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677781151/1250000000 : ℝ)^135 ≤ (11208163686971/25000000000000 : ℝ)^103 := by
    have hnat : (677781151 : ℕ)^135*25000000000000^103 ≤ 11208163686971^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677781151 1250000000 11208163686971 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(199162879/400000000 : ℝ), (-2360731533/10000000000 : ℝ), (-677781151/1250000000 : ℝ)] ![(40092079984873/100000000000000 : ℝ), (7537632629453/50000000000000 : ℝ), (11208163686971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(199162879/400000000 : ℝ)|^135 ≤ (40092079984873/100000000000000 : ℝ)^103
        have hw : |(199162879/400000000 : ℝ)|=(199162879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2360731533/10000000000 : ℝ)|^135 ≤ (7537632629453/50000000000000 : ℝ)^103
        have hw : |(-2360731533/10000000000 : ℝ)|=(2360731533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-677781151/1250000000 : ℝ)|^135 ≤ (11208163686971/25000000000000 : ℝ)^103
        have hw : |(-677781151/1250000000 : ℝ)|=(677781151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3607450029/10000000000 : ℝ)*x 0 + (2351010289/5000000000 : ℝ)*x 1 + (579682909/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3607450029/10000000000 : ℝ)^135 ≤ (13140185518387/50000000000000 : ℝ)^103 := by
    have hnat : (3607450029 : ℕ)^135*50000000000000^103 ≤ 13140185518387^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3607450029 10000000000 13140185518387 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2351010289/5000000000 : ℝ)^135 ≤ (37193753551701/100000000000000 : ℝ)^103 := by
    have hnat : (2351010289 : ℕ)^135*100000000000000^103 ≤ 37193753551701^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351010289 5000000000 37193753551701 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579682909/1250000000 : ℝ)^135 ≤ (36525875391299/100000000000000 : ℝ)^103 := by
    have hnat : (579682909 : ℕ)^135*100000000000000^103 ≤ 36525875391299^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579682909 1250000000 36525875391299 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3607450029/10000000000 : ℝ), (2351010289/5000000000 : ℝ), (579682909/1250000000 : ℝ)] ![(13140185518387/50000000000000 : ℝ), (37193753551701/100000000000000 : ℝ), (36525875391299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3607450029/10000000000 : ℝ)|^135 ≤ (13140185518387/50000000000000 : ℝ)^103
        have hw : |(3607450029/10000000000 : ℝ)|=(3607450029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2351010289/5000000000 : ℝ)|^135 ≤ (37193753551701/100000000000000 : ℝ)^103
        have hw : |(2351010289/5000000000 : ℝ)|=(2351010289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(579682909/1250000000 : ℝ)|^135 ≤ (36525875391299/100000000000000 : ℝ)^103
        have hw : |(579682909/1250000000 : ℝ)|=(579682909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_19 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (831800583/10000000000 : ℝ)*x 0 + (528249331/625000000 : ℝ)*x 1 + (-1231772451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (831800583/10000000000 : ℝ)^135 ≤ (153656594109/4000000000000 : ℝ)^103 := by
    have hnat : (831800583 : ℕ)^135*4000000000000^103 ≤ 153656594109^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831800583 10000000000 153656594109 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528249331/625000000 : ℝ)^135 ≤ (80217028397691/100000000000000 : ℝ)^103 := by
    have hnat : (528249331 : ℕ)^135*100000000000000^103 ≤ 80217028397691^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528249331 625000000 80217028397691 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231772451/5000000000 : ℝ)^135 ≤ (3985389185683/25000000000000 : ℝ)^103 := by
    have hnat : (1231772451 : ℕ)^135*25000000000000^103 ≤ 3985389185683^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231772451 5000000000 3985389185683 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(831800583/10000000000 : ℝ), (528249331/625000000 : ℝ), (-1231772451/5000000000 : ℝ)] ![(153656594109/4000000000000 : ℝ), (80217028397691/100000000000000 : ℝ), (3985389185683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(831800583/10000000000 : ℝ)|^135 ≤ (153656594109/4000000000000 : ℝ)^103
        have hw : |(831800583/10000000000 : ℝ)|=(831800583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528249331/625000000 : ℝ)|^135 ≤ (80217028397691/100000000000000 : ℝ)^103
        have hw : |(528249331/625000000 : ℝ)|=(528249331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1231772451/5000000000 : ℝ)|^135 ≤ (3985389185683/25000000000000 : ℝ)^103
        have hw : |(-1231772451/5000000000 : ℝ)|=(1231772451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5311102417/10000000000 : ℝ)*x 0 + (444979587/1250000000 : ℝ)*x 1 + (-4045651361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311102417/10000000000 : ℝ)^135 ≤ (43632003776517/100000000000000 : ℝ)^103 := by
    have hnat : (5311102417 : ℕ)^135*100000000000000^103 ≤ 43632003776517^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311102417 10000000000 43632003776517 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444979587/1250000000 : ℝ)^135 ≤ (25826677868077/100000000000000 : ℝ)^103 := by
    have hnat : (444979587 : ℕ)^135*100000000000000^103 ≤ 25826677868077^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444979587 1250000000 25826677868077 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4045651361/10000000000 : ℝ)^135 ≤ (15270659168893/50000000000000 : ℝ)^103 := by
    have hnat : (4045651361 : ℕ)^135*50000000000000^103 ≤ 15270659168893^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4045651361 10000000000 15270659168893 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5311102417/10000000000 : ℝ), (444979587/1250000000 : ℝ), (-4045651361/10000000000 : ℝ)] ![(43632003776517/100000000000000 : ℝ), (25826677868077/100000000000000 : ℝ), (15270659168893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5311102417/10000000000 : ℝ)|^135 ≤ (43632003776517/100000000000000 : ℝ)^103
        have hw : |(-5311102417/10000000000 : ℝ)|=(5311102417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(444979587/1250000000 : ℝ)|^135 ≤ (25826677868077/100000000000000 : ℝ)^103
        have hw : |(444979587/1250000000 : ℝ)|=(444979587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4045651361/10000000000 : ℝ)|^135 ≤ (15270659168893/50000000000000 : ℝ)^103
        have hw : |(-4045651361/10000000000 : ℝ)|=(4045651361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (88286337/200000000 : ℝ)*x 0 + (-1273953557/5000000000 : ℝ)*x 1 + (-2905848917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88286337/200000000 : ℝ)^135 ≤ (34239690754797/100000000000000 : ℝ)^103 := by
    have hnat : (88286337 : ℕ)^135*100000000000000^103 ≤ 34239690754797^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88286337 200000000 34239690754797 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273953557/5000000000 : ℝ)^135 ≤ (2082605222803/12500000000000 : ℝ)^103 := by
    have hnat : (1273953557 : ℕ)^135*12500000000000^103 ≤ 2082605222803^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273953557 5000000000 2082605222803 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2905848917/5000000000 : ℝ)^135 ≤ (24549733730111/50000000000000 : ℝ)^103 := by
    have hnat : (2905848917 : ℕ)^135*50000000000000^103 ≤ 24549733730111^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2905848917 5000000000 24549733730111 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(88286337/200000000 : ℝ), (-1273953557/5000000000 : ℝ), (-2905848917/5000000000 : ℝ)] ![(34239690754797/100000000000000 : ℝ), (2082605222803/12500000000000 : ℝ), (24549733730111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(88286337/200000000 : ℝ)|^135 ≤ (34239690754797/100000000000000 : ℝ)^103
        have hw : |(88286337/200000000 : ℝ)|=(88286337/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1273953557/5000000000 : ℝ)|^135 ≤ (2082605222803/12500000000000 : ℝ)^103
        have hw : |(-1273953557/5000000000 : ℝ)|=(1273953557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2905848917/5000000000 : ℝ)|^135 ≤ (24549733730111/50000000000000 : ℝ)^103
        have hw : |(-2905848917/5000000000 : ℝ)|=(2905848917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5066707441/10000000000 : ℝ)*x 0 + (401798883/1000000000 : ℝ)*x 1 + (3859487211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5066707441/10000000000 : ℝ)^135 ≤ (20509740597351/50000000000000 : ℝ)^103 := by
    have hnat : (5066707441 : ℕ)^135*50000000000000^103 ≤ 20509740597351^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066707441 10000000000 20509740597351 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401798883/1000000000 : ℝ)^135 ≤ (7566975332847/25000000000000 : ℝ)^103 := by
    have hnat : (401798883 : ℕ)^135*25000000000000^103 ≤ 7566975332847^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401798883 1000000000 7566975332847 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3859487211/10000000000 : ℝ)^135 ≤ (28712617455187/100000000000000 : ℝ)^103 := by
    have hnat : (3859487211 : ℕ)^135*100000000000000^103 ≤ 28712617455187^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3859487211 10000000000 28712617455187 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5066707441/10000000000 : ℝ), (401798883/1000000000 : ℝ), (3859487211/10000000000 : ℝ)] ![(20509740597351/50000000000000 : ℝ), (7566975332847/25000000000000 : ℝ), (28712617455187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5066707441/10000000000 : ℝ)|^135 ≤ (20509740597351/50000000000000 : ℝ)^103
        have hw : |(5066707441/10000000000 : ℝ)|=(5066707441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401798883/1000000000 : ℝ)|^135 ≤ (7566975332847/25000000000000 : ℝ)^103
        have hw : |(401798883/1000000000 : ℝ)|=(401798883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3859487211/10000000000 : ℝ)|^135 ≤ (28712617455187/100000000000000 : ℝ)^103
        have hw : |(3859487211/10000000000 : ℝ)|=(3859487211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s0_25 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (46936577/1250000000 : ℝ)*x 0 + (9747478229/10000000000 : ℝ)*x 1 + (-494357269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46936577/1250000000 : ℝ)^135 ≤ (5290773293/390625000000 : ℝ)^103 := by
    have hnat : (46936577 : ℕ)^135*390625000000^103 ≤ 5290773293^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46936577 1250000000 5290773293 390625000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9747478229/10000000000 : ℝ)^135 ≤ (4835165391753/5000000000000 : ℝ)^103 := by
    have hnat : (9747478229 : ℕ)^135*5000000000000^103 ≤ 4835165391753^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9747478229 10000000000 4835165391753 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494357269/10000000000 : ℝ)^135 ≤ (1942254185149/100000000000000 : ℝ)^103 := by
    have hnat : (494357269 : ℕ)^135*100000000000000^103 ≤ 1942254185149^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494357269 10000000000 1942254185149 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(46936577/1250000000 : ℝ), (9747478229/10000000000 : ℝ), (-494357269/10000000000 : ℝ)] ![(5290773293/390625000000 : ℝ), (4835165391753/5000000000000 : ℝ), (1942254185149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(46936577/1250000000 : ℝ)|^135 ≤ (5290773293/390625000000 : ℝ)^103
        have hw : |(46936577/1250000000 : ℝ)|=(46936577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9747478229/10000000000 : ℝ)|^135 ≤ (4835165391753/5000000000000 : ℝ)^103
        have hw : |(9747478229/10000000000 : ℝ)|=(9747478229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494357269/10000000000 : ℝ)|^135 ≤ (1942254185149/100000000000000 : ℝ)^103
        have hw : |(-494357269/10000000000 : ℝ)|=(494357269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-4683079899/10000000000 : ℝ)*x 0 + (3783606109/10000000000 : ℝ)*x 1 + (-4491600493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4683079899/10000000000 : ℝ)^135 ≤ (18498752721781/50000000000000 : ℝ)^103 := by
    have hnat : (4683079899 : ℕ)^135*50000000000000^103 ≤ 18498752721781^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4683079899 10000000000 18498752721781 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3783606109/10000000000 : ℝ)^135 ≤ (2797498694523/10000000000000 : ℝ)^103 := by
    have hnat : (3783606109 : ℕ)^135*10000000000000^103 ≤ 2797498694523^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3783606109 10000000000 2797498694523 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491600493/10000000000 : ℝ)^135 ≤ (35027507605327/100000000000000 : ℝ)^103 := by
    have hnat : (4491600493 : ℕ)^135*100000000000000^103 ≤ 35027507605327^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491600493 10000000000 35027507605327 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4683079899/10000000000 : ℝ), (3783606109/10000000000 : ℝ), (-4491600493/10000000000 : ℝ)] ![(18498752721781/50000000000000 : ℝ), (2797498694523/10000000000000 : ℝ), (35027507605327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4683079899/10000000000 : ℝ)|^135 ≤ (18498752721781/50000000000000 : ℝ)^103
        have hw : |(-4683079899/10000000000 : ℝ)|=(4683079899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3783606109/10000000000 : ℝ)|^135 ≤ (2797498694523/10000000000000 : ℝ)^103
        have hw : |(3783606109/10000000000 : ℝ)|=(3783606109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4491600493/10000000000 : ℝ)|^135 ≤ (35027507605327/100000000000000 : ℝ)^103
        have hw : |(-4491600493/10000000000 : ℝ)|=(4491600493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2264656131/5000000000 : ℝ)*x 0 + (-908723657/2500000000 : ℝ)*x 1 + (-956758067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2264656131/5000000000 : ℝ)^135 ≤ (4426683921157/12500000000000 : ℝ)^103 := by
    have hnat : (2264656131 : ℕ)^135*12500000000000^103 ≤ 4426683921157^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264656131 5000000000 4426683921157 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908723657/2500000000 : ℝ)^135 ≤ (13271365224533/50000000000000 : ℝ)^103 := by
    have hnat : (908723657 : ℕ)^135*50000000000000^103 ≤ 13271365224533^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908723657 2500000000 13271365224533 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956758067/2000000000 : ℝ)^135 ≤ (38043798165893/100000000000000 : ℝ)^103 := by
    have hnat : (956758067 : ℕ)^135*100000000000000^103 ≤ 38043798165893^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956758067 2000000000 38043798165893 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2264656131/5000000000 : ℝ), (-908723657/2500000000 : ℝ), (-956758067/2000000000 : ℝ)] ![(4426683921157/12500000000000 : ℝ), (13271365224533/50000000000000 : ℝ), (38043798165893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2264656131/5000000000 : ℝ)|^135 ≤ (4426683921157/12500000000000 : ℝ)^103
        have hw : |(2264656131/5000000000 : ℝ)|=(2264656131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908723657/2500000000 : ℝ)|^135 ≤ (13271365224533/50000000000000 : ℝ)^103
        have hw : |(-908723657/2500000000 : ℝ)|=(908723657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-956758067/2000000000 : ℝ)|^135 ≤ (38043798165893/100000000000000 : ℝ)^103
        have hw : |(-956758067/2000000000 : ℝ)|=(956758067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (203252199/500000000 : ℝ)*x 0 + (4986431359/10000000000 : ℝ)*x 1 + (779766903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203252199/500000000 : ℝ)^135 ≤ (30733342217633/100000000000000 : ℝ)^103 := by
    have hnat : (203252199 : ℕ)^135*100000000000000^103 ≤ 30733342217633^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203252199 500000000 30733342217633 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4986431359/10000000000 : ℝ)^135 ≤ (8033953379469/20000000000000 : ℝ)^103 := by
    have hnat : (4986431359 : ℕ)^135*20000000000000^103 ≤ 8033953379469^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986431359 10000000000 8033953379469 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (779766903/2000000000 : ℝ)^135 ≤ (29096890871977/100000000000000 : ℝ)^103 := by
    have hnat : (779766903 : ℕ)^135*100000000000000^103 ≤ 29096890871977^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779766903 2000000000 29096890871977 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(203252199/500000000 : ℝ), (4986431359/10000000000 : ℝ), (779766903/2000000000 : ℝ)] ![(30733342217633/100000000000000 : ℝ), (8033953379469/20000000000000 : ℝ), (29096890871977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(203252199/500000000 : ℝ)|^135 ≤ (30733342217633/100000000000000 : ℝ)^103
        have hw : |(203252199/500000000 : ℝ)|=(203252199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4986431359/10000000000 : ℝ)|^135 ≤ (8033953379469/20000000000000 : ℝ)^103
        have hw : |(4986431359/10000000000 : ℝ)|=(4986431359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(779766903/2000000000 : ℝ)|^135 ≤ (29096890871977/100000000000000 : ℝ)^103
        have hw : |(779766903/2000000000 : ℝ)|=(779766903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303026_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1828188843/5000000000 : ℝ)*x 0 + (1348255877/2500000000 : ℝ)*x 1 + (-965452547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1828188843/5000000000 : ℝ)^135 ≤ (13374264998469/50000000000000 : ℝ)^103 := by
    have hnat : (1828188843 : ℕ)^135*50000000000000^103 ≤ 13374264998469^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828188843 5000000000 13374264998469 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348255877/2500000000 : ℝ)^135 ≤ (22258099779943/50000000000000 : ℝ)^103 := by
    have hnat : (1348255877 : ℕ)^135*50000000000000^103 ≤ 22258099779943^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348255877 2500000000 22258099779943 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965452547/2500000000 : ℝ)^135 ≤ (3591908803671/12500000000000 : ℝ)^103 := by
    have hnat : (965452547 : ℕ)^135*12500000000000^103 ≤ 3591908803671^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965452547 2500000000 3591908803671 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1828188843/5000000000 : ℝ), (1348255877/2500000000 : ℝ), (-965452547/2500000000 : ℝ)] ![(13374264998469/50000000000000 : ℝ), (22258099779943/50000000000000 : ℝ), (3591908803671/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1828188843/5000000000 : ℝ)|^135 ≤ (13374264998469/50000000000000 : ℝ)^103
        have hw : |(1828188843/5000000000 : ℝ)|=(1828188843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348255877/2500000000 : ℝ)|^135 ≤ (22258099779943/50000000000000 : ℝ)^103
        have hw : |(1348255877/2500000000 : ℝ)|=(1348255877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-965452547/2500000000 : ℝ)|^135 ≤ (3591908803671/12500000000000 : ℝ)^103
        have hw : |(-965452547/2500000000 : ℝ)|=(965452547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303026 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((2284178081/5000000000 : ℝ)*X 1 0+(-528507391/2000000000 : ℝ)*X 1 1+(-5594579669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((445898809/1000000000 : ℝ)*X 2 0+(921004153/2000000000 : ℝ)*X 2 1+(1950298307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1511199273/10000000000 : ℝ)*X 0 0+(848607181/1000000000 : ℝ)*X 0 1+(-1850671101/10000000000 : ℝ)*X 0 2+(1511199273/10000000000 : ℝ)*X 1 0+(848607181/1000000000 : ℝ)*X 1 1+(-1850671101/10000000000 : ℝ)*X 1 2+(1511199273/10000000000 : ℝ)*X 2 0+(848607181/1000000000 : ℝ)*X 2 1+(-1850671101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5099701849/10000000000 : ℝ)*X 0 0+(588529043/2000000000 : ℝ)*X 0 1+(-603525301/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((229657849/500000000 : ℝ)*X 1 0+(-339267619/2000000000 : ℝ)*X 1 1+(-782867567/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((473322397/1250000000 : ℝ)*X 2 0+(2761612737/5000000000 : ℝ)*X 2 1+(71699763/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((223118449/5000000000 : ℝ)*X 0 0+(2418554871/2500000000 : ℝ)*X 0 1+(-38028789/625000000 : ℝ)*X 0 2+(223118449/5000000000 : ℝ)*X 1 0+(2418554871/2500000000 : ℝ)*X 1 1+(-38028789/625000000 : ℝ)*X 1 2+(223118449/5000000000 : ℝ)*X 2 0+(2418554871/2500000000 : ℝ)*X 2 1+(-38028789/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5810713041/10000000000 : ℝ)*X 0 0+(3387258767/10000000000 : ℝ)*X 0 1+(-3652703337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((199162879/400000000 : ℝ)*X 1 0+(-2360731533/10000000000 : ℝ)*X 1 1+(-677781151/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3607450029/10000000000 : ℝ)*X 2 0+(2351010289/5000000000 : ℝ)*X 2 1+(579682909/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((831800583/10000000000 : ℝ)*X 0 0+(528249331/625000000 : ℝ)*X 0 1+(-1231772451/5000000000 : ℝ)*X 0 2+(831800583/10000000000 : ℝ)*X 1 0+(528249331/625000000 : ℝ)*X 1 1+(-1231772451/5000000000 : ℝ)*X 1 2+(831800583/10000000000 : ℝ)*X 2 0+(528249331/625000000 : ℝ)*X 2 1+(-1231772451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5311102417/10000000000 : ℝ)*X 0 0+(444979587/1250000000 : ℝ)*X 0 1+(-4045651361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((88286337/200000000 : ℝ)*X 1 0+(-1273953557/5000000000 : ℝ)*X 1 1+(-2905848917/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5066707441/10000000000 : ℝ)*X 2 0+(401798883/1000000000 : ℝ)*X 2 1+(3859487211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((46936577/1250000000 : ℝ)*X 0 0+(9747478229/10000000000 : ℝ)*X 0 1+(-494357269/10000000000 : ℝ)*X 0 2+(46936577/1250000000 : ℝ)*X 1 0+(9747478229/10000000000 : ℝ)*X 1 1+(-494357269/10000000000 : ℝ)*X 1 2+(46936577/1250000000 : ℝ)*X 2 0+(9747478229/10000000000 : ℝ)*X 2 1+(-494357269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((43489/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43489/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (71965824523466432297853/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13175117/1000000000000 : ℝ)*(base18) + (1219828457/3906250000 : ℝ)*(base49) + (445054868449/1000000000000 : ℝ)*(base60) + (2549636330499/500000000000 : ℝ)*(major_s0_0) + (10488008352969/1000000000000 : ℝ)*(major_s0_1) + (2549636330499/500000000000 : ℝ)*(major_s0_2) + (5388735691971/1000000000000 : ℝ)*(sp_s0_4) + (6808517481453/1000000000000 : ℝ)*(sp_s0_7) + (6808347136257/1000000000000 : ℝ)*(sp_s0_8) + (54467771251/8000000000 : ℝ)*(sp_s0_9) + (1695001882183/500000000000 : ℝ)*(sp_s0_12) + (46075079/1000000000000 : ℝ)*(sp_s0_15) + (19278447/1000000000000 : ℝ)*(sp_s0_19) + (982313/6250000000 : ℝ)*(sp_s0_21) + (847505760703/250000000000 : ℝ)*(f.failure) + (6808517481453/1000000000000 : ℝ)*(f.sum) + (508473579578587/2000000000000000000000000000 : ℝ)*base62 + (585421029052969/625000000000000000000000000 : ℝ)*base64 + (101971015587961/1250000000000000000000000000 : ℝ)*base67 + (507240408600639/1000000000000000000000000000 : ℝ)*base68 + (3849529288920557/5000000000000000000000000000 : ℝ)*base70 + (502590214759531/625000000000000000000000000 : ℝ)*base73 + (1002365565777309/2000000000000000000000000000 : ℝ)*base74 + (1288536191099361/1000000000000000000000000000 : ℝ)*base76 + (342006756392977/1250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (237/1250000000000000 : ℝ)*base86 + (237/1250000000000000 : ℝ)*base88 + (237/1250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11621/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(11621/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (403817959234776467619/39062500000000000000000000 : ℝ) := by norm_num
    linear_combination (39829164829/250000000000 : ℝ)*(base1) + (2544593/1000000000000 : ℝ)*(base39) + (77881841059/100000000000 : ℝ)*(base49) + (87804482711/250000000000 : ℝ)*(base60) + (13838287283/3906250000 : ℝ)*(major_s0_0) + (13838287283/3906250000 : ℝ)*(major_s0_1) + (13838287283/3906250000 : ℝ)*(major_s0_2) + (168273/1562500000 : ℝ)*(sp_s0_6) + (14551691/500000000000 : ℝ)*(sp_s0_7) + (85408323/1000000000000 : ℝ)*(sp_s0_8) + (4889347227867/1000000000000 : ℝ)*(sp_s0_13) + (472997426361/100000000000 : ℝ)*(sp_s0_14) + (4730059671933/1000000000000 : ℝ)*(sp_s0_15) + (2195715617011/1000000000000 : ℝ)*(sp_s0_19) + (2355139971047/1000000000000 : ℝ)*(f.failure) + (4730059671933/1000000000000 : ℝ)*(f.sum) + (665033364049/7812500000000000000000000 : ℝ)*base63 + (64710522499111/156250000000000000000000000 : ℝ)*base64 + (55943934563389/156250000000000000000000000 : ℝ)*base67 + (3356294862527/31250000000000000000000000 : ℝ)*base68 + (37520834577101/156250000000000000000000000 : ℝ)*base70 + (7585763945757/78125000000000000000000000 : ℝ)*base73 + (1178868942201/15625000000000000000000000 : ℝ)*base74 + (2471422870299/15625000000000000000000000 : ℝ)*base76 + (24601501063389/78125000000000000000000000 : ℝ)*base79 + (4487/5000000000000000 : ℝ)*base87 + (4487/5000000000000000 : ℝ)*base89 + (4487/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-16863/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-16863/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (77356133811028719490467/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396674032491/500000000000 : ℝ)*(base49) + (7398401/1000000000000 : ℝ)*(base60) + (4971680089163/1000000000000 : ℝ)*(major_s0_0) + (8044648622833/1000000000000 : ℝ)*(major_s0_1) + (4971680089163/1000000000000 : ℝ)*(major_s0_2) + (56860843/125000000000 : ℝ)*(sp_s0_1) + (11191317/100000000000 : ℝ)*(sp_s0_2) + (307296853367/100000000000 : ℝ)*(sp_s0_4) + (75919449/125000000000 : ℝ)*(sp_s0_12) + (15812929/250000000000 : ℝ)*(sp_s0_13) + (6638092933493/1000000000000 : ℝ)*(sp_s0_20) + (1327540259693/200000000000 : ℝ)*(sp_s0_21) + (6638044272039/1000000000000 : ℝ)*(sp_s0_22) + (1652295740221/500000000000 : ℝ)*(sp_s0_25) + (1652599418017/500000000000 : ℝ)*(f.failure) + (6638156185209/1000000000000 : ℝ)*(f.sum) + (178622329551861/500000000000000000000000000 : ℝ)*base63 + (1271872672045947/1250000000000000000000000000 : ℝ)*base65 + (326538369972823/1250000000000000000000000000 : ℝ)*base66 + (1369592358513657/2000000000000000000000000000 : ℝ)*base69 + (8185475747799291/10000000000000000000000000000 : ℝ)*base71 + (288754840704053/1250000000000000000000000000 : ℝ)*base72 + (420362939293787/2000000000000000000000000000 : ℝ)*base75 + (1079017075086343/2000000000000000000000000000 : ℝ)*base77 + (2058424643281/312500000000000000000000000 : ℝ)*base79 + (1643/2500000000000000 : ℝ)*base86 + (1643/2500000000000000 : ℝ)*base88 + (1643/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (43489/100000 : ℝ) ^ (131/32 : ℝ) ≤ (3308382817967336273/100000000000000000000 : ℝ) := by
    have hpowers : (43489/100000 : ℝ)^131 ≤ (3308382817967336273/100000000000000000000 : ℝ)^32 := by
      have hnat : (43489 : ℕ)^131*100000000000000000000^32 ≤ 3308382817967336273^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43489 100000 3308382817967336273 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43489/100000 : ℝ)) (X := (3308382817967336273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (103308382817967336273/100000000000000000000 : ℝ) ≤ (2519956074707437/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (103308382817967336273/100000000000000000000 : ℝ)^32 ≤ (2519956074707437/2500000000000000 : ℝ)^131 := by
      have hnat : (103308382817967336273 : ℕ)^32*2500000000000000^131 ≤ 2519956074707437^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103308382817967336273 100000000000000000000 2519956074707437 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2519956074707437/2500000000000000 : ℝ)) (X := (103308382817967336273/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (53308382817967336273/50000000000000000000 : ℝ) ≤ (10157739467307461/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (53308382817967336273/50000000000000000000 : ℝ)^32 ≤ (10157739467307461/10000000000000000 : ℝ)^131 := by
      have hnat : (53308382817967336273 : ℕ)^32*10000000000000000^131 ≤ 10157739467307461^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53308382817967336273 50000000000000000000 10157739467307461 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10157739467307461/10000000000000000 : ℝ)) (X := (53308382817967336273/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19956074707437/1087225000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(77915168477713/4348900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (43489/100000 : ℝ)) (alpha := (19956074707437/1087225000000000 : ℝ)) (beta := (77915168477713/4348900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (43489/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19956074707437/1087225000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(77915168477713/4348900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (11621/100000 : ℝ) ^ (131/32 : ℝ) ≤ (14905295244882339/100000000000000000000 : ℝ) := by
    have hpowers : (11621/100000 : ℝ)^131 ≤ (14905295244882339/100000000000000000000 : ℝ)^32 := by
      have hnat : (11621 : ℕ)^131*100000000000000000000^32 ≤ 14905295244882339^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11621 100000 14905295244882339 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11621/100000 : ℝ)) (X := (14905295244882339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100014905295244882339/100000000000000000000 : ℝ) ≤ (10000364078310327/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100014905295244882339/100000000000000000000 : ℝ)^32 ≤ (10000364078310327/10000000000000000 : ℝ)^131 := by
      have hnat : (100014905295244882339 : ℕ)^32*10000000000000000^131 ≤ 10000364078310327^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014905295244882339 100000000000000000000 10000364078310327 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000364078310327/10000000000000000 : ℝ)) (X := (100014905295244882339/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50014905295244882339/50000000000000000000 : ℝ) ≤ (400029124624727/400000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50014905295244882339/50000000000000000000 : ℝ)^32 ≤ (400029124624727/400000000000000 : ℝ)^131 := by
      have hnat : (50014905295244882339 : ℕ)^32*400000000000000^131 ≤ 400029124624727^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014905295244882339 50000000000000000000 400029124624727 400000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400029124624727/400000000000000 : ℝ)) (X := (50014905295244882339/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(364078310327/1162100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(45504663481/145262500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (11621/100000 : ℝ)) (alpha := (364078310327/1162100000000000 : ℝ)) (beta := (45504663481/145262500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (11621/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(364078310327/1162100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(45504663481/145262500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16863/50000 : ℝ) ^ (131/32 : ℝ) ≤ (1168439004532525433/100000000000000000000 : ℝ) := by
    have hpowers : (16863/50000 : ℝ)^131 ≤ (1168439004532525433/100000000000000000000 : ℝ)^32 := by
      have hnat : (16863 : ℕ)^131*100000000000000000000^32 ≤ 1168439004532525433^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16863 50000 1168439004532525433 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16863/50000 : ℝ)) (X := (1168439004532525433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101168439004532525433/100000000000000000000 : ℝ) ≤ (10028416860621809/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (101168439004532525433/100000000000000000000 : ℝ)^32 ≤ (10028416860621809/10000000000000000 : ℝ)^131 := by
      have hnat : (101168439004532525433 : ℕ)^32*10000000000000000^131 ≤ 10028416860621809^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101168439004532525433 100000000000000000000 10028416860621809 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028416860621809/10000000000000000 : ℝ)) (X := (101168439004532525433/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51168439004532525433/50000000000000000000 : ℝ) ≤ (251414669120711/250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (51168439004532525433/50000000000000000000 : ℝ)^32 ≤ (251414669120711/250000000000000 : ℝ)^131 := by
      have hnat : (51168439004532525433 : ℕ)^32*250000000000000^131 ≤ 251414669120711^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51168439004532525433 50000000000000000000 251414669120711 250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251414669120711/250000000000000 : ℝ)) (X := (51168439004532525433/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(2583350965619/306600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(853633460807/102200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (16863/50000 : ℝ)) (alpha := (2583350965619/306600000000000 : ℝ)) (beta := (853633460807/102200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (16863/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(2583350965619/306600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(853633460807/102200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4683079899/10000000000 : ℝ)*X 0 0+(3783606109/10000000000 : ℝ)*X 0 1+(-4491600493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2264656131/5000000000 : ℝ)*X 1 0+(-908723657/2500000000 : ℝ)*X 1 1+(-956758067/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((203252199/500000000 : ℝ)*X 2 0+(4986431359/10000000000 : ℝ)*X 2 1+(779766903/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1828188843/5000000000 : ℝ)*X 0 0+(1348255877/2500000000 : ℝ)*X 0 1+(-965452547/2500000000 : ℝ)*X 0 2+(1828188843/5000000000 : ℝ)*X 1 0+(1348255877/2500000000 : ℝ)*X 1 1+(-965452547/2500000000 : ℝ)*X 1 2+(1828188843/5000000000 : ℝ)*X 2 0+(1348255877/2500000000 : ℝ)*X 2 1+(-965452547/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303026_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-3469593818920339423218361611/581050000000000000000000000 : ℝ) := by norm_num
    linear_combination (741/200000000000 : ℝ)*(base18) + (809/500000000000 : ℝ)*(base23) + (138896318873/1000000000000 : ℝ)*(base39) + (3141/250000000000 : ℝ)*(base43) + (552510493181/1000000000000 : ℝ)*(base49) + (41122261351/125000000000 : ℝ)*(base50) + (28045817879/125000000000 : ℝ)*(base60) + (7521/5000 : ℝ)*(major_s1_0) + (376049996859/250000000000 : ℝ)*(major_s1_1) + (1504200005563/1000000000000 : ℝ)*(major_s1_2) + (248802009123/125000000000 : ℝ)*(sp_s1_0) + (1990416081843/1000000000000 : ℝ)*(sp_s1_1) + (1990416065803/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (398083215997/200000000000 : ℝ)*(f.sum) + (289703768923199629/3562998600000000000000000000000 : ℝ)*base62 + (19761747126979/102200000000000000000000000 : ℝ)*base64 + (37257416673547/72631250000000000000000000 : ℝ)*base66 + (26148009429943/306600000000000000000000000 : ℝ)*base69 + (1394815542075653069/4444575800000000000000000000000 : ℝ)*base71 + (15022384828791/86978000000000000000000000 : ℝ)*base72 + (23757712859743/290525000000000000000000000 : ℝ)*base74 + (104205644170453/434890000000000000000000000 : ℝ)*base76 + (1831582685732998471/25269283450000000000000000000000 : ℝ)*base79 + (5563/1000000000000 : ℝ)*base81 + (5563/1000000000000 : ℝ)*base83 + (5563/1000000000000 : ℝ)*base90 + hcertificate_margin
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
theorem coarse_distinct_p003_b013 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 26 ≤ c.val) (hhi : c.val < 28)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=26 ∨ c=27 := by omega
  rcases hc with rfl|rfl
  · exact collision_c303026 p hpa (by linarith only [hpb]) X hX
  · exact collision_c10027 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 26 ≤ c.val) (hhi : c.val < 28)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b013 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

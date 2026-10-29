-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p011_b007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:03:29.300975+00:00
-- url     : https://prove2.me/submissions/481fc2e2-da8a-41f0-b7dd-6f0794500ec2

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
theorem collision_support_c311015_s0_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1504650791/5000000000 : ℝ)*x 0 + (-6434438501/10000000000 : ℝ)*x 1 + (75731639/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1504650791/5000000000 : ℝ)^73 ≤ (1074088652949/5000000000000 : ℝ)^57 := by
    have hnat : (1504650791 : ℕ)^73*5000000000000^57 ≤ 1074088652949^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504650791 5000000000 1074088652949 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6434438501/10000000000 : ℝ)^73 ≤ (56853768798009/100000000000000 : ℝ)^57 := by
    have hnat : (6434438501 : ℕ)^73*100000000000000^57 ≤ 56853768798009^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6434438501 10000000000 56853768798009 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75731639/250000000 : ℝ)^73 ≤ (10832229061281/50000000000000 : ℝ)^57 := by
    have hnat : (75731639 : ℕ)^73*50000000000000^57 ≤ 10832229061281^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75731639 250000000 10832229061281 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1504650791/5000000000 : ℝ), (-6434438501/10000000000 : ℝ), (75731639/250000000 : ℝ)] ![(1074088652949/5000000000000 : ℝ), (56853768798009/100000000000000 : ℝ), (10832229061281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1504650791/5000000000 : ℝ)|^73 ≤ (1074088652949/5000000000000 : ℝ)^57
        have hw : |(-1504650791/5000000000 : ℝ)|=(1504650791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6434438501/10000000000 : ℝ)|^73 ≤ (56853768798009/100000000000000 : ℝ)^57
        have hw : |(-6434438501/10000000000 : ℝ)|=(6434438501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75731639/250000000 : ℝ)|^73 ≤ (10832229061281/50000000000000 : ℝ)^57
        have hw : |(75731639/250000000 : ℝ)|=(75731639/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (393297797/1000000000 : ℝ)*x 0 + (-955545063/2000000000 : ℝ)*x 1 + (-3997410507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393297797/1000000000 : ℝ)^73 ≤ (30266286005401/100000000000000 : ℝ)^57 := by
    have hnat : (393297797 : ℕ)^73*100000000000000^57 ≤ 30266286005401^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393297797 1000000000 30266286005401 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955545063/2000000000 : ℝ)^73 ≤ (19415474253823/50000000000000 : ℝ)^57 := by
    have hnat : (955545063 : ℕ)^73*50000000000000^57 ≤ 19415474253823^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955545063 2000000000 19415474253823 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3997410507/10000000000 : ℝ)^73 ≤ (30902765479281/100000000000000 : ℝ)^57 := by
    have hnat : (3997410507 : ℕ)^73*100000000000000^57 ≤ 30902765479281^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3997410507 10000000000 30902765479281 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(393297797/1000000000 : ℝ), (-955545063/2000000000 : ℝ), (-3997410507/10000000000 : ℝ)] ![(30266286005401/100000000000000 : ℝ), (19415474253823/50000000000000 : ℝ), (30902765479281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(393297797/1000000000 : ℝ)|^73 ≤ (30266286005401/100000000000000 : ℝ)^57
        have hw : |(393297797/1000000000 : ℝ)|=(393297797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-955545063/2000000000 : ℝ)|^73 ≤ (19415474253823/50000000000000 : ℝ)^57
        have hw : |(-955545063/2000000000 : ℝ)|=(955545063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3997410507/10000000000 : ℝ)|^73 ≤ (30902765479281/100000000000000 : ℝ)^57
        have hw : |(-3997410507/10000000000 : ℝ)|=(3997410507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-747737083/2500000000 : ℝ)*x 0 + (-937088221/1250000000 : ℝ)*x 1 + (399265223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (747737083/2500000000 : ℝ)^73 ≤ (10657063577953/50000000000000 : ℝ)^57 := by
    have hnat : (747737083 : ℕ)^73*50000000000000^57 ≤ 10657063577953^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747737083 2500000000 10657063577953 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (937088221/1250000000 : ℝ)^73 ≤ (69142708211403/100000000000000 : ℝ)^57 := by
    have hnat : (937088221 : ℕ)^73*100000000000000^57 ≤ 69142708211403^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937088221 1250000000 69142708211403 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399265223/2500000000 : ℝ)^73 ≤ (1908632923577/20000000000000 : ℝ)^57 := by
    have hnat : (399265223 : ℕ)^73*20000000000000^57 ≤ 1908632923577^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399265223 2500000000 1908632923577 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-747737083/2500000000 : ℝ), (-937088221/1250000000 : ℝ), (399265223/2500000000 : ℝ)] ![(10657063577953/50000000000000 : ℝ), (69142708211403/100000000000000 : ℝ), (1908632923577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-747737083/2500000000 : ℝ)|^73 ≤ (10657063577953/50000000000000 : ℝ)^57
        have hw : |(-747737083/2500000000 : ℝ)|=(747737083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-937088221/1250000000 : ℝ)|^73 ≤ (69142708211403/100000000000000 : ℝ)^57
        have hw : |(-937088221/1250000000 : ℝ)|=(937088221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(399265223/2500000000 : ℝ)|^73 ≤ (1908632923577/20000000000000 : ℝ)^57
        have hw : |(399265223/2500000000 : ℝ)|=(399265223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4679777991/10000000000 : ℝ)*x 0 + (1258081407/2500000000 : ℝ)*x 1 + (1460894267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4679777991/10000000000 : ℝ)^73 ≤ (7562874532731/20000000000000 : ℝ)^57 := by
    have hnat : (4679777991 : ℕ)^73*20000000000000^57 ≤ 7562874532731^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4679777991 10000000000 7562874532731 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1258081407/2500000000 : ℝ)^73 ≤ (20750315314701/50000000000000 : ℝ)^57 := by
    have hnat : (1258081407 : ℕ)^73*50000000000000^57 ≤ 20750315314701^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258081407 2500000000 20750315314701 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460894267/5000000000 : ℝ)^73 ≤ (20684996686051/100000000000000 : ℝ)^57 := by
    have hnat : (1460894267 : ℕ)^73*100000000000000^57 ≤ 20684996686051^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460894267 5000000000 20684996686051 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4679777991/10000000000 : ℝ), (1258081407/2500000000 : ℝ), (1460894267/5000000000 : ℝ)] ![(7562874532731/20000000000000 : ℝ), (20750315314701/50000000000000 : ℝ), (20684996686051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4679777991/10000000000 : ℝ)|^73 ≤ (7562874532731/20000000000000 : ℝ)^57
        have hw : |(4679777991/10000000000 : ℝ)|=(4679777991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1258081407/2500000000 : ℝ)|^73 ≤ (20750315314701/50000000000000 : ℝ)^57
        have hw : |(1258081407/2500000000 : ℝ)|=(1258081407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1460894267/5000000000 : ℝ)|^73 ≤ (20684996686051/100000000000000 : ℝ)^57
        have hw : |(1460894267/5000000000 : ℝ)|=(1460894267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (898633313/1250000000 : ℝ)*x 0 + (-126945589/312500000 : ℝ)*x 1 + (-158529343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898633313/1250000000 : ℝ)^73 ≤ (65530007971917/100000000000000 : ℝ)^57 := by
    have hnat : (898633313 : ℕ)^73*100000000000000^57 ≤ 65530007971917^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898633313 1250000000 65530007971917 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126945589/312500000 : ℝ)^73 ≤ (15773133339793/50000000000000 : ℝ)^57 := by
    have hnat : (126945589 : ℕ)^73*50000000000000^57 ≤ 15773133339793^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126945589 312500000 15773133339793 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158529343/2500000000 : ℝ)^73 ≤ (1461862666279/50000000000000 : ℝ)^57 := by
    have hnat : (158529343 : ℕ)^73*50000000000000^57 ≤ 1461862666279^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158529343 2500000000 1461862666279 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898633313/1250000000 : ℝ), (-126945589/312500000 : ℝ), (-158529343/2500000000 : ℝ)] ![(65530007971917/100000000000000 : ℝ), (15773133339793/50000000000000 : ℝ), (1461862666279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898633313/1250000000 : ℝ)|^73 ≤ (65530007971917/100000000000000 : ℝ)^57
        have hw : |(898633313/1250000000 : ℝ)|=(898633313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126945589/312500000 : ℝ)|^73 ≤ (15773133339793/50000000000000 : ℝ)^57
        have hw : |(-126945589/312500000 : ℝ)|=(126945589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-158529343/2500000000 : ℝ)|^73 ≤ (1461862666279/50000000000000 : ℝ)^57
        have hw : |(-158529343/2500000000 : ℝ)|=(158529343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (646499659/5000000000 : ℝ)*x 0 + (10861637/2000000000 : ℝ)*x 1 + (9416792051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646499659/5000000000 : ℝ)^73 ≤ (3640762784263/50000000000000 : ℝ)^57 := by
    have hnat : (646499659 : ℕ)^73*50000000000000^57 ≤ 3640762784263^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646499659 5000000000 3640762784263 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10861637/2000000000 : ℝ)^73 ≤ (125613987291/100000000000000 : ℝ)^57 := by
    have hnat : (10861637 : ℕ)^73*100000000000000^57 ≤ 125613987291^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10861637 2000000000 125613987291 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9416792051/10000000000 : ℝ)^73 ≤ (11574107555113/12500000000000 : ℝ)^57 := by
    have hnat : (9416792051 : ℕ)^73*12500000000000^57 ≤ 11574107555113^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9416792051 10000000000 11574107555113 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646499659/5000000000 : ℝ), (10861637/2000000000 : ℝ), (9416792051/10000000000 : ℝ)] ![(3640762784263/50000000000000 : ℝ), (125613987291/100000000000000 : ℝ), (11574107555113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646499659/5000000000 : ℝ)|^73 ≤ (3640762784263/50000000000000 : ℝ)^57
        have hw : |(646499659/5000000000 : ℝ)|=(646499659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10861637/2000000000 : ℝ)|^73 ≤ (125613987291/100000000000000 : ℝ)^57
        have hw : |(10861637/2000000000 : ℝ)|=(10861637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9416792051/10000000000 : ℝ)|^73 ≤ (11574107555113/12500000000000 : ℝ)^57
        have hw : |(9416792051/10000000000 : ℝ)|=(9416792051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-38709077/80000000 : ℝ)*x 0 + (-461686607/1000000000 : ℝ)*x 1 + (401731299/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38709077/80000000 : ℝ)^73 ≤ (3946607836097/10000000000000 : ℝ)^57 := by
    have hnat : (38709077 : ℕ)^73*10000000000000^57 ≤ 3946607836097^57*80000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38709077 80000000 3946607836097 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461686607/1000000000 : ℝ)^73 ≤ (37164557646703/100000000000000 : ℝ)^57 := by
    have hnat : (461686607 : ℕ)^73*100000000000000^57 ≤ 37164557646703^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461686607 1000000000 37164557646703 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401731299/1250000000 : ℝ)^73 ≤ (2336936398153/10000000000000 : ℝ)^57 := by
    have hnat : (401731299 : ℕ)^73*10000000000000^57 ≤ 2336936398153^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401731299 1250000000 2336936398153 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38709077/80000000 : ℝ), (-461686607/1000000000 : ℝ), (401731299/1250000000 : ℝ)] ![(3946607836097/10000000000000 : ℝ), (37164557646703/100000000000000 : ℝ), (2336936398153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38709077/80000000 : ℝ)|^73 ≤ (3946607836097/10000000000000 : ℝ)^57
        have hw : |(-38709077/80000000 : ℝ)|=(38709077/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-461686607/1000000000 : ℝ)|^73 ≤ (37164557646703/100000000000000 : ℝ)^57
        have hw : |(-461686607/1000000000 : ℝ)|=(461686607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401731299/1250000000 : ℝ)|^73 ≤ (2336936398153/10000000000000 : ℝ)^57
        have hw : |(401731299/1250000000 : ℝ)|=(401731299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1779547069/2500000000 : ℝ)*x 0 + (3214910941/10000000000 : ℝ)*x 1 + (949777133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1779547069/2500000000 : ℝ)^73 ≤ (64703730753833/100000000000000 : ℝ)^57 := by
    have hnat : (1779547069 : ℕ)^73*100000000000000^57 ≤ 64703730753833^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779547069 2500000000 64703730753833 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3214910941/10000000000 : ℝ)^73 ≤ (23379240868693/100000000000000 : ℝ)^57 := by
    have hnat : (3214910941 : ℕ)^73*100000000000000^57 ≤ 23379240868693^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3214910941 10000000000 23379240868693 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949777133/5000000000 : ℝ)^73 ≤ (2979257090339/25000000000000 : ℝ)^57 := by
    have hnat : (949777133 : ℕ)^73*25000000000000^57 ≤ 2979257090339^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949777133 5000000000 2979257090339 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1779547069/2500000000 : ℝ), (3214910941/10000000000 : ℝ), (949777133/5000000000 : ℝ)] ![(64703730753833/100000000000000 : ℝ), (23379240868693/100000000000000 : ℝ), (2979257090339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1779547069/2500000000 : ℝ)|^73 ≤ (64703730753833/100000000000000 : ℝ)^57
        have hw : |(1779547069/2500000000 : ℝ)|=(1779547069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3214910941/10000000000 : ℝ)|^73 ≤ (23379240868693/100000000000000 : ℝ)^57
        have hw : |(3214910941/10000000000 : ℝ)|=(3214910941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(949777133/5000000000 : ℝ)|^73 ≤ (2979257090339/25000000000000 : ℝ)^57
        have hw : |(949777133/5000000000 : ℝ)|=(949777133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (220940047/5000000000 : ℝ)*x 0 + (-2461351957/2500000000 : ℝ)*x 1 + (-11464747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220940047/5000000000 : ℝ)^73 ≤ (1840937382653/100000000000000 : ℝ)^57 := by
    have hnat : (220940047 : ℕ)^73*100000000000000^57 ≤ 1840937382653^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220940047 5000000000 1840937382653 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2461351957/2500000000 : ℝ)^73 ≤ (3920977884471/4000000000000 : ℝ)^57 := by
    have hnat : (2461351957 : ℕ)^73*4000000000000^57 ≤ 3920977884471^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2461351957 2500000000 3920977884471 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11464747/2000000000 : ℝ)^73 ≤ (67307744841/50000000000000 : ℝ)^57 := by
    have hnat : (11464747 : ℕ)^73*50000000000000^57 ≤ 67307744841^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11464747 2000000000 67307744841 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220940047/5000000000 : ℝ), (-2461351957/2500000000 : ℝ), (-11464747/2000000000 : ℝ)] ![(1840937382653/100000000000000 : ℝ), (3920977884471/4000000000000 : ℝ), (67307744841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220940047/5000000000 : ℝ)|^73 ≤ (1840937382653/100000000000000 : ℝ)^57
        have hw : |(220940047/5000000000 : ℝ)|=(220940047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2461351957/2500000000 : ℝ)|^73 ≤ (3920977884471/4000000000000 : ℝ)^57
        have hw : |(-2461351957/2500000000 : ℝ)|=(2461351957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11464747/2000000000 : ℝ)|^73 ≤ (67307744841/50000000000000 : ℝ)^57
        have hw : |(-11464747/2000000000 : ℝ)|=(11464747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (15668759/156250000 : ℝ)*x 0 + (7802827/5000000000 : ℝ)*x 1 + (958498459/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15668759/156250000 : ℝ)^73 ≤ (2629200813311/50000000000000 : ℝ)^57 := by
    have hnat : (15668759 : ℕ)^73*50000000000000^57 ≤ 2629200813311^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15668759 156250000 2629200813311 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7802827/5000000000 : ℝ)^73 ≤ (25434974099/100000000000000 : ℝ)^57 := by
    have hnat : (7802827 : ℕ)^73*100000000000000^57 ≤ 25434974099^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7802827 5000000000 25434974099 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958498459/1000000000 : ℝ)^73 ≤ (94716163383721/100000000000000 : ℝ)^57 := by
    have hnat : (958498459 : ℕ)^73*100000000000000^57 ≤ 94716163383721^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958498459 1000000000 94716163383721 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(15668759/156250000 : ℝ), (7802827/5000000000 : ℝ), (958498459/1000000000 : ℝ)] ![(2629200813311/50000000000000 : ℝ), (25434974099/100000000000000 : ℝ), (94716163383721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(15668759/156250000 : ℝ)|^73 ≤ (2629200813311/50000000000000 : ℝ)^57
        have hw : |(15668759/156250000 : ℝ)|=(15668759/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7802827/5000000000 : ℝ)|^73 ≤ (25434974099/100000000000000 : ℝ)^57
        have hw : |(7802827/5000000000 : ℝ)|=(7802827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958498459/1000000000 : ℝ)|^73 ≤ (94716163383721/100000000000000 : ℝ)^57
        have hw : |(958498459/1000000000 : ℝ)|=(958498459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-733176737/5000000000 : ℝ)*x 0 + (-1943148073/2500000000 : ℝ)*x 1 + (2737287543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733176737/5000000000 : ℝ)^73 ≤ (427730687081/5000000000000 : ℝ)^57 := by
    have hnat : (733176737 : ℕ)^73*5000000000000^57 ≤ 427730687081^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733176737 5000000000 427730687081 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1943148073/2500000000 : ℝ)^73 ≤ (1810454225749/2500000000000 : ℝ)^57 := by
    have hnat : (1943148073 : ℕ)^73*2500000000000^57 ≤ 1810454225749^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943148073 2500000000 1810454225749 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737287543/10000000000 : ℝ)^73 ≤ (19027217210797/100000000000000 : ℝ)^57 := by
    have hnat : (2737287543 : ℕ)^73*100000000000000^57 ≤ 19027217210797^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737287543 10000000000 19027217210797 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-733176737/5000000000 : ℝ), (-1943148073/2500000000 : ℝ), (2737287543/10000000000 : ℝ)] ![(427730687081/5000000000000 : ℝ), (1810454225749/2500000000000 : ℝ), (19027217210797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-733176737/5000000000 : ℝ)|^73 ≤ (427730687081/5000000000000 : ℝ)^57
        have hw : |(-733176737/5000000000 : ℝ)|=(733176737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1943148073/2500000000 : ℝ)|^73 ≤ (1810454225749/2500000000000 : ℝ)^57
        have hw : |(-1943148073/2500000000 : ℝ)|=(1943148073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737287543/10000000000 : ℝ)|^73 ≤ (19027217210797/100000000000000 : ℝ)^57
        have hw : |(2737287543/10000000000 : ℝ)|=(2737287543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3543221357/5000000000 : ℝ)*x 0 + (321921569/1250000000 : ℝ)*x 1 + (2628892169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3543221357/5000000000 : ℝ)^73 ≤ (16083599322413/25000000000000 : ℝ)^57 := by
    have hnat : (3543221357 : ℕ)^73*25000000000000^57 ≤ 16083599322413^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3543221357 5000000000 16083599322413 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321921569/1250000000 : ℝ)^73 ≤ (8798970042059/50000000000000 : ℝ)^57 := by
    have hnat : (321921569 : ℕ)^73*50000000000000^57 ≤ 8798970042059^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321921569 1250000000 8798970042059 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628892169/10000000000 : ℝ)^73 ≤ (282307228287/1562500000000 : ℝ)^57 := by
    have hnat : (2628892169 : ℕ)^73*1562500000000^57 ≤ 282307228287^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628892169 10000000000 282307228287 1562500000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3543221357/5000000000 : ℝ), (321921569/1250000000 : ℝ), (2628892169/10000000000 : ℝ)] ![(16083599322413/25000000000000 : ℝ), (8798970042059/50000000000000 : ℝ), (282307228287/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3543221357/5000000000 : ℝ)|^73 ≤ (16083599322413/25000000000000 : ℝ)^57
        have hw : |(3543221357/5000000000 : ℝ)|=(3543221357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321921569/1250000000 : ℝ)|^73 ≤ (8798970042059/50000000000000 : ℝ)^57
        have hw : |(321921569/1250000000 : ℝ)|=(321921569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628892169/10000000000 : ℝ)|^73 ≤ (282307228287/1562500000000 : ℝ)^57
        have hw : |(2628892169/10000000000 : ℝ)|=(2628892169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s0_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (649847933/2500000000 : ℝ)*x 0 + (-4846961163/10000000000 : ℝ)*x 1 + (-16061693/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649847933/2500000000 : ℝ)^73 ≤ (17808412312923/100000000000000 : ℝ)^57 := by
    have hnat : (649847933 : ℕ)^73*100000000000000^57 ≤ 17808412312923^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649847933 2500000000 17808412312923 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4846961163/10000000000 : ℝ)^73 ≤ (4944134775113/12500000000000 : ℝ)^57 := by
    have hnat : (4846961163 : ℕ)^73*12500000000000^57 ≤ 4944134775113^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4846961163 10000000000 4944134775113 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16061693/31250000 : ℝ)^73 ≤ (5329813683189/12500000000000 : ℝ)^57 := by
    have hnat : (16061693 : ℕ)^73*12500000000000^57 ≤ 5329813683189^57*31250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16061693 31250000 5329813683189 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649847933/2500000000 : ℝ), (-4846961163/10000000000 : ℝ), (-16061693/31250000 : ℝ)] ![(17808412312923/100000000000000 : ℝ), (4944134775113/12500000000000 : ℝ), (5329813683189/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649847933/2500000000 : ℝ)|^73 ≤ (17808412312923/100000000000000 : ℝ)^57
        have hw : |(649847933/2500000000 : ℝ)|=(649847933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4846961163/10000000000 : ℝ)|^73 ≤ (4944134775113/12500000000000 : ℝ)^57
        have hw : |(-4846961163/10000000000 : ℝ)|=(4846961163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16061693/31250000 : ℝ)|^73 ≤ (5329813683189/12500000000000 : ℝ)^57
        have hw : |(-16061693/31250000 : ℝ)|=(16061693/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1653324871/5000000000 : ℝ)*x 0 + (-5152815287/10000000000 : ℝ)*x 1 + (131445617/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1653324871/5000000000 : ℝ)^73 ≤ (12118521060257/50000000000000 : ℝ)^57 := by
    have hnat : (1653324871 : ℕ)^73*50000000000000^57 ≤ 12118521060257^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653324871 5000000000 12118521060257 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152815287/10000000000 : ℝ)^73 ≤ (21388729390007/50000000000000 : ℝ)^57 := by
    have hnat : (5152815287 : ℕ)^73*50000000000000^57 ≤ 21388729390007^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152815287 10000000000 21388729390007 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131445617/312500000 : ℝ)^73 ≤ (32985499090229/100000000000000 : ℝ)^57 := by
    have hnat : (131445617 : ℕ)^73*100000000000000^57 ≤ 32985499090229^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131445617 312500000 32985499090229 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1653324871/5000000000 : ℝ), (-5152815287/10000000000 : ℝ), (131445617/312500000 : ℝ)] ![(12118521060257/50000000000000 : ℝ), (21388729390007/50000000000000 : ℝ), (32985499090229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1653324871/5000000000 : ℝ)|^73 ≤ (12118521060257/50000000000000 : ℝ)^57
        have hw : |(-1653324871/5000000000 : ℝ)|=(1653324871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5152815287/10000000000 : ℝ)|^73 ≤ (21388729390007/50000000000000 : ℝ)^57
        have hw : |(-5152815287/10000000000 : ℝ)|=(5152815287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131445617/312500000 : ℝ)|^73 ≤ (32985499090229/100000000000000 : ℝ)^57
        have hw : |(131445617/312500000 : ℝ)|=(131445617/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2696732209/5000000000 : ℝ)*x 0 + (873891039/2500000000 : ℝ)*x 1 + (3765216677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696732209/5000000000 : ℝ)^73 ≤ (22676323727323/50000000000000 : ℝ)^57 := by
    have hnat : (2696732209 : ℕ)^73*50000000000000^57 ≤ 22676323727323^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696732209 5000000000 22676323727323 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873891039/2500000000 : ℝ)^73 ≤ (26024462966519/100000000000000 : ℝ)^57 := by
    have hnat : (873891039 : ℕ)^73*100000000000000^57 ≤ 26024462966519^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873891039 2500000000 26024462966519 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3765216677/10000000000 : ℝ)^73 ≤ (28622889566923/100000000000000 : ℝ)^57 := by
    have hnat : (3765216677 : ℕ)^73*100000000000000^57 ≤ 28622889566923^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3765216677 10000000000 28622889566923 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696732209/5000000000 : ℝ), (873891039/2500000000 : ℝ), (3765216677/10000000000 : ℝ)] ![(22676323727323/50000000000000 : ℝ), (26024462966519/100000000000000 : ℝ), (28622889566923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696732209/5000000000 : ℝ)|^73 ≤ (22676323727323/50000000000000 : ℝ)^57
        have hw : |(2696732209/5000000000 : ℝ)|=(2696732209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873891039/2500000000 : ℝ)|^73 ≤ (26024462966519/100000000000000 : ℝ)^57
        have hw : |(873891039/2500000000 : ℝ)|=(873891039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3765216677/10000000000 : ℝ)|^73 ≤ (28622889566923/100000000000000 : ℝ)^57
        have hw : |(3765216677/10000000000 : ℝ)|=(3765216677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s1_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1732168097/5000000000 : ℝ)*x 0 + (-4352095381/10000000000 : ℝ)*x 1 + (-974414001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1732168097/5000000000 : ℝ)^73 ≤ (25727084103577/100000000000000 : ℝ)^57 := by
    have hnat : (1732168097 : ℕ)^73*100000000000000^57 ≤ 25727084103577^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732168097 5000000000 25727084103577 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4352095381/10000000000 : ℝ)^73 ≤ (17228617039989/50000000000000 : ℝ)^57 := by
    have hnat : (4352095381 : ℕ)^73*50000000000000^57 ≤ 17228617039989^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352095381 10000000000 17228617039989 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974414001/2000000000 : ℝ)^73 ≤ (19907840904897/50000000000000 : ℝ)^57 := by
    have hnat : (974414001 : ℕ)^73*50000000000000^57 ≤ 19907840904897^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974414001 2000000000 19907840904897 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1732168097/5000000000 : ℝ), (-4352095381/10000000000 : ℝ), (-974414001/2000000000 : ℝ)] ![(25727084103577/100000000000000 : ℝ), (17228617039989/50000000000000 : ℝ), (19907840904897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1732168097/5000000000 : ℝ)|^73 ≤ (25727084103577/100000000000000 : ℝ)^57
        have hw : |(1732168097/5000000000 : ℝ)|=(1732168097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4352095381/10000000000 : ℝ)|^73 ≤ (17228617039989/50000000000000 : ℝ)^57
        have hw : |(-4352095381/10000000000 : ℝ)|=(4352095381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974414001/2000000000 : ℝ)|^73 ≤ (19907840904897/50000000000000 : ℝ)^57
        have hw : |(-974414001/2000000000 : ℝ)|=(974414001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311015_s1_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (512269029/2500000000 : ℝ)*x 0 + (-773631729/10000000000 : ℝ)*x 1 + (4326929369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512269029/2500000000 : ℝ)^73 ≤ (3282851579139/25000000000000 : ℝ)^57 := by
    have hnat : (512269029 : ℕ)^73*25000000000000^57 ≤ 3282851579139^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512269029 2500000000 3282851579139 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773631729/10000000000 : ℝ)^73 ≤ (3771758638873/100000000000000 : ℝ)^57 := by
    have hnat : (773631729 : ℕ)^73*100000000000000^57 ≤ 3771758638873^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773631729 10000000000 3771758638873 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326929369/5000000000 : ℝ)^73 ≤ (20774208759561/25000000000000 : ℝ)^57 := by
    have hnat : (4326929369 : ℕ)^73*25000000000000^57 ≤ 20774208759561^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326929369 5000000000 20774208759561 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(512269029/2500000000 : ℝ), (-773631729/10000000000 : ℝ), (4326929369/5000000000 : ℝ)] ![(3282851579139/25000000000000 : ℝ), (3771758638873/100000000000000 : ℝ), (20774208759561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(512269029/2500000000 : ℝ)|^73 ≤ (3282851579139/25000000000000 : ℝ)^57
        have hw : |(512269029/2500000000 : ℝ)|=(512269029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-773631729/10000000000 : ℝ)|^73 ≤ (3771758638873/100000000000000 : ℝ)^57
        have hw : |(-773631729/10000000000 : ℝ)|=(773631729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326929369/5000000000 : ℝ)|^73 ≤ (20774208759561/25000000000000 : ℝ)^57
        have hw : |(4326929369/5000000000 : ℝ)|=(4326929369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311015 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : False := by
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
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (89829/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1504650791/5000000000 : ℝ)*X 0 0+(-6434438501/10000000000 : ℝ)*X 0 1+(75731639/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((393297797/1000000000 : ℝ)*X 2 0+(-955545063/2000000000 : ℝ)*X 2 1+(-3997410507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-747737083/2500000000 : ℝ)*X 0 0+(-937088221/1250000000 : ℝ)*X 0 1+(399265223/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4679777991/10000000000 : ℝ)*X 1 0+(1258081407/2500000000 : ℝ)*X 1 1+(1460894267/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((898633313/1250000000 : ℝ)*X 2 0+(-126945589/312500000 : ℝ)*X 2 1+(-158529343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((646499659/5000000000 : ℝ)*X 0 0+(10861637/2000000000 : ℝ)*X 0 1+(9416792051/10000000000 : ℝ)*X 0 2+(646499659/5000000000 : ℝ)*X 1 0+(10861637/2000000000 : ℝ)*X 1 1+(9416792051/10000000000 : ℝ)*X 1 2+(646499659/5000000000 : ℝ)*X 2 0+(10861637/2000000000 : ℝ)*X 2 1+(9416792051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-38709077/80000000 : ℝ)*X 0 0+(-461686607/1000000000 : ℝ)*X 0 1+(401731299/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1779547069/2500000000 : ℝ)*X 1 0+(3214910941/10000000000 : ℝ)*X 1 1+(949777133/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((220940047/5000000000 : ℝ)*X 2 0+(-2461351957/2500000000 : ℝ)*X 2 1+(-11464747/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((15668759/156250000 : ℝ)*X 0 0+(7802827/5000000000 : ℝ)*X 0 1+(958498459/1000000000 : ℝ)*X 0 2+(15668759/156250000 : ℝ)*X 1 0+(7802827/5000000000 : ℝ)*X 1 1+(958498459/1000000000 : ℝ)*X 1 2+(15668759/156250000 : ℝ)*X 2 0+(7802827/5000000000 : ℝ)*X 2 1+(958498459/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-733176737/5000000000 : ℝ)*X 0 0+(-1943148073/2500000000 : ℝ)*X 0 1+(2737287543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3543221357/5000000000 : ℝ)*X 1 0+(321921569/1250000000 : ℝ)*X 1 1+(2628892169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((649847933/2500000000 : ℝ)*X 2 0+(-4846961163/10000000000 : ℝ)*X 2 1+(-16061693/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((38553/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38553/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (81567558484585079418201/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180067293811/500000000000 : ℝ)*(base3) + (33777714927/62500000000 : ℝ)*(base7) + (1704643/500000000000 : ℝ)*(base40) + (364363930393/1000000000000 : ℝ)*(base43) + (221711495167/500000000000 : ℝ)*(base50) + (690291954867/500000000000 : ℝ)*(base54) + (550121/500000000000 : ℝ)*(base60) + (1972628053181/1000000000000 : ℝ)*(major_s0_0) + (402066030697/250000000000 : ℝ)*(major_s0_1) + (74005517931/125000000000 : ℝ)*(major_s0_2) + (7164031/500000000000 : ℝ)*(sp_s0_2) + (64280053807/31250000000 : ℝ)*(sp_s0_7) + (2781460239839/1000000000000 : ℝ)*(sp_s0_8) + (676363484029/1000000000000 : ℝ)*(sp_s0_9) + (1200275058523/1000000000000 : ℝ)*(f.failure) + (2421325652217/1000000000000 : ℝ)*(f.sum) + (19989944819157/100000000000000000000000000 : ℝ)*base63 + (12689074910543/78125000000000000000000000 : ℝ)*base64 + (3595894395659/156250000000000000000000000 : ℝ)*base67 + (50092006760601/250000000000000000000000000 : ℝ)*base68 + (2170681662883741/10000000000000000000000000000 : ℝ)*base71 + (287632700453793/625000000000000000000000000 : ℝ)*base72 + (364668251033013/500000000000000000000000000 : ℝ)*base74 + (1451537219486649/2000000000000000000000000000 : ℝ)*base77 + (311329606871157/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (9501/25000000000000000 : ℝ)*base87 + (9501/25000000000000000 : ℝ)*base89 + (15499/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-8521/12500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-8521/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19074212072549831293797/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40222540977/500000000000 : ℝ)*(base3) + (46669443177/200000000000 : ℝ)*(base7) + (281009242841/500000000000 : ℝ)*(base33) + (360619371047/1000000000000 : ℝ)*(base40) + (654677769203/500000000000 : ℝ)*(base54) + (455041/500000000000 : ℝ)*(base60) + (1353742482451/1000000000000 : ℝ)*(major_s0_0) + (1915760968133/1000000000000 : ℝ)*(major_s0_1) + (606405429727/1000000000000 : ℝ)*(major_s0_2) + (55539731/500000000000 : ℝ)*(sp_s0_13) + (2526104921307/1000000000000 : ℝ)*(sp_s0_14) + (2044531517579/1000000000000 : ℝ)*(sp_s0_15) + (654730897219/1000000000000 : ℝ)*(sp_s0_16) + (9108945697/1000000000000 : ℝ)*(sp_s0_20) + (1165673429633/1000000000000 : ℝ)*(f.failure) + (2526104921307/1000000000000 : ℝ)*(f.sum) + (438122317024087/1000000000000000000000000000 : ℝ)*base62 + (360998639196069/625000000000000000000000000 : ℝ)*base65 + (400236820419649/625000000000000000000000000 : ℝ)*base66 + (2052438311623117/2000000000000000000000000000 : ℝ)*base68 + (5970765115554499/10000000000000000000000000000 : ℝ)*base71 + (526292324889103/625000000000000000000000000 : ℝ)*base72 + (909075453025057/2000000000000000000000000000 : ℝ)*base74 + (229187048283479/2000000000000000000000000000 : ℝ)*base77 + (162077550155313/156250000000000000000000000 : ℝ)*base78 + (6071/25000000000000000 : ℝ)*base87 + (6071/25000000000000000 : ℝ)*base89 + (6071/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72377/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72377/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30701511163302846956817/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (349397192047/125000000000 : ℝ)*(base3) + (283582162633/250000000000 : ℝ)*(base7) + (297553/1000000000000 : ℝ)*(base33) + (47271378759/62500000000 : ℝ)*(base40) + (291470815359/200000000000 : ℝ)*(base50) + (545914325871/200000000000 : ℝ)*(major_s0_0) + (2729571926907/1000000000000 : ℝ)*(major_s0_1) + (2729571926907/1000000000000 : ℝ)*(major_s0_2) + (79017/200000000000 : ℝ)*(sp_s0_0) + (28109/2000000000 : ℝ)*(sp_s0_2) + (21444773/1000000000000 : ℝ)*(sp_s0_15) + (623797694091/200000000000 : ℝ)*(sp_s0_21) + (5914144659591/1000000000000 : ℝ)*(sp_s0_22) + (3118974513487/1000000000000 : ℝ)*(sp_s0_23) + (415212221461/250000000000 : ℝ)*(f.failure) + (155949443277/50000000000 : ℝ)*(f.sum) + (122443243/500000000000000000000 : ℝ)*base62 + (222495621127029/625000000000000000000000000 : ℝ)*base65 + (403549073247971/625000000000000000000000000 : ℝ)*base66 + (126172906172897/2000000000000000000000000000 : ℝ)*base68 + (2571630448201061/10000000000000000000000000000 : ℝ)*base70 + (36726561291863/125000000000000000000000000 : ℝ)*base72 + (503791744972897/2000000000000000000000000000 : ℝ)*base75 + (61784822590659/400000000000000000000000000 : ℝ)*base77 + (66942259166143/312500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (6893/6250000000000000 : ℝ)*base86 + (643/6250000000000000 : ℝ)*base88 + (643/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (38553/50000 : ℝ) ^ (71/16 : ℝ) ≤ (788667202560418061/2500000000000000000 : ℝ) := by
    have hpowers : (38553/50000 : ℝ)^71 ≤ (788667202560418061/2500000000000000000 : ℝ)^16 := by
      have hnat : (38553 : ℕ)^71*2500000000000000000^16 ≤ 788667202560418061^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38553 50000 788667202560418061 2500000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38553/50000 : ℝ)) (X := (788667202560418061/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3288667202560418061/2500000000000000000 : ℝ) ≤ (10637385813679833/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3288667202560418061/2500000000000000000 : ℝ)^16 ≤ (10637385813679833/10000000000000000 : ℝ)^71 := by
      have hnat : (3288667202560418061 : ℕ)^16*10000000000000000^71 ≤ 10637385813679833^71*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3288667202560418061 2500000000000000000 10637385813679833 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10637385813679833/10000000000000000 : ℝ)) (X := (3288667202560418061/2500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2038667202560418061/1250000000000000000 : ℝ) ≤ (11165366268647199/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2038667202560418061/1250000000000000000 : ℝ)^16 ≤ (11165366268647199/10000000000000000 : ℝ)^71 := by
      have hnat : (2038667202560418061 : ℕ)^16*10000000000000000^71 ≤ 11165366268647199^71*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2038667202560418061 1250000000000000000 11165366268647199 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11165366268647199/10000000000000000 : ℝ)) (X := (2038667202560418061/1250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(637385813679833/7710600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(87996742494561/1285100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (38553/50000 : ℝ)) (alpha := (637385813679833/7710600000000000 : ℝ)) (beta := (87996742494561/1285100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38553/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(637385813679833/7710600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(87996742494561/1285100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8521/12500 : ℝ) ^ (71/16 : ℝ) ≤ (730421742108775299/4000000000000000000 : ℝ) := by
    have hpowers : (8521/12500 : ℝ)^71 ≤ (730421742108775299/4000000000000000000 : ℝ)^16 := by
      have hnat : (8521 : ℕ)^71*4000000000000000000^16 ≤ 730421742108775299^16*12500^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8521 12500 730421742108775299 4000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8521/12500 : ℝ)) (X := (730421742108775299/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (4730421742108775299/4000000000000000000 : ℝ) ≤ (649074632486677/625000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (4730421742108775299/4000000000000000000 : ℝ)^16 ≤ (649074632486677/625000000000000 : ℝ)^71 := by
      have hnat : (4730421742108775299 : ℕ)^16*625000000000000^71 ≤ 649074632486677^71*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4730421742108775299 4000000000000000000 649074632486677 625000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (649074632486677/625000000000000 : ℝ)) (X := (4730421742108775299/4000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2730421742108775299/2000000000000000000 : ℝ) ≤ (1340841859225997/1250000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2730421742108775299/2000000000000000000 : ℝ)^16 ≤ (1340841859225997/1250000000000000 : ℝ)^71 := by
      have hnat : (2730421742108775299 : ℕ)^16*1250000000000000^71 ≤ 1340841859225997^71*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2730421742108775299 2000000000000000000 1340841859225997 1250000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1340841859225997/1250000000000000 : ℝ)) (X := (2730421742108775299/2000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(24074632486677/426050000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(42692594252643/852100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (8521/12500 : ℝ)) (alpha := (24074632486677/426050000000000 : ℝ)) (beta := (42692594252643/852100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (8521/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(24074632486677/426050000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(42692594252643/852100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (72377/100000 : ℝ) ^ (71/16 : ℝ) ≤ (23821963999142580717/100000000000000000000 : ℝ) := by
    have hpowers : (72377/100000 : ℝ)^71 ≤ (23821963999142580717/100000000000000000000 : ℝ)^16 := by
      have hnat : (72377 : ℕ)^71*100000000000000000000^16 ≤ 23821963999142580717^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72377 100000 23821963999142580717 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72377/100000 : ℝ)) (X := (23821963999142580717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (123821963999142580717/100000000000000000000 : ℝ) ≤ (10493301588136557/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (123821963999142580717/100000000000000000000 : ℝ)^16 ≤ (10493301588136557/10000000000000000 : ℝ)^71 := by
      have hnat : (123821963999142580717 : ℕ)^16*10000000000000000^71 ≤ 10493301588136557^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123821963999142580717 100000000000000000000 10493301588136557 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10493301588136557/10000000000000000 : ℝ)) (X := (123821963999142580717/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (73821963999142580717/50000000000000000000 : ℝ) ≤ (5458874315051301/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (73821963999142580717/50000000000000000000 : ℝ)^16 ≤ (5458874315051301/5000000000000000 : ℝ)^71 := by
      have hnat : (73821963999142580717 : ℕ)^16*5000000000000000^71 ≤ 5458874315051301^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73821963999142580717 50000000000000000000 5458874315051301 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5458874315051301/5000000000000000 : ℝ)) (X := (73821963999142580717/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(493301588136557/7237700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(84889408393209/1447540000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (72377/100000 : ℝ)) (alpha := (493301588136557/7237700000000000 : ℝ)) (beta := (84889408393209/1447540000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (72377/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(493301588136557/7237700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(84889408393209/1447540000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1653324871/5000000000 : ℝ)*X 0 0+(-5152815287/10000000000 : ℝ)*X 0 1+(131445617/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2696732209/5000000000 : ℝ)*X 1 0+(873891039/2500000000 : ℝ)*X 1 1+(3765216677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1732168097/5000000000 : ℝ)*X 2 0+(-4352095381/10000000000 : ℝ)*X 2 1+(-974414001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((512269029/2500000000 : ℝ)*X 0 0+(-773631729/10000000000 : ℝ)*X 0 1+(4326929369/5000000000 : ℝ)*X 0 2+(512269029/2500000000 : ℝ)*X 1 0+(-773631729/10000000000 : ℝ)*X 1 1+(4326929369/5000000000 : ℝ)*X 1 2+(512269029/2500000000 : ℝ)*X 2 0+(-773631729/10000000000 : ℝ)*X 2 1+(4326929369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311015_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-85761/12500 : ℝ) < ((-41087/25000 : ℝ)*P 0+(-41087/25000 : ℝ)*P 1+(-41087/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-85761/12500 : ℝ) < (-10262787733308012025342440591/1512477500000000000000000000 : ℝ) := by norm_num
    linear_combination (988793463177/1000000000000 : ℝ)*(base3) + (68511/1000000000000 : ℝ)*(base13) + (5491/100000000000 : ℝ)*(base22) + (59727/1000000000000 : ℝ)*(base24) + (10059/500000000000 : ℝ)*(base39) + (104479589631/200000000000 : ℝ)*(base40) + (15295019521/20000000000 : ℝ)*(base50) + (380766602809/1000000000000 : ℝ)*(base59) + (41087/25000 : ℝ)*(major_s1_0) + (41087/25000 : ℝ)*(major_s1_1) + (41087/25000 : ℝ)*(major_s1_2) + (45236099589/20000000000 : ℝ)*(sp_s1_0) + (3250598511137/1000000000000 : ℝ)*(sp_s1_1) + (2261804933323/1000000000000 : ℝ)*(sp_s1_2) + (11206536823/1000000000000 : ℝ)*(sp_s1_6) + (2261805047961/1000000000000 : ℝ)*(f.sum) + (56946345283892433/192726380312500000000000000000 : ℝ)*base62 + (94452171638891/723770000000000000000000000 : ℝ)*base64 + (22228346726327/42605000000000000000000000 : ℝ)*base66 + (102694476520641/361885000000000000000000000 : ℝ)*base69 + (4130726178730019/30832602000000000000000000000 : ℝ)*base71 + (280247819733/710000000000000000000000 : ℝ)*base72 + (4555309275973/8521000000000000000000000 : ℝ)*base74 + (14685819961/213000000000000000000000 : ℝ)*base76 + (7882417610900169/6049910000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c311016_s0_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-314818457/625000000 : ℝ)*x 0 + (27393591/100000000 : ℝ)*x 1 + (-4832626241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (314818457/625000000 : ℝ)^73 ≤ (1038775332917/2500000000000 : ℝ)^57 := by
    have hnat : (314818457 : ℕ)^73*2500000000000^57 ≤ 1038775332917^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314818457 625000000 1038775332917 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27393591/100000000 : ℝ)^73 ≤ (9522830409023/50000000000000 : ℝ)^57 := by
    have hnat : (27393591 : ℕ)^73*50000000000000^57 ≤ 9522830409023^57*100000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27393591 100000000 9522830409023 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4832626241/10000000000 : ℝ)^73 ≤ (1576133033979/4000000000000 : ℝ)^57 := by
    have hnat : (4832626241 : ℕ)^73*4000000000000^57 ≤ 1576133033979^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832626241 10000000000 1576133033979 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-314818457/625000000 : ℝ), (27393591/100000000 : ℝ), (-4832626241/10000000000 : ℝ)] ![(1038775332917/2500000000000 : ℝ), (9522830409023/50000000000000 : ℝ), (1576133033979/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-314818457/625000000 : ℝ)|^73 ≤ (1038775332917/2500000000000 : ℝ)^57
        have hw : |(-314818457/625000000 : ℝ)|=(314818457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27393591/100000000 : ℝ)|^73 ≤ (9522830409023/50000000000000 : ℝ)^57
        have hw : |(27393591/100000000 : ℝ)|=(27393591/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4832626241/10000000000 : ℝ)|^73 ≤ (1576133033979/4000000000000 : ℝ)^57
        have hw : |(-4832626241/10000000000 : ℝ)|=(4832626241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311016_s0_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (75537291/156250000 : ℝ)*x 0 + (-817462493/2500000000 : ℝ)*x 1 + (-2285197777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75537291/156250000 : ℝ)^73 ≤ (39421709300559/100000000000000 : ℝ)^57 := by
    have hnat : (75537291 : ℕ)^73*100000000000000^57 ≤ 39421709300559^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75537291 156250000 39421709300559 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (817462493/2500000000 : ℝ)^73 ≤ (11946066838637/50000000000000 : ℝ)^57 := by
    have hnat : (817462493 : ℕ)^73*50000000000000^57 ≤ 11946066838637^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817462493 2500000000 11946066838637 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285197777/5000000000 : ℝ)^73 ≤ (18343078506303/50000000000000 : ℝ)^57 := by
    have hnat : (2285197777 : ℕ)^73*50000000000000^57 ≤ 18343078506303^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285197777 5000000000 18343078506303 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(75537291/156250000 : ℝ), (-817462493/2500000000 : ℝ), (-2285197777/5000000000 : ℝ)] ![(39421709300559/100000000000000 : ℝ), (11946066838637/50000000000000 : ℝ), (18343078506303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(75537291/156250000 : ℝ)|^73 ≤ (39421709300559/100000000000000 : ℝ)^57
        have hw : |(75537291/156250000 : ℝ)|=(75537291/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-817462493/2500000000 : ℝ)|^73 ≤ (11946066838637/50000000000000 : ℝ)^57
        have hw : |(-817462493/2500000000 : ℝ)|=(817462493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2285197777/5000000000 : ℝ)|^73 ≤ (18343078506303/50000000000000 : ℝ)^57
        have hw : |(-2285197777/5000000000 : ℝ)|=(2285197777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311016_s0_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3417384191/10000000000 : ℝ)*x 0 + (2947792719/5000000000 : ℝ)*x 1 + (3269557437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3417384191/10000000000 : ℝ)^73 ≤ (25281383656231/100000000000000 : ℝ)^57 := by
    have hnat : (3417384191 : ℕ)^73*100000000000000^57 ≤ 25281383656231^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3417384191 10000000000 25281383656231 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2947792719/5000000000 : ℝ)^73 ≤ (25414610056451/50000000000000 : ℝ)^57 := by
    have hnat : (2947792719 : ℕ)^73*50000000000000^57 ≤ 25414610056451^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947792719 5000000000 25414610056451 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3269557437/10000000000 : ℝ)^73 ≤ (11944698109543/50000000000000 : ℝ)^57 := by
    have hnat : (3269557437 : ℕ)^73*50000000000000^57 ≤ 11944698109543^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3269557437 10000000000 11944698109543 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3417384191/10000000000 : ℝ), (2947792719/5000000000 : ℝ), (3269557437/10000000000 : ℝ)] ![(25281383656231/100000000000000 : ℝ), (25414610056451/50000000000000 : ℝ), (11944698109543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3417384191/10000000000 : ℝ)|^73 ≤ (25281383656231/100000000000000 : ℝ)^57
        have hw : |(3417384191/10000000000 : ℝ)|=(3417384191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2947792719/5000000000 : ℝ)|^73 ≤ (25414610056451/50000000000000 : ℝ)^57
        have hw : |(2947792719/5000000000 : ℝ)|=(2947792719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3269557437/10000000000 : ℝ)|^73 ≤ (11944698109543/50000000000000 : ℝ)^57
        have hw : |(3269557437/10000000000 : ℝ)|=(3269557437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311016_s0_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2669854609/10000000000 : ℝ)*x 0 + (5815233893/10000000000 : ℝ)*x 1 + (-3180003/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2669854609/10000000000 : ℝ)^73 ≤ (575906128377/3125000000000 : ℝ)^57 := by
    have hnat : (2669854609 : ℕ)^73*3125000000000^57 ≤ 575906128377^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669854609 10000000000 575906128377 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5815233893/10000000000 : ℝ)^73 ≤ (6242963509143/12500000000000 : ℝ)^57 := by
    have hnat : (5815233893 : ℕ)^73*12500000000000^57 ≤ 6242963509143^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5815233893 10000000000 6242963509143 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3180003/7812500 : ℝ)^73 ≤ (1581364790537/5000000000000 : ℝ)^57 := by
    have hnat : (3180003 : ℕ)^73*5000000000000^57 ≤ 1581364790537^57*7812500^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3180003 7812500 1581364790537 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2669854609/10000000000 : ℝ), (5815233893/10000000000 : ℝ), (-3180003/7812500 : ℝ)] ![(575906128377/3125000000000 : ℝ), (6242963509143/12500000000000 : ℝ), (1581364790537/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2669854609/10000000000 : ℝ)|^73 ≤ (575906128377/3125000000000 : ℝ)^57
        have hw : |(2669854609/10000000000 : ℝ)|=(2669854609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5815233893/10000000000 : ℝ)|^73 ≤ (6242963509143/12500000000000 : ℝ)^57
        have hw : |(5815233893/10000000000 : ℝ)|=(5815233893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3180003/7812500 : ℝ)|^73 ≤ (1581364790537/5000000000000 : ℝ)^57
        have hw : |(-3180003/7812500 : ℝ)|=(3180003/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311016 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-314818457/625000000 : ℝ)*X 0 0+(27393591/100000000 : ℝ)*X 0 1+(-4832626241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311016_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((75537291/156250000 : ℝ)*X 1 0+(-817462493/2500000000 : ℝ)*X 1 1+(-2285197777/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311016_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3417384191/10000000000 : ℝ)*X 2 0+(2947792719/5000000000 : ℝ)*X 2 1+(3269557437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311016_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2669854609/10000000000 : ℝ)*X 0 0+(5815233893/10000000000 : ℝ)*X 0 1+(-3180003/7812500 : ℝ)*X 0 2+(2669854609/10000000000 : ℝ)*X 1 0+(5815233893/10000000000 : ℝ)*X 1 1+(-3180003/7812500 : ℝ)*X 1 2+(2669854609/10000000000 : ℝ)*X 2 0+(5815233893/10000000000 : ℝ)*X 2 1+(-3180003/7812500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311016_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-85761/12500 : ℝ) < ((-41087/25000 : ℝ)*P 0+(-41087/25000 : ℝ)*P 1+(-41087/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-85761/12500 : ℝ) < (-68176807975736772492777/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (708751/1000000000000 : ℝ)*(base1) + (21117/125000000000 : ℝ)*(base12) + (47583/500000000000 : ℝ)*(base15) + (1482399/1000000000000 : ℝ)*(base23) + (139628759/10000000000 : ℝ)*(base39) + (322023175737/1000000000000 : ℝ)*(base50) + (51118829873/200000000000 : ℝ)*(base59) + (1387/5000000000 : ℝ)*(base60) + (41087/25000 : ℝ)*(major_s0_0) + (41087/25000 : ℝ)*(major_s0_1) + (41087/25000 : ℝ)*(major_s0_2) + (2272560805671/1000000000000 : ℝ)*(sp_s0_0) + (227256017069/100000000000 : ℝ)*(sp_s0_1) + (2272558783457/1000000000000 : ℝ)*(sp_s0_2) + (999999291249/1000000000000 : ℝ)*(sp_s0_6) + (17754377077/7812500000 : ℝ)*(f.sum) + (1512968511/10000000000000000000000 : ℝ)*base63 + (441031417/10000000000000000000000 : ℝ)*base64 + (4108264089/10000000000000000000000 : ℝ)*base66 + (2242931801/10000000000000000000000 : ℝ)*base68 + (2230209963/10000000000000000000000 : ℝ)*base71 + (67879069/500000000000000000000 : ℝ)*base73 + (313223809/1250000000000000000000 : ℝ)*base75 + (226463077/10000000000000000000000 : ℝ)*base77 + (4298923549/10000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p011_b007 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 15 ≤ c.val) (hhi : c.val < 17)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=15 ∨ c=16 := by omega
  rcases hc with rfl|rfl
  · exact collision_c311015 p hpa (by linarith only [hpb]) X hX
  · exact collision_c311016 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 15 ≤ c.val) (hhi : c.val < 17)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p011_b007 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

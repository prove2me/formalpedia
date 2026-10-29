-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:01:47.698989+00:00
-- url     : https://prove2.me/submissions/7df2f71d-fdc8-4282-9641-f762e3aed18a

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
theorem collision_support_c309071_s0_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1833374773/5000000000 : ℝ)*x 0 + (543333361/1000000000 : ℝ)*x 1 + (3684857381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1833374773/5000000000 : ℝ)^35 ≤ (27238262071629/100000000000000 : ℝ)^27 := by
    have hnat : (1833374773 : ℕ)^35*100000000000000^27 ≤ 27238262071629^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833374773 5000000000 27238262071629 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543333361/1000000000 : ℝ)^35 ≤ (45348979555869/100000000000000 : ℝ)^27 := by
    have hnat : (543333361 : ℕ)^35*100000000000000^27 ≤ 45348979555869^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543333361 1000000000 45348979555869 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3684857381/10000000000 : ℝ)^35 ≤ (13706379182929/50000000000000 : ℝ)^27 := by
    have hnat : (3684857381 : ℕ)^35*50000000000000^27 ≤ 13706379182929^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3684857381 10000000000 13706379182929 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1833374773/5000000000 : ℝ), (543333361/1000000000 : ℝ), (3684857381/10000000000 : ℝ)] ![(27238262071629/100000000000000 : ℝ), (45348979555869/100000000000000 : ℝ), (13706379182929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1833374773/5000000000 : ℝ)|^35 ≤ (27238262071629/100000000000000 : ℝ)^27
        have hw : |(1833374773/5000000000 : ℝ)|=(1833374773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543333361/1000000000 : ℝ)|^35 ≤ (45348979555869/100000000000000 : ℝ)^27
        have hw : |(543333361/1000000000 : ℝ)|=(543333361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3684857381/10000000000 : ℝ)|^35 ≤ (13706379182929/50000000000000 : ℝ)^27
        have hw : |(3684857381/10000000000 : ℝ)|=(3684857381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1718784451/2500000000 : ℝ)*x 0 + (-149789619/400000000 : ℝ)*x 1 + (-27423957/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1718784451/2500000000 : ℝ)^35 ≤ (15381847449177/25000000000000 : ℝ)^27 := by
    have hnat : (1718784451 : ℕ)^35*25000000000000^27 ≤ 15381847449177^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718784451 2500000000 15381847449177 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149789619/400000000 : ℝ)^35 ≤ (13995814125391/50000000000000 : ℝ)^27 := by
    have hnat : (149789619 : ℕ)^35*50000000000000^27 ≤ 13995814125391^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149789619 400000000 13995814125391 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27423957/156250000 : ℝ)^35 ≤ (10480981942643/100000000000000 : ℝ)^27 := by
    have hnat : (27423957 : ℕ)^35*100000000000000^27 ≤ 10480981942643^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27423957 156250000 10480981942643 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1718784451/2500000000 : ℝ), (-149789619/400000000 : ℝ), (-27423957/156250000 : ℝ)] ![(15381847449177/25000000000000 : ℝ), (13995814125391/50000000000000 : ℝ), (10480981942643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1718784451/2500000000 : ℝ)|^35 ≤ (15381847449177/25000000000000 : ℝ)^27
        have hw : |(1718784451/2500000000 : ℝ)|=(1718784451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149789619/400000000 : ℝ)|^35 ≤ (13995814125391/50000000000000 : ℝ)^27
        have hw : |(-149789619/400000000 : ℝ)|=(149789619/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27423957/156250000 : ℝ)|^35 ≤ (10480981942643/100000000000000 : ℝ)^27
        have hw : |(-27423957/156250000 : ℝ)|=(27423957/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-149487719/400000000 : ℝ)*x 0 + (-145288433/250000000 : ℝ)*x 1 + (634974399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (149487719/400000000 : ℝ)^35 ≤ (6979629255573/25000000000000 : ℝ)^27 := by
    have hnat : (149487719 : ℕ)^35*25000000000000^27 ≤ 6979629255573^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149487719 400000000 6979629255573 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145288433/250000000 : ℝ)^35 ≤ (4948246618647/10000000000000 : ℝ)^27 := by
    have hnat : (145288433 : ℕ)^35*10000000000000^27 ≤ 4948246618647^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145288433 250000000 4948246618647 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634974399/2000000000 : ℝ)^35 ≤ (22599016772607/100000000000000 : ℝ)^27 := by
    have hnat : (634974399 : ℕ)^35*100000000000000^27 ≤ 22599016772607^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634974399 2000000000 22599016772607 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-149487719/400000000 : ℝ), (-145288433/250000000 : ℝ), (634974399/2000000000 : ℝ)] ![(6979629255573/25000000000000 : ℝ), (4948246618647/10000000000000 : ℝ), (22599016772607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-149487719/400000000 : ℝ)|^35 ≤ (6979629255573/25000000000000 : ℝ)^27
        have hw : |(-149487719/400000000 : ℝ)|=(149487719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145288433/250000000 : ℝ)|^35 ≤ (4948246618647/10000000000000 : ℝ)^27
        have hw : |(-145288433/250000000 : ℝ)|=(145288433/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634974399/2000000000 : ℝ)|^35 ≤ (22599016772607/100000000000000 : ℝ)^27
        have hw : |(634974399/2000000000 : ℝ)|=(634974399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (341252789/1250000000 : ℝ)*x 0 + (6955649849/10000000000 : ℝ)*x 1 + (2772082871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341252789/1250000000 : ℝ)^35 ≤ (18582508013343/100000000000000 : ℝ)^27 := by
    have hnat : (341252789 : ℕ)^35*100000000000000^27 ≤ 18582508013343^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341252789 1250000000 18582508013343 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6955649849/10000000000 : ℝ)^35 ≤ (62463017284893/100000000000000 : ℝ)^27 := by
    have hnat : (6955649849 : ℕ)^35*100000000000000^27 ≤ 62463017284893^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6955649849 10000000000 62463017284893 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2772082871/10000000000 : ℝ)^35 ≤ (151635797533/800000000000 : ℝ)^27 := by
    have hnat : (2772082871 : ℕ)^35*800000000000^27 ≤ 151635797533^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772082871 10000000000 151635797533 800000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341252789/1250000000 : ℝ), (6955649849/10000000000 : ℝ), (2772082871/10000000000 : ℝ)] ![(18582508013343/100000000000000 : ℝ), (62463017284893/100000000000000 : ℝ), (151635797533/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341252789/1250000000 : ℝ)|^35 ≤ (18582508013343/100000000000000 : ℝ)^27
        have hw : |(341252789/1250000000 : ℝ)|=(341252789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6955649849/10000000000 : ℝ)|^35 ≤ (62463017284893/100000000000000 : ℝ)^27
        have hw : |(6955649849/10000000000 : ℝ)|=(6955649849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2772082871/10000000000 : ℝ)|^35 ≤ (151635797533/800000000000 : ℝ)^27
        have hw : |(2772082871/10000000000 : ℝ)|=(2772082871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (461053171/625000000 : ℝ)*x 0 + (-2051690787/5000000000 : ℝ)*x 1 + (-303041293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (461053171/625000000 : ℝ)^35 ≤ (8426198280291/12500000000000 : ℝ)^27 := by
    have hnat : (461053171 : ℕ)^35*12500000000000^27 ≤ 8426198280291^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461053171 625000000 8426198280291 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051690787/5000000000 : ℝ)^35 ≤ (31514997926939/100000000000000 : ℝ)^27 := by
    have hnat : (2051690787 : ℕ)^35*100000000000000^27 ≤ 31514997926939^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051690787 5000000000 31514997926939 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303041293/10000000000 : ℝ)^35 ≤ (1075415819777/100000000000000 : ℝ)^27 := by
    have hnat : (303041293 : ℕ)^35*100000000000000^27 ≤ 1075415819777^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303041293 10000000000 1075415819777 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(461053171/625000000 : ℝ), (-2051690787/5000000000 : ℝ), (-303041293/10000000000 : ℝ)] ![(8426198280291/12500000000000 : ℝ), (31514997926939/100000000000000 : ℝ), (1075415819777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(461053171/625000000 : ℝ)|^35 ≤ (8426198280291/12500000000000 : ℝ)^27
        have hw : |(461053171/625000000 : ℝ)|=(461053171/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051690787/5000000000 : ℝ)|^35 ≤ (31514997926939/100000000000000 : ℝ)^27
        have hw : |(-2051690787/5000000000 : ℝ)|=(2051690787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-303041293/10000000000 : ℝ)|^35 ≤ (1075415819777/100000000000000 : ℝ)^27
        have hw : |(-303041293/10000000000 : ℝ)|=(303041293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4933739/400000000 : ℝ)*x 0 + (-1286083677/10000000000 : ℝ)*x 1 + (9428918703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4933739/400000000 : ℝ)^35 ≤ (335367500293/100000000000000 : ℝ)^27 := by
    have hnat : (4933739 : ℕ)^35*100000000000000^27 ≤ 335367500293^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4933739 400000000 335367500293 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286083677/10000000000 : ℝ)^35 ≤ (7004046116229/100000000000000 : ℝ)^27 := by
    have hnat : (1286083677 : ℕ)^35*100000000000000^27 ≤ 7004046116229^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286083677 10000000000 7004046116229 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9428918703/10000000000 : ℝ)^35 ≤ (46330293187839/50000000000000 : ℝ)^27 := by
    have hnat : (9428918703 : ℕ)^35*50000000000000^27 ≤ 46330293187839^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9428918703 10000000000 46330293187839 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4933739/400000000 : ℝ), (-1286083677/10000000000 : ℝ), (9428918703/10000000000 : ℝ)] ![(335367500293/100000000000000 : ℝ), (7004046116229/100000000000000 : ℝ), (46330293187839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4933739/400000000 : ℝ)|^35 ≤ (335367500293/100000000000000 : ℝ)^27
        have hw : |(-4933739/400000000 : ℝ)|=(4933739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1286083677/10000000000 : ℝ)|^35 ≤ (7004046116229/100000000000000 : ℝ)^27
        have hw : |(-1286083677/10000000000 : ℝ)|=(1286083677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9428918703/10000000000 : ℝ)|^35 ≤ (46330293187839/50000000000000 : ℝ)^27
        have hw : |(9428918703/10000000000 : ℝ)|=(9428918703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-174061053/500000000 : ℝ)*x 0 + (-273082273/1000000000 : ℝ)*x 1 + (6388762819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174061053/500000000 : ℝ)^35 ≤ (25465275157559/100000000000000 : ℝ)^27 := by
    have hnat : (174061053 : ℕ)^35*100000000000000^27 ≤ 25465275157559^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174061053 500000000 25465275157559 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273082273/1000000000 : ℝ)^35 ≤ (4647392708267/25000000000000 : ℝ)^27 := by
    have hnat : (273082273 : ℕ)^35*25000000000000^27 ≤ 4647392708267^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273082273 1000000000 4647392708267 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6388762819/10000000000 : ℝ)^35 ≤ (55945153995393/100000000000000 : ℝ)^27 := by
    have hnat : (6388762819 : ℕ)^35*100000000000000^27 ≤ 55945153995393^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6388762819 10000000000 55945153995393 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174061053/500000000 : ℝ), (-273082273/1000000000 : ℝ), (6388762819/10000000000 : ℝ)] ![(25465275157559/100000000000000 : ℝ), (4647392708267/25000000000000 : ℝ), (55945153995393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174061053/500000000 : ℝ)|^35 ≤ (25465275157559/100000000000000 : ℝ)^27
        have hw : |(-174061053/500000000 : ℝ)|=(174061053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273082273/1000000000 : ℝ)|^35 ≤ (4647392708267/25000000000000 : ℝ)^27
        have hw : |(-273082273/1000000000 : ℝ)|=(273082273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6388762819/10000000000 : ℝ)|^35 ≤ (55945153995393/100000000000000 : ℝ)^27
        have hw : |(6388762819/10000000000 : ℝ)|=(6388762819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (264531229/400000000 : ℝ)*x 0 + (3724054947/10000000000 : ℝ)*x 1 + (2158161627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264531229/400000000 : ℝ)^35 ≤ (58506910865497/100000000000000 : ℝ)^27 := by
    have hnat : (264531229 : ℕ)^35*100000000000000^27 ≤ 58506910865497^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264531229 400000000 58506910865497 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3724054947/10000000000 : ℝ)^35 ≤ (3473919469149/12500000000000 : ℝ)^27 := by
    have hnat : (3724054947 : ℕ)^35*12500000000000^27 ≤ 3473919469149^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3724054947 10000000000 3473919469149 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158161627/10000000000 : ℝ)^35 ≤ (3425433341247/25000000000000 : ℝ)^27 := by
    have hnat : (2158161627 : ℕ)^35*25000000000000^27 ≤ 3425433341247^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158161627 10000000000 3425433341247 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264531229/400000000 : ℝ), (3724054947/10000000000 : ℝ), (2158161627/10000000000 : ℝ)] ![(58506910865497/100000000000000 : ℝ), (3473919469149/12500000000000 : ℝ), (3425433341247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264531229/400000000 : ℝ)|^35 ≤ (58506910865497/100000000000000 : ℝ)^27
        have hw : |(264531229/400000000 : ℝ)|=(264531229/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3724054947/10000000000 : ℝ)|^35 ≤ (3473919469149/12500000000000 : ℝ)^27
        have hw : |(3724054947/10000000000 : ℝ)|=(3724054947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2158161627/10000000000 : ℝ)|^35 ≤ (3425433341247/25000000000000 : ℝ)^27
        have hw : |(2158161627/10000000000 : ℝ)|=(2158161627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (873259673/1000000000 : ℝ)*x 0 + (-1993974037/10000000000 : ℝ)*x 1 + (-49591939/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873259673/1000000000 : ℝ)^35 ≤ (8388888341419/10000000000000 : ℝ)^27 := by
    have hnat : (873259673 : ℕ)^35*10000000000000^27 ≤ 8388888341419^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873259673 1000000000 8388888341419 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993974037/10000000000 : ℝ)^35 ≤ (6182996273591/50000000000000 : ℝ)^27 := by
    have hnat : (1993974037 : ℕ)^35*50000000000000^27 ≤ 6182996273591^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993974037 10000000000 6182996273591 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49591939/625000000 : ℝ)^35 ≤ (749024804389/20000000000000 : ℝ)^27 := by
    have hnat : (49591939 : ℕ)^35*20000000000000^27 ≤ 749024804389^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49591939 625000000 749024804389 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873259673/1000000000 : ℝ), (-1993974037/10000000000 : ℝ), (-49591939/625000000 : ℝ)] ![(8388888341419/10000000000000 : ℝ), (6182996273591/50000000000000 : ℝ), (749024804389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873259673/1000000000 : ℝ)|^35 ≤ (8388888341419/10000000000000 : ℝ)^27
        have hw : |(873259673/1000000000 : ℝ)|=(873259673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993974037/10000000000 : ℝ)|^35 ≤ (6182996273591/50000000000000 : ℝ)^27
        have hw : |(-1993974037/10000000000 : ℝ)|=(1993974037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49591939/625000000 : ℝ)|^35 ≤ (749024804389/20000000000000 : ℝ)^27
        have hw : |(-49591939/625000000 : ℝ)|=(49591939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-13814081/10000000000 : ℝ)*x 0 + (-314441391/2000000000 : ℝ)*x 1 + (9289859727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13814081/10000000000 : ℝ)^35 ≤ (19634054749/100000000000000 : ℝ)^27 := by
    have hnat : (13814081 : ℕ)^35*100000000000000^27 ≤ 19634054749^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13814081 10000000000 19634054749 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314441391/2000000000 : ℝ)^35 ≤ (4543688200937/50000000000000 : ℝ)^27 := by
    have hnat : (314441391 : ℕ)^35*50000000000000^27 ≤ 4543688200937^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314441391 2000000000 4543688200937 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9289859727/10000000000 : ℝ)^35 ≤ (90892989531931/100000000000000 : ℝ)^27 := by
    have hnat : (9289859727 : ℕ)^35*100000000000000^27 ≤ 90892989531931^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9289859727 10000000000 90892989531931 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13814081/10000000000 : ℝ), (-314441391/2000000000 : ℝ), (9289859727/10000000000 : ℝ)] ![(19634054749/100000000000000 : ℝ), (4543688200937/50000000000000 : ℝ), (90892989531931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13814081/10000000000 : ℝ)|^35 ≤ (19634054749/100000000000000 : ℝ)^27
        have hw : |(-13814081/10000000000 : ℝ)|=(13814081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-314441391/2000000000 : ℝ)|^35 ≤ (4543688200937/50000000000000 : ℝ)^27
        have hw : |(-314441391/2000000000 : ℝ)|=(314441391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9289859727/10000000000 : ℝ)|^35 ≤ (90892989531931/100000000000000 : ℝ)^27
        have hw : |(9289859727/10000000000 : ℝ)|=(9289859727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-914369409/2500000000 : ℝ)*x 0 + (-566226321/1250000000 : ℝ)*x 1 + (1161662477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914369409/2500000000 : ℝ)^35 ≤ (6787252987593/25000000000000 : ℝ)^27 := by
    have hnat : (914369409 : ℕ)^35*25000000000000^27 ≤ 6787252987593^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914369409 2500000000 6787252987593 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566226321/1250000000 : ℝ)^35 ≤ (17912154839849/50000000000000 : ℝ)^27 := by
    have hnat : (566226321 : ℕ)^35*50000000000000^27 ≤ 17912154839849^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566226321 1250000000 17912154839849 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161662477/2500000000 : ℝ)^35 ≤ (37026678360397/100000000000000 : ℝ)^27 := by
    have hnat : (1161662477 : ℕ)^35*100000000000000^27 ≤ 37026678360397^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161662477 2500000000 37026678360397 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914369409/2500000000 : ℝ), (-566226321/1250000000 : ℝ), (1161662477/2500000000 : ℝ)] ![(6787252987593/25000000000000 : ℝ), (17912154839849/50000000000000 : ℝ), (37026678360397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914369409/2500000000 : ℝ)|^35 ≤ (6787252987593/25000000000000 : ℝ)^27
        have hw : |(-914369409/2500000000 : ℝ)|=(914369409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566226321/1250000000 : ℝ)|^35 ≤ (17912154839849/50000000000000 : ℝ)^27
        have hw : |(-566226321/1250000000 : ℝ)|=(566226321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1161662477/2500000000 : ℝ)|^35 ≤ (37026678360397/100000000000000 : ℝ)^27
        have hw : |(1161662477/2500000000 : ℝ)|=(1161662477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1440451287/5000000000 : ℝ)*x 0 + (1207281063/2000000000 : ℝ)*x 1 + (3755602277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1440451287/5000000000 : ℝ)^35 ≤ (19924566863721/100000000000000 : ℝ)^27 := by
    have hnat : (1440451287 : ℕ)^35*100000000000000^27 ≤ 19924566863721^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440451287 5000000000 19924566863721 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1207281063/2000000000 : ℝ)^35 ≤ (51978511982141/100000000000000 : ℝ)^27 := by
    have hnat : (1207281063 : ℕ)^35*100000000000000^27 ≤ 51978511982141^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207281063 2000000000 51978511982141 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3755602277/10000000000 : ℝ)^35 ≤ (28096921142509/100000000000000 : ℝ)^27 := by
    have hnat : (3755602277 : ℕ)^35*100000000000000^27 ≤ 28096921142509^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3755602277 10000000000 28096921142509 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1440451287/5000000000 : ℝ), (1207281063/2000000000 : ℝ), (3755602277/10000000000 : ℝ)] ![(19924566863721/100000000000000 : ℝ), (51978511982141/100000000000000 : ℝ), (28096921142509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1440451287/5000000000 : ℝ)|^35 ≤ (19924566863721/100000000000000 : ℝ)^27
        have hw : |(1440451287/5000000000 : ℝ)|=(1440451287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1207281063/2000000000 : ℝ)|^35 ≤ (51978511982141/100000000000000 : ℝ)^27
        have hw : |(1207281063/2000000000 : ℝ)|=(1207281063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3755602277/10000000000 : ℝ)|^35 ≤ (28096921142509/100000000000000 : ℝ)^27
        have hw : |(3755602277/10000000000 : ℝ)|=(3755602277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s0_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7590428529/10000000000 : ℝ)*x 0 + (-2837606737/10000000000 : ℝ)*x 1 + (-109949537/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7590428529/10000000000 : ℝ)^35 ≤ (69950309773719/100000000000000 : ℝ)^27 := by
    have hnat : (7590428529 : ℕ)^35*100000000000000^27 ≤ 69950309773719^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7590428529 10000000000 69950309773719 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2837606737/10000000000 : ℝ)^35 ≤ (488431854689/2500000000000 : ℝ)^27 := by
    have hnat : (2837606737 : ℕ)^35*2500000000000^27 ≤ 488431854689^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837606737 10000000000 488431854689 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109949537/625000000 : ℝ)^35 ≤ (10512416020011/100000000000000 : ℝ)^27 := by
    have hnat : (109949537 : ℕ)^35*100000000000000^27 ≤ 10512416020011^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109949537 625000000 10512416020011 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7590428529/10000000000 : ℝ), (-2837606737/10000000000 : ℝ), (-109949537/625000000 : ℝ)] ![(69950309773719/100000000000000 : ℝ), (488431854689/2500000000000 : ℝ), (10512416020011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7590428529/10000000000 : ℝ)|^35 ≤ (69950309773719/100000000000000 : ℝ)^27
        have hw : |(7590428529/10000000000 : ℝ)|=(7590428529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2837606737/10000000000 : ℝ)|^35 ≤ (488431854689/2500000000000 : ℝ)^27
        have hw : |(-2837606737/10000000000 : ℝ)|=(2837606737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109949537/625000000 : ℝ)|^35 ≤ (10512416020011/100000000000000 : ℝ)^27
        have hw : |(-109949537/625000000 : ℝ)|=(109949537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3426349299/10000000000 : ℝ)*x 0 + (-807206699/2000000000 : ℝ)*x 1 + (2663771493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3426349299/10000000000 : ℝ)^35 ≤ (24946175383483/100000000000000 : ℝ)^27 := by
    have hnat : (3426349299 : ℕ)^35*100000000000000^27 ≤ 24946175383483^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3426349299 10000000000 24946175383483 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (807206699/2000000000 : ℝ)^35 ≤ (15423062604819/50000000000000 : ℝ)^27 := by
    have hnat : (807206699 : ℕ)^35*50000000000000^27 ≤ 15423062604819^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807206699 2000000000 15423062604819 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2663771493/5000000000 : ℝ)^35 ≤ (44207699393231/100000000000000 : ℝ)^27 := by
    have hnat : (2663771493 : ℕ)^35*100000000000000^27 ≤ 44207699393231^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663771493 5000000000 44207699393231 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3426349299/10000000000 : ℝ), (-807206699/2000000000 : ℝ), (2663771493/5000000000 : ℝ)] ![(24946175383483/100000000000000 : ℝ), (15423062604819/50000000000000 : ℝ), (44207699393231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3426349299/10000000000 : ℝ)|^35 ≤ (24946175383483/100000000000000 : ℝ)^27
        have hw : |(-3426349299/10000000000 : ℝ)|=(3426349299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-807206699/2000000000 : ℝ)|^35 ≤ (15423062604819/50000000000000 : ℝ)^27
        have hw : |(-807206699/2000000000 : ℝ)|=(807206699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2663771493/5000000000 : ℝ)|^35 ≤ (44207699393231/100000000000000 : ℝ)^27
        have hw : |(2663771493/5000000000 : ℝ)|=(2663771493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (210748593/500000000 : ℝ)*x 0 + (2509393923/5000000000 : ℝ)*x 1 + (896261737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210748593/500000000 : ℝ)^35 ≤ (32630425177917/100000000000000 : ℝ)^27 := by
    have hnat : (210748593 : ℕ)^35*100000000000000^27 ≤ 32630425177917^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210748593 500000000 32630425177917 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509393923/5000000000 : ℝ)^35 ≤ (10228863678283/25000000000000 : ℝ)^27 := by
    have hnat : (2509393923 : ℕ)^35*25000000000000^27 ≤ 10228863678283^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509393923 5000000000 10228863678283 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896261737/2500000000 : ℝ)^35 ≤ (13227060042419/50000000000000 : ℝ)^27 := by
    have hnat : (896261737 : ℕ)^35*50000000000000^27 ≤ 13227060042419^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896261737 2500000000 13227060042419 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210748593/500000000 : ℝ), (2509393923/5000000000 : ℝ), (896261737/2500000000 : ℝ)] ![(32630425177917/100000000000000 : ℝ), (10228863678283/25000000000000 : ℝ), (13227060042419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210748593/500000000 : ℝ)|^35 ≤ (32630425177917/100000000000000 : ℝ)^27
        have hw : |(210748593/500000000 : ℝ)|=(210748593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509393923/5000000000 : ℝ)|^35 ≤ (10228863678283/25000000000000 : ℝ)^27
        have hw : |(2509393923/5000000000 : ℝ)|=(2509393923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896261737/2500000000 : ℝ)|^35 ≤ (13227060042419/50000000000000 : ℝ)^27
        have hw : |(896261737/2500000000 : ℝ)|=(896261737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5730510281/10000000000 : ℝ)*x 0 + (-4125188239/10000000000 : ℝ)*x 1 + (-2853330973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5730510281/10000000000 : ℝ)^35 ≤ (2429499810671/5000000000000 : ℝ)^27 := by
    have hnat : (5730510281 : ℕ)^35*5000000000000^27 ≤ 2429499810671^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5730510281 10000000000 2429499810671 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4125188239/10000000000 : ℝ)^35 ≤ (31732273184901/100000000000000 : ℝ)^27 := by
    have hnat : (4125188239 : ℕ)^35*100000000000000^27 ≤ 31732273184901^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125188239 10000000000 31732273184901 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2853330973/10000000000 : ℝ)^35 ≤ (19677730583937/100000000000000 : ℝ)^27 := by
    have hnat : (2853330973 : ℕ)^35*100000000000000^27 ≤ 19677730583937^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2853330973 10000000000 19677730583937 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5730510281/10000000000 : ℝ), (-4125188239/10000000000 : ℝ), (-2853330973/10000000000 : ℝ)] ![(2429499810671/5000000000000 : ℝ), (31732273184901/100000000000000 : ℝ), (19677730583937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5730510281/10000000000 : ℝ)|^35 ≤ (2429499810671/5000000000000 : ℝ)^27
        have hw : |(5730510281/10000000000 : ℝ)|=(5730510281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4125188239/10000000000 : ℝ)|^35 ≤ (31732273184901/100000000000000 : ℝ)^27
        have hw : |(-4125188239/10000000000 : ℝ)|=(4125188239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2853330973/10000000000 : ℝ)|^35 ≤ (19677730583937/100000000000000 : ℝ)^27
        have hw : |(-2853330973/10000000000 : ℝ)|=(2853330973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309071_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2718800399/10000000000 : ℝ)*x 0 + (-153380301/500000000 : ℝ)*x 1 + (6734618207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2718800399/10000000000 : ℝ)^35 ≤ (18483551473581/100000000000000 : ℝ)^27 := by
    have hnat : (2718800399 : ℕ)^35*100000000000000^27 ≤ 18483551473581^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718800399 10000000000 18483551473581 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153380301/500000000 : ℝ)^35 ≤ (10807125688723/50000000000000 : ℝ)^27 := by
    have hnat : (153380301 : ℕ)^35*50000000000000^27 ≤ 10807125688723^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153380301 500000000 10807125688723 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6734618207/10000000000 : ℝ)^35 ≤ (59902197130333/100000000000000 : ℝ)^27 := by
    have hnat : (6734618207 : ℕ)^35*100000000000000^27 ≤ 59902197130333^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6734618207 10000000000 59902197130333 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2718800399/10000000000 : ℝ), (-153380301/500000000 : ℝ), (6734618207/10000000000 : ℝ)] ![(18483551473581/100000000000000 : ℝ), (10807125688723/50000000000000 : ℝ), (59902197130333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2718800399/10000000000 : ℝ)|^35 ≤ (18483551473581/100000000000000 : ℝ)^27
        have hw : |(2718800399/10000000000 : ℝ)|=(2718800399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-153380301/500000000 : ℝ)|^35 ≤ (10807125688723/50000000000000 : ℝ)^27
        have hw : |(-153380301/500000000 : ℝ)|=(153380301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6734618207/10000000000 : ℝ)|^35 ≤ (59902197130333/100000000000000 : ℝ)^27
        have hw : |(6734618207/10000000000 : ℝ)|=(6734618207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309071 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((1833374773/5000000000 : ℝ)*X 1 0+(543333361/1000000000 : ℝ)*X 1 1+(3684857381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1718784451/2500000000 : ℝ)*X 2 0+(-149789619/400000000 : ℝ)*X 2 1+(-27423957/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-149487719/400000000 : ℝ)*X 0 0+(-145288433/250000000 : ℝ)*X 0 1+(634974399/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((341252789/1250000000 : ℝ)*X 1 0+(6955649849/10000000000 : ℝ)*X 1 1+(2772082871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((461053171/625000000 : ℝ)*X 2 0+(-2051690787/5000000000 : ℝ)*X 2 1+(-303041293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-4933739/400000000 : ℝ)*X 0 0+(-1286083677/10000000000 : ℝ)*X 0 1+(9428918703/10000000000 : ℝ)*X 0 2+(-4933739/400000000 : ℝ)*X 1 0+(-1286083677/10000000000 : ℝ)*X 1 1+(9428918703/10000000000 : ℝ)*X 1 2+(-4933739/400000000 : ℝ)*X 2 0+(-1286083677/10000000000 : ℝ)*X 2 1+(9428918703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-174061053/500000000 : ℝ)*X 0 0+(-273082273/1000000000 : ℝ)*X 0 1+(6388762819/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((264531229/400000000 : ℝ)*X 1 0+(3724054947/10000000000 : ℝ)*X 1 1+(2158161627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((873259673/1000000000 : ℝ)*X 2 0+(-1993974037/10000000000 : ℝ)*X 2 1+(-49591939/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-13814081/10000000000 : ℝ)*X 0 0+(-314441391/2000000000 : ℝ)*X 0 1+(9289859727/10000000000 : ℝ)*X 0 2+(-13814081/10000000000 : ℝ)*X 1 0+(-314441391/2000000000 : ℝ)*X 1 1+(9289859727/10000000000 : ℝ)*X 1 2+(-13814081/10000000000 : ℝ)*X 2 0+(-314441391/2000000000 : ℝ)*X 2 1+(9289859727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-914369409/2500000000 : ℝ)*X 0 0+(-566226321/1250000000 : ℝ)*X 0 1+(1161662477/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1440451287/5000000000 : ℝ)*X 1 0+(1207281063/2000000000 : ℝ)*X 1 1+(3755602277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((7590428529/10000000000 : ℝ)*X 2 0+(-2837606737/10000000000 : ℝ)*X 2 1+(-109949537/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((64581/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64581/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2376910452994617436857/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54465763157/1000000000000 : ℝ)*(base1) + (403556510523/1000000000000 : ℝ)*(base7) + (3671321/1000000000000 : ℝ)*(base43) + (501197890793/500000000000 : ℝ)*(base54) + (303396992397/500000000000 : ℝ)*(base60) + (1110277133851/500000000000 : ℝ)*(major_s0_0) + (2220550596381/1000000000000 : ℝ)*(major_s0_1) + (304539621529/250000000000 : ℝ)*(major_s0_2) + (142772948183/50000000000 : ℝ)*(sp_s0_7) + (560200647493/200000000000 : ℝ)*(sp_s0_8) + (1798603784559/1000000000000 : ℝ)*(sp_s0_9) + (185188702629/250000000000 : ℝ)*(sp_s0_13) + (10906539/31250000000 : ℝ)*(sp_s0_20) + (6365641/1000000000000 : ℝ)*(sp_s0_21) + (1394408853983/1000000000000 : ℝ)*(f.failure) + (560200647493/200000000000 : ℝ)*(f.sum) + (553152123505811/10000000000000000000000000000 : ℝ)*base63 + (1024362016915311/2500000000000000000000000000 : ℝ)*base65 + (3117911471591981/5000000000000000000000000000 : ℝ)*base66 + (161955425758071/1250000000000000000000000000 : ℝ)*base68 + (40861841338193/125000000000000000000000000 : ℝ)*base71 + (2499362226174109/5000000000000000000000000000 : ℝ)*base72 + (4777097962429621/10000000000000000000000000000 : ℝ)*base74 + (1146090087598549/2500000000000000000000000000 : ℝ)*base77 + (80342091076609/500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (30801/100000000000000000 : ℝ)*base87 + (30801/100000000000000000 : ℝ)*base89 + (30801/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-87533/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-87533/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7098924287792965689027/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (502798960341/1000000000000 : ℝ)*(base1) + (558586924157/500000000000 : ℝ)*(base7) + (7260153/1000000000000 : ℝ)*(base21) + (12507651307/500000000000 : ℝ)*(base40) + (657111/200000000000 : ℝ)*(base54) + (14850132987/50000000000 : ℝ)*(base60) + (474999969037/250000000000 : ℝ)*(major_s0_0) + (474999969037/250000000000 : ℝ)*(major_s0_1) + (1899996590593/1000000000000 : ℝ)*(major_s0_2) + (746987/200000000000 : ℝ)*(sp_s0_1) + (1214762008549/500000000000 : ℝ)*(sp_s0_14) + (963360660911/500000000000 : ℝ)*(sp_s0_15) + (1926714511049/1000000000000 : ℝ)*(sp_s0_16) + (903743311287/500000000000 : ℝ)*(sp_s0_20) + (298278755039/250000000000 : ℝ)*(f.failure) + (481681264189/250000000000 : ℝ)*(f.sum) + (881479077324359/5000000000000000000000000000 : ℝ)*base63 + (5259663751687/10000000000000000000000000000 : ℝ)*base65 + (163137777150237/1250000000000000000000000000 : ℝ)*base66 + (1415256765402607/5000000000000000000000000000 : ℝ)*base68 + (8217342317450209/10000000000000000000000000000 : ℝ)*base70 + (680543931886517/2500000000000000000000000000 : ℝ)*base73 + (1331721982636517/2500000000000000000000000000 : ℝ)*base74 + (434038584275237/1250000000000000000000000000 : ℝ)*base76 + (1390300968836043/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (4367/25000000000000000 : ℝ)*base86 + (4367/25000000000000000 : ℝ)*base88 + (4367/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13451/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13451/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18561980903923644688683/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1137331443/400000000 : ℝ)*(base1) + (249777543163/250000000000 : ℝ)*(base7) + (726980070921/500000000000 : ℝ)*(base40) + (439144942051/1000000000000 : ℝ)*(base60) + (2936862530941/1000000000000 : ℝ)*(major_s0_0) + (2936862530941/1000000000000 : ℝ)*(major_s0_1) + (2936862530941/1000000000000 : ℝ)*(major_s0_2) + (46173261/1000000000000 : ℝ)*(sp_s0_1) + (29567/31250000000 : ℝ)*(sp_s0_2) + (3125361/250000000000 : ℝ)*(sp_s0_7) + (10817243/200000000000 : ℝ)*(sp_s0_8) + (6264539527907/1000000000000 : ℝ)*(sp_s0_21) + (27368985299/8000000000 : ℝ)*(sp_s0_22) + (3421222475707/1000000000000 : ℝ)*(sp_s0_23) + (1844218434847/1000000000000 : ℝ)*(f.failure) + (855305855463/250000000000 : ℝ)*(f.sum) + (2728567796661499/10000000000000000000000000000 : ℝ)*base62 + (1813482706973419/10000000000000000000000000000 : ℝ)*base65 + (5230168182541/5000000000000000000000000000 : ℝ)*base66 + (277677417817459/5000000000000000000000000000 : ℝ)*base68 + (8330897580608337/10000000000000000000000000000 : ℝ)*base71 + (1344212031973419/10000000000000000000000000000 : ℝ)*base72 + (3789398671973419/10000000000000000000000000000 : ℝ)*base75 + (800599729317459/5000000000000000000000000000 : ℝ)*base77 + (4280730195338501/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (19791/100000000000000000 : ℝ)*base86 + (19791/100000000000000000 : ℝ)*base88 + (19791/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (64581/100000 : ℝ) ^ (69/16 : ℝ) ≤ (948324168090433841/6250000000000000000 : ℝ) := by
    have hpowers : (64581/100000 : ℝ)^69 ≤ (948324168090433841/6250000000000000000 : ℝ)^16 := by
      have hnat : (64581 : ℕ)^69*6250000000000000000^16 ≤ 948324168090433841^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64581 100000 948324168090433841 6250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64581/100000 : ℝ)) (X := (948324168090433841/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (7198324168090433841/6250000000000000000 : ℝ) ≤ (1033299948478329/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (7198324168090433841/6250000000000000000 : ℝ)^16 ≤ (1033299948478329/1000000000000000 : ℝ)^69 := by
      have hnat : (7198324168090433841 : ℕ)^16*1000000000000000^69 ≤ 1033299948478329^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7198324168090433841 6250000000000000000 1033299948478329 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1033299948478329/1000000000000000 : ℝ)) (X := (7198324168090433841/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (4073324168090433841/3125000000000000000 : ℝ) ≤ (2126765505590879/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (4073324168090433841/3125000000000000000 : ℝ)^16 ≤ (2126765505590879/2000000000000000 : ℝ)^69 := by
      have hnat : (4073324168090433841 : ℕ)^16*2000000000000000^69 ≤ 2126765505590879^69*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4073324168090433841 3125000000000000000 2126765505590879 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2126765505590879/2000000000000000 : ℝ)) (X := (4073324168090433841/3125000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(33299948478329/645810000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(60165608634221/1291620000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (64581/100000 : ℝ)) (alpha := (33299948478329/645810000000000 : ℝ)) (beta := (60165608634221/1291620000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (64581/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(33299948478329/645810000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(60165608634221/1291620000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (87533/100000 : ℝ) ^ (69/16 : ℝ) ≤ (3519621498543916951/6250000000000000000 : ℝ) := by
    have hpowers : (87533/100000 : ℝ)^69 ≤ (3519621498543916951/6250000000000000000 : ℝ)^16 := by
      have hnat : (87533 : ℕ)^69*6250000000000000000^16 ≤ 3519621498543916951^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87533 100000 3519621498543916951 6250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87533/100000 : ℝ)) (X := (3519621498543916951/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (9769621498543916951/6250000000000000000 : ℝ) ≤ (221827290434819/200000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (9769621498543916951/6250000000000000000 : ℝ)^16 ≤ (221827290434819/200000000000000 : ℝ)^69 := by
      have hnat : (9769621498543916951 : ℕ)^16*200000000000000^69 ≤ 221827290434819^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9769621498543916951 6250000000000000000 221827290434819 200000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (221827290434819/200000000000000 : ℝ)) (X := (9769621498543916951/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (6644621498543916951/3125000000000000000 : ℝ) ≤ (2977898671497119/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (6644621498543916951/3125000000000000000 : ℝ)^16 ≤ (2977898671497119/2500000000000000 : ℝ)^69 := by
      have hnat : (6644621498543916951 : ℕ)^16*2500000000000000^69 ≤ 2977898671497119^69*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6644621498543916951 3125000000000000000 2977898671497119 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2977898671497119/2500000000000000 : ℝ)) (X := (6644621498543916951/3125000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(21827290434819/175066000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(410115082123763/4376650000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (87533/100000 : ℝ)) (alpha := (21827290434819/175066000000000 : ℝ)) (beta := (410115082123763/4376650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (87533/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(21827290434819/175066000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(410115082123763/4376650000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13451/25000 : ℝ) ^ (69/16 : ℝ) ≤ (863073575910502833/12500000000000000000 : ℝ) := by
    have hpowers : (13451/25000 : ℝ)^69 ≤ (863073575910502833/12500000000000000000 : ℝ)^16 := by
      have hnat : (13451 : ℕ)^69*12500000000000000000^16 ≤ 863073575910502833^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13451 25000 863073575910502833 12500000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13451/25000 : ℝ)) (X := (863073575910502833/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (13363073575910502833/12500000000000000000 : ℝ) ≤ (5078012842068537/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (13363073575910502833/12500000000000000000 : ℝ)^16 ≤ (5078012842068537/5000000000000000 : ℝ)^69 := by
      have hnat : (13363073575910502833 : ℕ)^16*5000000000000000^69 ≤ 5078012842068537^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13363073575910502833 12500000000000000000 5078012842068537 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5078012842068537/5000000000000000 : ℝ)) (X := (13363073575910502833/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (7113073575910502833/6250000000000000000 : ℝ) ≤ (10304492713763667/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (7113073575910502833/6250000000000000000 : ℝ)^16 ≤ (10304492713763667/10000000000000000 : ℝ)^69 := by
      have hnat : (7113073575910502833 : ℕ)^16*10000000000000000^69 ≤ 10304492713763667^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7113073575910502833 6250000000000000000 10304492713763667 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10304492713763667/10000000000000000 : ℝ)) (X := (7113073575910502833/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(78012842068537/2690200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(148467029626593/5380400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (13451/25000 : ℝ)) (alpha := (78012842068537/2690200000000000 : ℝ)) (beta := (148467029626593/5380400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (13451/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(78012842068537/2690200000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(148467029626593/5380400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3426349299/10000000000 : ℝ)*X 0 0+(-807206699/2000000000 : ℝ)*X 0 1+(2663771493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((210748593/500000000 : ℝ)*X 1 0+(2509393923/5000000000 : ℝ)*X 1 1+(896261737/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5730510281/10000000000 : ℝ)*X 2 0+(-4125188239/10000000000 : ℝ)*X 2 1+(-2853330973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2718800399/10000000000 : ℝ)*X 0 0+(-153380301/500000000 : ℝ)*X 0 1+(6734618207/10000000000 : ℝ)*X 0 2+(2718800399/10000000000 : ℝ)*X 1 0+(-153380301/500000000 : ℝ)*X 1 1+(6734618207/10000000000 : ℝ)*X 1 2+(2718800399/10000000000 : ℝ)*X 2 0+(-153380301/500000000 : ℝ)*X 2 1+(6734618207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-327741/50000 : ℝ) < ((-159247/100000 : ℝ)*P 0+(-159247/100000 : ℝ)*P 1+(-159247/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-327741/50000 : ℝ) < (-10830513192016052203269838049155627/1667501789923750000000000000000000 : ℝ) := by norm_num
    linear_combination (127443411307/500000000000 : ℝ)*(base1) + (109351/1000000000000 : ℝ)*(base5) + (27729/250000000000 : ℝ)*(base21) + (15237/250000000000 : ℝ)*(base34) + (12146107639/31250000000 : ℝ)*(base40) + (107/250000000000 : ℝ)*(base49) + (421054489/976562500 : ℝ)*(base60) + (398117485171/250000000000 : ℝ)*(major_s1_0) + (159247/100000 : ℝ)*(major_s1_1) + (159247/100000 : ℝ)*(major_s1_2) + (151244035071/62500000000 : ℝ)*(sp_s1_0) + (2165017801103/1000000000000 : ℝ)*(sp_s1_1) + (1082508899769/500000000000 : ℝ)*(sp_s1_2) + (745113007087/1000000000000 : ℝ)*(sp_s1_6) + (2165017799471/1000000000000 : ℝ)*(f.sum) + (5973499168630115233/11774063830000000000000000000000 : ℝ)*base63 + (3525951426447/6725500000000000000000000 : ℝ)*base64 + (20063598176807/175066000000000000000000000 : ℝ)*base67 + (81090347119857/134510000000000000000000000 : ℝ)*base69 + (1633158160342631551/4343395155000000000000000000000 : ℝ)*base70 + (25161162406189/645810000000000000000000000 : ℝ)*base73 + (600054623767097/875330000000000000000000000 : ℝ)*base75 + (24647122205441/322905000000000000000000000 : ℝ)*base76 + (79568632024218571/2975246670000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (51/31250000000 : ℝ)*base83 + (51/31250000000 : ℝ)*base85 + (51/31250000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c309072_s0_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-535605521/1250000000 : ℝ)*x 0 + (-535605521/1250000000 : ℝ)*x 1 + (-535605521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535605521/1250000000 : ℝ), (-535605521/1250000000 : ℝ), (-535605521/1250000000 : ℝ)] ![(16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(-535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(-535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(-535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309072_s0_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (535605521/1250000000 : ℝ)*x 0 + (535605521/1250000000 : ℝ)*x 1 + (-535605521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535605521/1250000000 : ℝ), (535605521/1250000000 : ℝ), (-535605521/1250000000 : ℝ)] ![(16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(-535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309072_s0_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (535605521/1250000000 : ℝ)*x 0 + (-535605521/1250000000 : ℝ)*x 1 + (535605521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535605521/1250000000 : ℝ), (-535605521/1250000000 : ℝ), (535605521/1250000000 : ℝ)] ![(16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(-535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309072_s0_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (535605521/1250000000 : ℝ)*x 0 + (-535605521/1250000000 : ℝ)*x 1 + (-535605521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535605521/1250000000 : ℝ), (-535605521/1250000000 : ℝ), (-535605521/1250000000 : ℝ)] ![(16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(-535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(-535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309072 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-535605521/1250000000 : ℝ)*X 0 0+(-535605521/1250000000 : ℝ)*X 0 1+(-535605521/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309072_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((535605521/1250000000 : ℝ)*X 1 0+(535605521/1250000000 : ℝ)*X 1 1+(-535605521/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309072_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((535605521/1250000000 : ℝ)*X 2 0+(-535605521/1250000000 : ℝ)*X 2 1+(535605521/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309072_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((535605521/1250000000 : ℝ)*X 0 0+(-535605521/1250000000 : ℝ)*X 0 1+(-535605521/1250000000 : ℝ)*X 0 2+(535605521/1250000000 : ℝ)*X 1 0+(-535605521/1250000000 : ℝ)*X 1 1+(-535605521/1250000000 : ℝ)*X 1 2+(535605521/1250000000 : ℝ)*X 2 0+(-535605521/1250000000 : ℝ)*X 2 1+(-535605521/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309072_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-327741/50000 : ℝ) < ((-159247/100000 : ℝ)*P 0+(-159247/100000 : ℝ)*P 1+(-159247/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-327741/50000 : ℝ) < (-8041294721366706624679/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (56900727029/500000000000 : ℝ)*(base6) + (11663899519/125000000000 : ℝ)*(base39) + (11663899519/125000000000 : ℝ)*(base49) + (11663899519/125000000000 : ℝ)*(base59) + (159247/100000 : ℝ)*(major_s0_0) + (159247/100000 : ℝ)*(major_s0_1) + (159247/100000 : ℝ)*(major_s0_2) + (2182279077049/1000000000000 : ℝ)*(sp_s0_0) + (2182279077049/1000000000000 : ℝ)*(sp_s0_1) + (2182279077049/1000000000000 : ℝ)*(sp_s0_2) + (443099272971/500000000000 : ℝ)*(sp_s0_6) + (2182279077049/1000000000000 : ℝ)*(f.sum) + (106944177/5000000000000000000000 : ℝ)*base62 + (1283391121/5000000000000000000000 : ℝ)*base64 + (517415613/2500000000000000000000 : ℝ)*base66 + (517415613/2500000000000000000000 : ℝ)*base69 + (106944177/5000000000000000000000 : ℝ)*base71 + (1283391121/5000000000000000000000 : ℝ)*base72 + (1283391121/5000000000000000000000 : ℝ)*base75 + (517415613/2500000000000000000000 : ℝ)*base76 + (106944177/5000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p009_b033 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 71 ≤ c.val) (hhi : c.val < 73)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=71 ∨ c=72 := by omega
  rcases hc with rfl|rfl
  · exact collision_c309071 p hpa (by linarith only [hpb]) X hX
  · exact collision_c309072 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 71 ≤ c.val) (hhi : c.val < 73)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b041
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:33:27.55717+00:00
-- url     : https://prove2.me/submissions/fda9c960-e933-458e-a7df-989e037b951c

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
theorem collision_support_c330082_s0_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (926522607/2500000000 : ℝ)*x 0 + (-2782411547/10000000000 : ℝ)*x 1 + (2715559411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926522607/2500000000 : ℝ)^6 ≤ (1215511873487/4000000000000 : ℝ)^5 := by
    have hnat : (926522607 : ℕ)^6*4000000000000^5 ≤ 1215511873487^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926522607 2500000000 1215511873487 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2782411547/10000000000 : ℝ)^6 ≤ (21542973160613/100000000000000 : ℝ)^5 := by
    have hnat : (2782411547 : ℕ)^6*100000000000000^5 ≤ 21542973160613^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782411547 10000000000 21542973160613 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715559411/5000000000 : ℝ)^6 ≤ (48069229984179/100000000000000 : ℝ)^5 := by
    have hnat : (2715559411 : ℕ)^6*100000000000000^5 ≤ 48069229984179^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715559411 5000000000 48069229984179 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(926522607/2500000000 : ℝ), (-2782411547/10000000000 : ℝ), (2715559411/5000000000 : ℝ)] ![(1215511873487/4000000000000 : ℝ), (21542973160613/100000000000000 : ℝ), (48069229984179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(926522607/2500000000 : ℝ)|^6 ≤ (1215511873487/4000000000000 : ℝ)^5
        have hw : |(926522607/2500000000 : ℝ)|=(926522607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2782411547/10000000000 : ℝ)|^6 ≤ (21542973160613/100000000000000 : ℝ)^5
        have hw : |(-2782411547/10000000000 : ℝ)|=(2782411547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715559411/5000000000 : ℝ)|^6 ≤ (48069229984179/100000000000000 : ℝ)^5
        have hw : |(2715559411/5000000000 : ℝ)|=(2715559411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (149050217/250000000 : ℝ)*x 0 + (1029635053/2000000000 : ℝ)*x 1 + (-121774731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (149050217/250000000 : ℝ)^6 ≤ (26880734359559/50000000000000 : ℝ)^5 := by
    have hnat : (149050217 : ℕ)^6*50000000000000^5 ≤ 26880734359559^5*250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149050217 250000000 26880734359559 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029635053/2000000000 : ℝ)^6 ≤ (45080008408379/100000000000000 : ℝ)^5 := by
    have hnat : (1029635053 : ℕ)^6*100000000000000^5 ≤ 45080008408379^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029635053 2000000000 45080008408379 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121774731/5000000000 : ℝ)^6 ≤ (72407679041/6250000000000 : ℝ)^5 := by
    have hnat : (121774731 : ℕ)^6*6250000000000^5 ≤ 72407679041^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121774731 5000000000 72407679041 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(149050217/250000000 : ℝ), (1029635053/2000000000 : ℝ), (-121774731/5000000000 : ℝ)] ![(26880734359559/50000000000000 : ℝ), (45080008408379/100000000000000 : ℝ), (72407679041/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(149050217/250000000 : ℝ)|^6 ≤ (26880734359559/50000000000000 : ℝ)^5
        have hw : |(149050217/250000000 : ℝ)|=(149050217/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029635053/2000000000 : ℝ)|^6 ≤ (45080008408379/100000000000000 : ℝ)^5
        have hw : |(1029635053/2000000000 : ℝ)|=(1029635053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121774731/5000000000 : ℝ)|^6 ≤ (72407679041/6250000000000 : ℝ)^5
        have hw : |(-121774731/5000000000 : ℝ)|=(121774731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-3157561371/10000000000 : ℝ)*x 0 + (807977861/5000000000 : ℝ)*x 1 + (6867512303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3157561371/10000000000 : ℝ)^6 ≤ (3134239455339/12500000000000 : ℝ)^5 := by
    have hnat : (3157561371 : ℕ)^6*12500000000000^5 ≤ 3134239455339^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3157561371 10000000000 3134239455339 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (807977861/5000000000 : ℝ)^6 ≤ (5611582502711/50000000000000 : ℝ)^5 := by
    have hnat : (807977861 : ℕ)^6*50000000000000^5 ≤ 5611582502711^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807977861 5000000000 5611582502711 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6867512303/10000000000 : ℝ)^6 ≤ (12740583866913/20000000000000 : ℝ)^5 := by
    have hnat : (6867512303 : ℕ)^6*20000000000000^5 ≤ 12740583866913^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6867512303 10000000000 12740583866913 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3157561371/10000000000 : ℝ), (807977861/5000000000 : ℝ), (6867512303/10000000000 : ℝ)] ![(3134239455339/12500000000000 : ℝ), (5611582502711/50000000000000 : ℝ), (12740583866913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3157561371/10000000000 : ℝ)|^6 ≤ (3134239455339/12500000000000 : ℝ)^5
        have hw : |(-3157561371/10000000000 : ℝ)|=(3157561371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(807977861/5000000000 : ℝ)|^6 ≤ (5611582502711/50000000000000 : ℝ)^5
        have hw : |(807977861/5000000000 : ℝ)|=(807977861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6867512303/10000000000 : ℝ)|^6 ≤ (12740583866913/20000000000000 : ℝ)^5
        have hw : |(6867512303/10000000000 : ℝ)|=(6867512303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (251859199/625000000 : ℝ)*x 0 + (-1018339117/10000000000 : ℝ)*x 1 + (652882529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251859199/625000000 : ℝ)^6 ≤ (33599542237273/100000000000000 : ℝ)^5 := by
    have hnat : (251859199 : ℕ)^6*100000000000000^5 ≤ 33599542237273^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251859199 625000000 33599542237273 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018339117/10000000000 : ℝ)^6 ≤ (6448681263113/100000000000000 : ℝ)^5 := by
    have hnat : (1018339117 : ℕ)^6*100000000000000^5 ≤ 6448681263113^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018339117 10000000000 6448681263113 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652882529/1000000000 : ℝ)^6 ≤ (14987944119891/25000000000000 : ℝ)^5 := by
    have hnat : (652882529 : ℕ)^6*25000000000000^5 ≤ 14987944119891^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652882529 1000000000 14987944119891 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(251859199/625000000 : ℝ), (-1018339117/10000000000 : ℝ), (652882529/1000000000 : ℝ)] ![(33599542237273/100000000000000 : ℝ), (6448681263113/100000000000000 : ℝ), (14987944119891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(251859199/625000000 : ℝ)|^6 ≤ (33599542237273/100000000000000 : ℝ)^5
        have hw : |(251859199/625000000 : ℝ)|=(251859199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1018339117/10000000000 : ℝ)|^6 ≤ (6448681263113/100000000000000 : ℝ)^5
        have hw : |(-1018339117/10000000000 : ℝ)|=(1018339117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652882529/1000000000 : ℝ)|^6 ≤ (14987944119891/25000000000000 : ℝ)^5
        have hw : |(652882529/1000000000 : ℝ)|=(652882529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4330976523/10000000000 : ℝ)*x 0 + (6776741941/10000000000 : ℝ)*x 1 + (-9650983/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330976523/10000000000 : ℝ)^6 ≤ (36635573584727/100000000000000 : ℝ)^5 := by
    have hnat : (4330976523 : ℕ)^6*100000000000000^5 ≤ 36635573584727^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330976523 10000000000 36635573584727 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6776741941/10000000000 : ℝ)^6 ≤ (31346939226123/50000000000000 : ℝ)^5 := by
    have hnat : (6776741941 : ℕ)^6*50000000000000^5 ≤ 31346939226123^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6776741941 10000000000 31346939226123 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9650983/625000000 : ℝ)^6 ≤ (536438361/80000000000 : ℝ)^5 := by
    have hnat : (9650983 : ℕ)^6*80000000000^5 ≤ 536438361^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9650983 625000000 536438361 80000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330976523/10000000000 : ℝ), (6776741941/10000000000 : ℝ), (-9650983/625000000 : ℝ)] ![(36635573584727/100000000000000 : ℝ), (31346939226123/50000000000000 : ℝ), (536438361/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330976523/10000000000 : ℝ)|^6 ≤ (36635573584727/100000000000000 : ℝ)^5
        have hw : |(4330976523/10000000000 : ℝ)|=(4330976523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6776741941/10000000000 : ℝ)|^6 ≤ (31346939226123/50000000000000 : ℝ)^5
        have hw : |(6776741941/10000000000 : ℝ)|=(6776741941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9650983/625000000 : ℝ)|^6 ≤ (536438361/80000000000 : ℝ)^5
        have hw : |(-9650983/625000000 : ℝ)|=(9650983/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4217941/1250000000 : ℝ)*x 0 + (4209696717/5000000000 : ℝ)*x 1 + (491172211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217941/1250000000 : ℝ)^6 ≤ (108100719637/100000000000000 : ℝ)^5 := by
    have hnat : (4217941 : ℕ)^6*100000000000000^5 ≤ 108100719637^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217941 1250000000 108100719637 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4209696717/5000000000 : ℝ)^6 ≤ (81346142886121/100000000000000 : ℝ)^5 := by
    have hnat : (4209696717 : ℕ)^6*100000000000000^5 ≤ 81346142886121^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209696717 5000000000 81346142886121 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491172211/2000000000 : ℝ)^6 ≤ (3709151276277/20000000000000 : ℝ)^5 := by
    have hnat : (491172211 : ℕ)^6*20000000000000^5 ≤ 3709151276277^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491172211 2000000000 3709151276277 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217941/1250000000 : ℝ), (4209696717/5000000000 : ℝ), (491172211/2000000000 : ℝ)] ![(108100719637/100000000000000 : ℝ), (81346142886121/100000000000000 : ℝ), (3709151276277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217941/1250000000 : ℝ)|^6 ≤ (108100719637/100000000000000 : ℝ)^5
        have hw : |(4217941/1250000000 : ℝ)|=(4217941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4209696717/5000000000 : ℝ)|^6 ≤ (81346142886121/100000000000000 : ℝ)^5
        have hw : |(4209696717/5000000000 : ℝ)|=(4209696717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(491172211/2000000000 : ℝ)|^6 ≤ (3709151276277/20000000000000 : ℝ)^5
        have hw : |(491172211/2000000000 : ℝ)|=(491172211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-2704433333/10000000000 : ℝ)*x 0 + (2004968133/10000000000 : ℝ)*x 1 + (3475827391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704433333/10000000000 : ℝ)^6 ≤ (4164103656417/20000000000000 : ℝ)^5 := by
    have hnat : (2704433333 : ℕ)^6*20000000000000^5 ≤ 4164103656417^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704433333 10000000000 4164103656417 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004968133/10000000000 : ℝ)^6 ≤ (3634703405297/25000000000000 : ℝ)^5 := by
    have hnat : (2004968133 : ℕ)^6*25000000000000^5 ≤ 3634703405297^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004968133 10000000000 3634703405297 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3475827391/5000000000 : ℝ)^6 ≤ (64640668085053/100000000000000 : ℝ)^5 := by
    have hnat : (3475827391 : ℕ)^6*100000000000000^5 ≤ 64640668085053^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3475827391 5000000000 64640668085053 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2704433333/10000000000 : ℝ), (2004968133/10000000000 : ℝ), (3475827391/5000000000 : ℝ)] ![(4164103656417/20000000000000 : ℝ), (3634703405297/25000000000000 : ℝ), (64640668085053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2704433333/10000000000 : ℝ)|^6 ≤ (4164103656417/20000000000000 : ℝ)^5
        have hw : |(-2704433333/10000000000 : ℝ)|=(2704433333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2004968133/10000000000 : ℝ)|^6 ≤ (3634703405297/25000000000000 : ℝ)^5
        have hw : |(2004968133/10000000000 : ℝ)|=(2004968133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3475827391/5000000000 : ℝ)|^6 ≤ (64640668085053/100000000000000 : ℝ)^5
        have hw : |(3475827391/5000000000 : ℝ)|=(3475827391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5987041231/10000000000 : ℝ)*x 0 + (-93121947/312500000 : ℝ)*x 1 + (289325509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5987041231/10000000000 : ℝ)^6 ≤ (54032454797957/100000000000000 : ℝ)^5 := by
    have hnat : (5987041231 : ℕ)^6*100000000000000^5 ≤ 54032454797957^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5987041231 10000000000 54032454797957 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93121947/312500000 : ℝ)^6 ≤ (2923832196843/12500000000000 : ℝ)^5 := by
    have hnat : (93121947 : ℕ)^6*12500000000000^5 ≤ 2923832196843^5*312500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93121947 312500000 2923832196843 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289325509/1000000000 : ℝ)^6 ≤ (22576887608667/100000000000000 : ℝ)^5 := by
    have hnat : (289325509 : ℕ)^6*100000000000000^5 ≤ 22576887608667^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289325509 1000000000 22576887608667 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5987041231/10000000000 : ℝ), (-93121947/312500000 : ℝ), (289325509/1000000000 : ℝ)] ![(54032454797957/100000000000000 : ℝ), (2923832196843/12500000000000 : ℝ), (22576887608667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5987041231/10000000000 : ℝ)|^6 ≤ (54032454797957/100000000000000 : ℝ)^5
        have hw : |(5987041231/10000000000 : ℝ)|=(5987041231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93121947/312500000 : ℝ)|^6 ≤ (2923832196843/12500000000000 : ℝ)^5
        have hw : |(-93121947/312500000 : ℝ)|=(93121947/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(289325509/1000000000 : ℝ)|^6 ≤ (22576887608667/100000000000000 : ℝ)^5
        have hw : |(289325509/1000000000 : ℝ)|=(289325509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (741239169/1000000000 : ℝ)*x 0 + (343031903/1000000000 : ℝ)*x 1 + (-92150751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741239169/1000000000 : ℝ)^6 ≤ (17453801853359/25000000000000 : ℝ)^5 := by
    have hnat : (741239169 : ℕ)^6*25000000000000^5 ≤ 17453801853359^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741239169 1000000000 17453801853359 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343031903/1000000000 : ℝ)^6 ≤ (27695002911503/100000000000000 : ℝ)^5 := by
    have hnat : (343031903 : ℕ)^6*100000000000000^5 ≤ 27695002911503^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343031903 1000000000 27695002911503 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92150751/2000000000 : ℝ)^6 ≤ (1244894832653/50000000000000 : ℝ)^5 := by
    have hnat : (92150751 : ℕ)^6*50000000000000^5 ≤ 1244894832653^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92150751 2000000000 1244894832653 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(741239169/1000000000 : ℝ), (343031903/1000000000 : ℝ), (-92150751/2000000000 : ℝ)] ![(17453801853359/25000000000000 : ℝ), (27695002911503/100000000000000 : ℝ), (1244894832653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(741239169/1000000000 : ℝ)|^6 ≤ (17453801853359/25000000000000 : ℝ)^5
        have hw : |(741239169/1000000000 : ℝ)|=(741239169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343031903/1000000000 : ℝ)|^6 ≤ (27695002911503/100000000000000 : ℝ)^5
        have hw : |(343031903/1000000000 : ℝ)|=(343031903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92150751/2000000000 : ℝ)|^6 ≤ (1244894832653/50000000000000 : ℝ)^5
        have hw : |(-92150751/2000000000 : ℝ)|=(92150751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (8661/5000000000 : ℝ)*x 0 + (4236866113/10000000000 : ℝ)*x 1 + (6922691217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8661/5000000000 : ℝ)^6 ≤ (2439763/20000000000000 : ℝ)^5 := by
    have hnat : (8661 : ℕ)^6*20000000000000^5 ≤ 2439763^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8661 5000000000 2439763 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236866113/10000000000 : ℝ)^6 ≤ (7136473936627/20000000000000 : ℝ)^5 := by
    have hnat : (4236866113 : ℕ)^6*20000000000000^5 ≤ 7136473936627^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236866113 10000000000 7136473936627 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6922691217/10000000000 : ℝ)^6 ≤ (1607940452657/2500000000000 : ℝ)^5 := by
    have hnat : (6922691217 : ℕ)^6*2500000000000^5 ≤ 1607940452657^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6922691217 10000000000 1607940452657 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8661/5000000000 : ℝ), (4236866113/10000000000 : ℝ), (6922691217/10000000000 : ℝ)] ![(2439763/20000000000000 : ℝ), (7136473936627/20000000000000 : ℝ), (1607940452657/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8661/5000000000 : ℝ)|^6 ≤ (2439763/20000000000000 : ℝ)^5
        have hw : |(8661/5000000000 : ℝ)|=(8661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236866113/10000000000 : ℝ)|^6 ≤ (7136473936627/20000000000000 : ℝ)^5
        have hw : |(4236866113/10000000000 : ℝ)|=(4236866113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6922691217/10000000000 : ℝ)|^6 ≤ (1607940452657/2500000000000 : ℝ)^5
        have hw : |(6922691217/10000000000 : ℝ)|=(6922691217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-2282883037/5000000000 : ℝ)*x 0 + (3229832773/10000000000 : ℝ)*x 1 + (1047375523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2282883037/5000000000 : ℝ)^6 ≤ (39031603025311/100000000000000 : ℝ)^5 := by
    have hnat : (2282883037 : ℕ)^6*100000000000000^5 ≤ 39031603025311^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282883037 5000000000 39031603025311 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3229832773/10000000000 : ℝ)^6 ≤ (12882081686383/50000000000000 : ℝ)^5 := by
    have hnat : (3229832773 : ℕ)^6*50000000000000^5 ≤ 12882081686383^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3229832773 10000000000 12882081686383 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047375523/2500000000 : ℝ)^6 ≤ (35204233585697/100000000000000 : ℝ)^5 := by
    have hnat : (1047375523 : ℕ)^6*100000000000000^5 ≤ 35204233585697^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047375523 2500000000 35204233585697 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2282883037/5000000000 : ℝ), (3229832773/10000000000 : ℝ), (1047375523/2500000000 : ℝ)] ![(39031603025311/100000000000000 : ℝ), (12882081686383/50000000000000 : ℝ), (35204233585697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2282883037/5000000000 : ℝ)|^6 ≤ (39031603025311/100000000000000 : ℝ)^5
        have hw : |(-2282883037/5000000000 : ℝ)|=(2282883037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3229832773/10000000000 : ℝ)|^6 ≤ (12882081686383/50000000000000 : ℝ)^5
        have hw : |(3229832773/10000000000 : ℝ)|=(3229832773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047375523/2500000000 : ℝ)|^6 ≤ (35204233585697/100000000000000 : ℝ)^5
        have hw : |(1047375523/2500000000 : ℝ)|=(1047375523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (59403783/156250000 : ℝ)*x 0 + (-111317841/312500000 : ℝ)*x 1 + (4629892999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59403783/156250000 : ℝ)^6 ≤ (31332344453197/100000000000000 : ℝ)^5 := by
    have hnat : (59403783 : ℕ)^6*100000000000000^5 ≤ 31332344453197^5*156250000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59403783 156250000 31332344453197 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111317841/312500000 : ℝ)^6 ≤ (28977285756029/100000000000000 : ℝ)^5 := by
    have hnat : (111317841 : ℕ)^6*100000000000000^5 ≤ 28977285756029^5*312500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111317841 312500000 28977285756029 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4629892999/10000000000 : ℝ)^6 ≤ (39690369775869/100000000000000 : ℝ)^5 := by
    have hnat : (4629892999 : ℕ)^6*100000000000000^5 ≤ 39690369775869^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4629892999 10000000000 39690369775869 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(59403783/156250000 : ℝ), (-111317841/312500000 : ℝ), (4629892999/10000000000 : ℝ)] ![(31332344453197/100000000000000 : ℝ), (28977285756029/100000000000000 : ℝ), (39690369775869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(59403783/156250000 : ℝ)|^6 ≤ (31332344453197/100000000000000 : ℝ)^5
        have hw : |(59403783/156250000 : ℝ)|=(59403783/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111317841/312500000 : ℝ)|^6 ≤ (28977285756029/100000000000000 : ℝ)^5
        have hw : |(-111317841/312500000 : ℝ)|=(111317841/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4629892999/10000000000 : ℝ)|^6 ≤ (39690369775869/100000000000000 : ℝ)^5
        have hw : |(4629892999/10000000000 : ℝ)|=(4629892999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (44601327/62500000 : ℝ)*x 0 + (3574031181/10000000000 : ℝ)*x 1 + (-142515687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44601327/62500000 : ℝ)^6 ≤ (66705449566697/100000000000000 : ℝ)^5 := by
    have hnat : (44601327 : ℕ)^6*100000000000000^5 ≤ 66705449566697^5*62500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44601327 62500000 66705449566697 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3574031181/10000000000 : ℝ)^6 ≤ (29093100321561/100000000000000 : ℝ)^5 := by
    have hnat : (3574031181 : ℕ)^6*100000000000000^5 ≤ 29093100321561^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574031181 10000000000 29093100321561 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142515687/2000000000 : ℝ)^6 ≤ (840290020307/20000000000000 : ℝ)^5 := by
    have hnat : (142515687 : ℕ)^6*20000000000000^5 ≤ 840290020307^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142515687 2000000000 840290020307 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44601327/62500000 : ℝ), (3574031181/10000000000 : ℝ), (-142515687/2000000000 : ℝ)] ![(66705449566697/100000000000000 : ℝ), (29093100321561/100000000000000 : ℝ), (840290020307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44601327/62500000 : ℝ)|^6 ≤ (66705449566697/100000000000000 : ℝ)^5
        have hw : |(44601327/62500000 : ℝ)|=(44601327/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3574031181/10000000000 : ℝ)|^6 ≤ (29093100321561/100000000000000 : ℝ)^5
        have hw : |(3574031181/10000000000 : ℝ)|=(3574031181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142515687/2000000000 : ℝ)|^6 ≤ (840290020307/20000000000000 : ℝ)^5
        have hw : |(-142515687/2000000000 : ℝ)|=(142515687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s0_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-13201/10000000000 : ℝ)*x 0 + (6979376291/10000000000 : ℝ)*x 1 + (2087094237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13201/10000000000 : ℝ)^6 ≤ (8804977/100000000000000 : ℝ)^5 := by
    have hnat : (13201 : ℕ)^6*100000000000000^5 ≤ 8804977^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13201 10000000000 8804977 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6979376291/10000000000 : ℝ)^6 ≤ (64950116826217/100000000000000 : ℝ)^5 := by
    have hnat : (6979376291 : ℕ)^6*100000000000000^5 ≤ 64950116826217^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6979376291 10000000000 64950116826217 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087094237/5000000000 : ℝ)^6 ≤ (35049874353809/100000000000000 : ℝ)^5 := by
    have hnat : (2087094237 : ℕ)^6*100000000000000^5 ≤ 35049874353809^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087094237 5000000000 35049874353809 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13201/10000000000 : ℝ), (6979376291/10000000000 : ℝ), (2087094237/5000000000 : ℝ)] ![(8804977/100000000000000 : ℝ), (64950116826217/100000000000000 : ℝ), (35049874353809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13201/10000000000 : ℝ)|^6 ≤ (8804977/100000000000000 : ℝ)^5
        have hw : |(-13201/10000000000 : ℝ)|=(13201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6979376291/10000000000 : ℝ)|^6 ≤ (64950116826217/100000000000000 : ℝ)^5
        have hw : |(6979376291/10000000000 : ℝ)|=(6979376291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2087094237/5000000000 : ℝ)|^6 ≤ (35049874353809/100000000000000 : ℝ)^5
        have hw : |(2087094237/5000000000 : ℝ)|=(2087094237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s1_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-3866081431/10000000000 : ℝ)*x 0 + (1620839753/5000000000 : ℝ)*x 1 + (4868138163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3866081431/10000000000 : ℝ)^6 ≤ (31968716239999/100000000000000 : ℝ)^5 := by
    have hnat : (3866081431 : ℕ)^6*100000000000000^5 ≤ 31968716239999^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866081431 10000000000 31968716239999 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1620839753/5000000000 : ℝ)^6 ≤ (12938802828733/50000000000000 : ℝ)^5 := by
    have hnat : (1620839753 : ℕ)^6*50000000000000^5 ≤ 12938802828733^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620839753 5000000000 12938802828733 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4868138163/10000000000 : ℝ)^6 ≤ (42153678079791/100000000000000 : ℝ)^5 := by
    have hnat : (4868138163 : ℕ)^6*100000000000000^5 ≤ 42153678079791^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4868138163 10000000000 42153678079791 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3866081431/10000000000 : ℝ), (1620839753/5000000000 : ℝ), (4868138163/10000000000 : ℝ)] ![(31968716239999/100000000000000 : ℝ), (12938802828733/50000000000000 : ℝ), (42153678079791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3866081431/10000000000 : ℝ)|^6 ≤ (31968716239999/100000000000000 : ℝ)^5
        have hw : |(-3866081431/10000000000 : ℝ)|=(3866081431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1620839753/5000000000 : ℝ)|^6 ≤ (12938802828733/50000000000000 : ℝ)^5
        have hw : |(1620839753/5000000000 : ℝ)|=(1620839753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4868138163/10000000000 : ℝ)|^6 ≤ (42153678079791/100000000000000 : ℝ)^5
        have hw : |(4868138163/10000000000 : ℝ)|=(4868138163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s1_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3926323683/10000000000 : ℝ)*x 0 + (-101139047/312500000 : ℝ)*x 1 + (4815283603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3926323683/10000000000 : ℝ)^6 ≤ (16283708671143/50000000000000 : ℝ)^5 := by
    have hnat : (3926323683 : ℕ)^6*50000000000000^5 ≤ 16283708671143^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3926323683 10000000000 16283708671143 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101139047/312500000 : ℝ)^6 ≤ (25827513814223/100000000000000 : ℝ)^5 := by
    have hnat : (101139047 : ℕ)^6*100000000000000^5 ≤ 25827513814223^5*312500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101139047 312500000 25827513814223 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4815283603/10000000000 : ℝ)^6 ≤ (41605068820423/100000000000000 : ℝ)^5 := by
    have hnat : (4815283603 : ℕ)^6*100000000000000^5 ≤ 41605068820423^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815283603 10000000000 41605068820423 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3926323683/10000000000 : ℝ), (-101139047/312500000 : ℝ), (4815283603/10000000000 : ℝ)] ![(16283708671143/50000000000000 : ℝ), (25827513814223/100000000000000 : ℝ), (41605068820423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3926323683/10000000000 : ℝ)|^6 ≤ (16283708671143/50000000000000 : ℝ)^5
        have hw : |(3926323683/10000000000 : ℝ)|=(3926323683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101139047/312500000 : ℝ)|^6 ≤ (25827513814223/100000000000000 : ℝ)^5
        have hw : |(-101139047/312500000 : ℝ)|=(101139047/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4815283603/10000000000 : ℝ)|^6 ≤ (41605068820423/100000000000000 : ℝ)^5
        have hw : |(4815283603/10000000000 : ℝ)|=(4815283603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s1_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (191481999/400000000 : ℝ)*x 0 + (5355884449/10000000000 : ℝ)*x 1 + (-819542443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191481999/400000000 : ℝ)^6 ≤ (41312507307749/100000000000000 : ℝ)^5 := by
    have hnat : (191481999 : ℕ)^6*100000000000000^5 ≤ 41312507307749^5*400000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191481999 400000000 41312507307749 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5355884449/10000000000 : ℝ)^6 ≤ (47271288302723/100000000000000 : ℝ)^5 := by
    have hnat : (5355884449 : ℕ)^6*100000000000000^5 ≤ 47271288302723^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355884449 10000000000 47271288302723 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (819542443/5000000000 : ℝ)^6 ≤ (11416204370249/100000000000000 : ℝ)^5 := by
    have hnat : (819542443 : ℕ)^6*100000000000000^5 ≤ 11416204370249^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819542443 5000000000 11416204370249 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(191481999/400000000 : ℝ), (5355884449/10000000000 : ℝ), (-819542443/5000000000 : ℝ)] ![(41312507307749/100000000000000 : ℝ), (47271288302723/100000000000000 : ℝ), (11416204370249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(191481999/400000000 : ℝ)|^6 ≤ (41312507307749/100000000000000 : ℝ)^5
        have hw : |(191481999/400000000 : ℝ)|=(191481999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5355884449/10000000000 : ℝ)|^6 ≤ (47271288302723/100000000000000 : ℝ)^5
        have hw : |(5355884449/10000000000 : ℝ)|=(5355884449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-819542443/5000000000 : ℝ)|^6 ≤ (11416204370249/100000000000000 : ℝ)^5
        have hw : |(-819542443/5000000000 : ℝ)|=(819542443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330082_s1_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1580870039/10000000000 : ℝ)*x 0 + (2093226971/5000000000 : ℝ)*x 1 + (5974356521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1580870039/10000000000 : ℝ)^6 ≤ (10931390339607/100000000000000 : ℝ)^5 := by
    have hnat : (1580870039 : ℕ)^6*100000000000000^5 ≤ 10931390339607^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580870039 10000000000 10931390339607 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2093226971/5000000000 : ℝ)^6 ≤ (35173499630199/100000000000000 : ℝ)^5 := by
    have hnat : (2093226971 : ℕ)^6*100000000000000^5 ≤ 35173499630199^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093226971 5000000000 35173499630199 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5974356521/10000000000 : ℝ)^6 ≤ (1347377750409/2500000000000 : ℝ)^5 := by
    have hnat : (5974356521 : ℕ)^6*2500000000000^5 ≤ 1347377750409^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5974356521 10000000000 1347377750409 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1580870039/10000000000 : ℝ), (2093226971/5000000000 : ℝ), (5974356521/10000000000 : ℝ)] ![(10931390339607/100000000000000 : ℝ), (35173499630199/100000000000000 : ℝ), (1347377750409/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1580870039/10000000000 : ℝ)|^6 ≤ (10931390339607/100000000000000 : ℝ)^5
        have hw : |(1580870039/10000000000 : ℝ)|=(1580870039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2093226971/5000000000 : ℝ)|^6 ≤ (35173499630199/100000000000000 : ℝ)^5
        have hw : |(2093226971/5000000000 : ℝ)|=(2093226971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5974356521/10000000000 : ℝ)|^6 ≤ (1347377750409/2500000000000 : ℝ)^5
        have hw : |(5974356521/10000000000 : ℝ)|=(5974356521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330082 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((926522607/2500000000 : ℝ)*X 1 0+(-2782411547/10000000000 : ℝ)*X 1 1+(2715559411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((149050217/250000000 : ℝ)*X 2 0+(1029635053/2000000000 : ℝ)*X 2 1+(-121774731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3157561371/10000000000 : ℝ)*X 0 0+(807977861/5000000000 : ℝ)*X 0 1+(6867512303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((251859199/625000000 : ℝ)*X 1 0+(-1018339117/10000000000 : ℝ)*X 1 1+(652882529/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4330976523/10000000000 : ℝ)*X 2 0+(6776741941/10000000000 : ℝ)*X 2 1+(-9650983/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((4217941/1250000000 : ℝ)*X 0 0+(4209696717/5000000000 : ℝ)*X 0 1+(491172211/2000000000 : ℝ)*X 0 2+(4217941/1250000000 : ℝ)*X 1 0+(4209696717/5000000000 : ℝ)*X 1 1+(491172211/2000000000 : ℝ)*X 1 2+(4217941/1250000000 : ℝ)*X 2 0+(4209696717/5000000000 : ℝ)*X 2 1+(491172211/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2704433333/10000000000 : ℝ)*X 0 0+(2004968133/10000000000 : ℝ)*X 0 1+(3475827391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5987041231/10000000000 : ℝ)*X 1 0+(-93121947/312500000 : ℝ)*X 1 1+(289325509/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((741239169/1000000000 : ℝ)*X 2 0+(343031903/1000000000 : ℝ)*X 2 1+(-92150751/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((8661/5000000000 : ℝ)*X 0 0+(4236866113/10000000000 : ℝ)*X 0 1+(6922691217/10000000000 : ℝ)*X 0 2+(8661/5000000000 : ℝ)*X 1 0+(4236866113/10000000000 : ℝ)*X 1 1+(6922691217/10000000000 : ℝ)*X 1 2+(8661/5000000000 : ℝ)*X 2 0+(4236866113/10000000000 : ℝ)*X 2 1+(6922691217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-2282883037/5000000000 : ℝ)*X 0 0+(3229832773/10000000000 : ℝ)*X 0 1+(1047375523/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((59403783/156250000 : ℝ)*X 1 0+(-111317841/312500000 : ℝ)*X 1 1+(4629892999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((44601327/62500000 : ℝ)*X 2 0+(3574031181/10000000000 : ℝ)*X 2 1+(-142515687/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-13201/10000000000 : ℝ)*X 0 0+(6979376291/10000000000 : ℝ)*X 0 1+(2087094237/5000000000 : ℝ)*X 0 2+(-13201/10000000000 : ℝ)*X 1 0+(6979376291/10000000000 : ℝ)*X 1 1+(2087094237/5000000000 : ℝ)*X 1 2+(-13201/10000000000 : ℝ)*X 2 0+(6979376291/10000000000 : ℝ)*X 2 1+(2087094237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((22931/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22931/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4722009025740170085897/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35491494743/40000000000 : ℝ)*(base7) + (194417/200000000000 : ℝ)*(base19) + (200201485583/1000000000000 : ℝ)*(base49) + (28771/40000000000 : ℝ)*(base53) + (190951000129/1000000000000 : ℝ)*(base60) + (470973255337/250000000000 : ℝ)*(major_s0_0) + (470973255337/250000000000 : ℝ)*(major_s0_1) + (235486537759/125000000000 : ℝ)*(major_s0_2) + (308716660499/125000000000 : ℝ)*(sp_s0_7) + (3087223857/1250000000 : ℝ)*(sp_s0_8) + (2469780776961/1000000000000 : ℝ)*(sp_s0_9) + (1714451409719/1000000000000 : ℝ)*(sp_s0_13) + (46773693/1000000000000 : ℝ)*(sp_s0_14) + (923247/1000000000000 : ℝ)*(sp_s0_27) + (82716496439/100000000000 : ℝ)*(f.failure) + (2469780776961/1000000000000 : ℝ)*(f.sum) + (501855351633501/2500000000000000000000000000 : ℝ)*base62 + (132019850602119/1250000000000000000000000000 : ℝ)*base64 + (5241284475463/2500000000000000000000000000 : ℝ)*base66 + (375457859062841/1250000000000000000000000000 : ℝ)*base69 + (1364932306179701/2500000000000000000000000000 : ℝ)*base70 + (48285964259183/2500000000000000000000000000 : ℝ)*base73 + (1157582982990817/2500000000000000000000000000 : ℝ)*base75 + (95935940774537/2500000000000000000000000000 : ℝ)*base77 + (3998140924157/62500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (8433/10000000000000000 : ℝ)*base86 + (8433/10000000000000000 : ℝ)*base88 + (1567/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((27967/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(27967/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (74196955349699439931263/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1307873924587/1000000000000 : ℝ)*(base7) + (144621/250000000000 : ℝ)*(base40) + (5847/31250000000 : ℝ)*(base49) + (144271575723/500000000000 : ℝ)*(base60) + (2175703237181/1000000000000 : ℝ)*(major_s0_0) + (2175703237181/1000000000000 : ℝ)*(major_s0_1) + (2175703237181/1000000000000 : ℝ)*(major_s0_2) + (32541121/1000000000000 : ℝ)*(sp_s0_1) + (4897397/500000000000 : ℝ)*(sp_s0_2) + (63834481/500000000000 : ℝ)*(sp_s0_7) + (337744982101/125000000000 : ℝ)*(sp_s0_14) + (2702054984649/1000000000000 : ℝ)*(sp_s0_15) + (84439929093/31250000000 : ℝ)*(sp_s0_16) + (2263164628631/1000000000000 : ℝ)*(sp_s0_20) + (238822676011/250000000000 : ℝ)*(f.failure) + (270208752577/100000000000 : ℝ)*(f.sum) + (24735023028909/250000000000000000000000000 : ℝ)*base62 + (2584211665310421/10000000000000000000000000000 : ℝ)*base64 + (1341896229533219/10000000000000000000000000000 : ℝ)*base66 + (3549931928466781/10000000000000000000000000000 : ℝ)*base68 + (10243077871091/250000000000000000000000000 : ℝ)*base70 + (44442866689579/10000000000000000000000000000 : ℝ)*base73 + (4380017207689579/10000000000000000000000000000 : ℝ)*base74 + (3140091953533219/10000000000000000000000000000 : ℝ)*base76 + (60794612153909/250000000000000000000000000 : ℝ)*base79 + (8283/25000000000000000 : ℝ)*base87 + (8283/25000000000000000 : ℝ)*base89 + (8283/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(48477/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(48477/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38124626046063642298227/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1323574613929/1000000000000 : ℝ)*(base7) + (131193781597/500000000000 : ℝ)*(base39) + (32497/20000000000 : ℝ)*(base44) + (2592463139069/1000000000000 : ℝ)*(major_s0_0) + (2592461514219/1000000000000 : ℝ)*(major_s0_1) + (2592463139069/1000000000000 : ℝ)*(major_s0_2) + (2879263/500000000000 : ℝ)*(sp_s0_2) + (2672693/200000000000 : ℝ)*(sp_s0_13) + (6365617/1000000000000 : ℝ)*(sp_s0_15) + (25859929/500000000000 : ℝ)*(sp_s0_16) + (836072624069/250000000000 : ℝ)*(sp_s0_21) + (209017656613/62500000000 : ℝ)*(sp_s0_22) + (836058254473/250000000000 : ℝ)*(sp_s0_23) + (49236759939/20000000000 : ℝ)*(sp_s0_27) + (142284796417/125000000000 : ℝ)*(f.failure) + (836072624069/250000000000 : ℝ)*(f.sum) + (5945457101249/1000000000000000000000000000 : ℝ)*base62 + (447615477615829/10000000000000000000000000000 : ℝ)*base64 + (3221062183475381/10000000000000000000000000000 : ℝ)*base66 + (1018948153090531/10000000000000000000000000000 : ℝ)*base69 + (113759510292659/250000000000000000000000000 : ℝ)*base70 + (164349466615829/10000000000000000000000000000 : ℝ)*base72 + (2212966881103021/10000000000000000000000000000 : ℝ)*base74 + (473405588090531/10000000000000000000000000000 : ℝ)*base76 + (25327483909121/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1499/12500000000000000 : ℝ)*base86 + (1499/12500000000000000 : ℝ)*base88 + (1499/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (22931/50000 : ℝ) ^ (95/16 : ℝ) ≤ (976960777138187061/100000000000000000000 : ℝ) := by
    have hpowers : (22931/50000 : ℝ)^95 ≤ (976960777138187061/100000000000000000000 : ℝ)^16 := by
      have hnat : (22931 : ℕ)^95*100000000000000000000^16 ≤ 976960777138187061^16*50000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22931 50000 976960777138187061 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22931/50000 : ℝ)) (X := (976960777138187061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100976960777138187061/100000000000000000000 : ℝ) ≤ (10016387634068331/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (100976960777138187061/100000000000000000000 : ℝ)^16 ≤ (10016387634068331/10000000000000000 : ℝ)^95 := by
      have hnat : (100976960777138187061 : ℕ)^16*10000000000000000^95 ≤ 10016387634068331^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100976960777138187061 100000000000000000000 10016387634068331 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016387634068331/10000000000000000 : ℝ)) (X := (100976960777138187061/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50976960777138187061/50000000000000000000 : ℝ) ≤ (5016321972957217/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (50976960777138187061/50000000000000000000 : ℝ)^16 ≤ (5016321972957217/5000000000000000 : ℝ)^95 := by
      have hnat : (50976960777138187061 : ℕ)^16*5000000000000000^95 ≤ 5016321972957217^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50976960777138187061 50000000000000000000 5016321972957217 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5016321972957217/5000000000000000 : ℝ)) (X := (50976960777138187061/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(16387634068331/4586200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16256311846103/4586200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (22931/50000 : ℝ)) (alpha := (16387634068331/4586200000000000 : ℝ)) (beta := (16256311846103/4586200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22931/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(16387634068331/4586200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16256311846103/4586200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (27967/50000 : ℝ) ^ (95/16 : ℝ) ≤ (793899511569250629/25000000000000000000 : ℝ) := by
    have hpowers : (27967/50000 : ℝ)^95 ≤ (793899511569250629/25000000000000000000 : ℝ)^16 := by
      have hnat : (27967 : ℕ)^95*25000000000000000000^16 ≤ 793899511569250629^16*50000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27967 50000 793899511569250629 25000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27967/50000 : ℝ)) (X := (793899511569250629/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25793899511569250629/25000000000000000000 : ℝ) ≤ (402111638345169/400000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (25793899511569250629/25000000000000000000 : ℝ)^16 ≤ (402111638345169/400000000000000 : ℝ)^95 := by
      have hnat : (25793899511569250629 : ℕ)^16*400000000000000^95 ≤ 402111638345169^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25793899511569250629 25000000000000000000 402111638345169 400000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402111638345169/400000000000000 : ℝ)) (X := (25793899511569250629/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13293899511569250629/12500000000000000000 : ℝ) ≤ (505212379638837/500000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (13293899511569250629/12500000000000000000 : ℝ)^16 ≤ (505212379638837/500000000000000 : ℝ)^95 := by
      have hnat : (13293899511569250629 : ℕ)^16*500000000000000^95 ≤ 505212379638837^95*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13293899511569250629 12500000000000000000 505212379638837 500000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505212379638837/500000000000000 : ℝ)) (X := (13293899511569250629/12500000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2111638345169/223736000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(10291326829503/1118680000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (27967/50000 : ℝ)) (alpha := (2111638345169/223736000000000 : ℝ)) (beta := (10291326829503/1118680000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (27967/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2111638345169/223736000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(10291326829503/1118680000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (48477/100000 : ℝ) ^ (95/16 : ℝ) ≤ (339475501997116521/25000000000000000000 : ℝ) := by
    have hpowers : (48477/100000 : ℝ)^95 ≤ (339475501997116521/25000000000000000000 : ℝ)^16 := by
      have hnat : (48477 : ℕ)^95*25000000000000000000^16 ≤ 339475501997116521^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48477 100000 339475501997116521 25000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48477/100000 : ℝ)) (X := (339475501997116521/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25339475501997116521/25000000000000000000 : ℝ) ≤ (1002274186492599/1000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (25339475501997116521/25000000000000000000 : ℝ)^16 ≤ (1002274186492599/1000000000000000 : ℝ)^95 := by
      have hnat : (25339475501997116521 : ℕ)^16*1000000000000000^95 ≤ 1002274186492599^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25339475501997116521 25000000000000000000 1002274186492599 1000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002274186492599/1000000000000000 : ℝ)) (X := (25339475501997116521/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12839475501997116521/12500000000000000000 : ℝ) ≤ (10045231763971647/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (12839475501997116521/12500000000000000000 : ℝ)^16 ≤ (10045231763971647/10000000000000000 : ℝ)^95 := by
      have hnat : (12839475501997116521 : ℕ)^16*10000000000000000^95 ≤ 10045231763971647^95*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12839475501997116521 12500000000000000000 10045231763971647 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045231763971647/10000000000000000 : ℝ)) (X := (12839475501997116521/12500000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2274186492599/484770000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(7496633015219/1615900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (48477/100000 : ℝ)) (alpha := (2274186492599/484770000000000 : ℝ)) (beta := (7496633015219/1615900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (48477/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2274186492599/484770000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(7496633015219/1615900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3866081431/10000000000 : ℝ)*X 0 0+(1620839753/5000000000 : ℝ)*X 0 1+(4868138163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3926323683/10000000000 : ℝ)*X 1 0+(-101139047/312500000 : ℝ)*X 1 1+(4815283603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((191481999/400000000 : ℝ)*X 2 0+(5355884449/10000000000 : ℝ)*X 2 1+(-819542443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1580870039/10000000000 : ℝ)*X 0 0+(2093226971/5000000000 : ℝ)*X 0 1+(5974356521/10000000000 : ℝ)*X 0 2+(1580870039/10000000000 : ℝ)*X 1 0+(2093226971/5000000000 : ℝ)*X 1 1+(5974356521/10000000000 : ℝ)*X 1 2+(1580870039/10000000000 : ℝ)*X 2 0+(2093226971/5000000000 : ℝ)*X 2 1+(5974356521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330082_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-533259/50000 : ℝ) < ((-227753/100000 : ℝ)*P 0+(-227753/100000 : ℝ)*P 1+(-227753/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-533259/50000 : ℝ) < (-194276702321812616824735782404903/18527101450000000000000000000000 : ℝ) := by norm_num
    linear_combination (1471/1000000000000 : ℝ)*(base7) + (64789/500000000000 : ℝ)*(base16) + (12357/250000000000 : ℝ)*(base19) + (51609/250000000000 : ℝ)*(base23) + (202082659/40000000000 : ℝ)*(base40) + (106311075127/250000000000 : ℝ)*(base49) + (32641/1000000000000 : ℝ)*(base53) + (92045856993/125000000000 : ℝ)*(base60) + (227753/100000 : ℝ)*(major_s1_0) + (227753/100000 : ℝ)*(major_s1_1) + (2277529967359/1000000000000 : ℝ)*(major_s1_2) + (3495360584571/1000000000000 : ℝ)*(sp_s1_0) + (699072081113/200000000000 : ℝ)*(sp_s1_1) + (436920051347/125000000000 : ℝ)*(sp_s1_2) + (1000000001471/1000000000000 : ℝ)*(sp_s1_6) + (873840154303/250000000000 : ℝ)*(f.sum) + (1675882063801049941/13557562590000000000000000000000 : ℝ)*base63 + (1007050564489901/1615900000000000000000000000 : ℝ)*base65 + (3114545893961/34958750000000000000000000 : ℝ)*base66 + (246594656055031/484770000000000000000000000 : ℝ)*base69 + (5490460043982628771/37054202900000000000000000000000 : ℝ)*base71 + (45435294072467/114655000000000000000000000 : ℝ)*base73 + (4020808819023/279670000000000000000000000 : ℝ)*base74 + (51917613065843/114655000000000000000000000 : ℝ)*base76 + (730065027050397633/1282622554000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p030_b041 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 82 ≤ c.val) (hhi : c.val < 83)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=82 := by omega
  rcases hc with rfl
  · exact collision_c330082 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 82 ≤ c.val) (hhi : c.val < 83)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b041 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

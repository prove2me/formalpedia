-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b009
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:14:54.058853+00:00
-- url     : https://prove2.me/submissions/76bf7d66-8078-41cc-bfda-579dd1701341

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
theorem collision_support_c327022_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-692477841/2500000000 : ℝ)*x 0 + (1162502993/2500000000 : ℝ)*x 1 + (-4645394833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (692477841/2500000000 : ℝ)^91 ≤ (21063243969047/100000000000000 : ℝ)^75 := by
    have hnat : (692477841 : ℕ)^91*100000000000000^75 ≤ 21063243969047^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692477841 2500000000 21063243969047 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1162502993/2500000000 : ℝ)^91 ≤ (39492164697487/100000000000000 : ℝ)^75 := by
    have hnat : (1162502993 : ℕ)^91*100000000000000^75 ≤ 39492164697487^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162502993 2500000000 39492164697487 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4645394833/10000000000 : ℝ)^91 ≤ (39444591325517/100000000000000 : ℝ)^75 := by
    have hnat : (4645394833 : ℕ)^91*100000000000000^75 ≤ 39444591325517^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4645394833 10000000000 39444591325517 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-692477841/2500000000 : ℝ), (1162502993/2500000000 : ℝ), (-4645394833/10000000000 : ℝ)] ![(21063243969047/100000000000000 : ℝ), (39492164697487/100000000000000 : ℝ), (39444591325517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-692477841/2500000000 : ℝ)|^91 ≤ (21063243969047/100000000000000 : ℝ)^75
        have hw : |(-692477841/2500000000 : ℝ)|=(692477841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1162502993/2500000000 : ℝ)|^91 ≤ (39492164697487/100000000000000 : ℝ)^75
        have hw : |(1162502993/2500000000 : ℝ)|=(1162502993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4645394833/10000000000 : ℝ)|^91 ≤ (39444591325517/100000000000000 : ℝ)^75
        have hw : |(-4645394833/10000000000 : ℝ)|=(4645394833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327022_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (68299641/100000000 : ℝ)*x 0 + (-130455883/1250000000 : ℝ)*x 1 + (-3767411029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68299641/100000000 : ℝ)^91 ≤ (62964295829261/100000000000000 : ℝ)^75 := by
    have hnat : (68299641 : ℕ)^91*100000000000000^75 ≤ 62964295829261^75*100000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68299641 100000000 62964295829261 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130455883/1250000000 : ℝ)^91 ≤ (6444339852569/100000000000000 : ℝ)^75 := by
    have hnat : (130455883 : ℕ)^91*100000000000000^75 ≤ 6444339852569^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130455883 1250000000 6444339852569 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3767411029/10000000000 : ℝ)^91 ≤ (3823920537257/12500000000000 : ℝ)^75 := by
    have hnat : (3767411029 : ℕ)^91*12500000000000^75 ≤ 3823920537257^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3767411029 10000000000 3823920537257 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68299641/100000000 : ℝ), (-130455883/1250000000 : ℝ), (-3767411029/10000000000 : ℝ)] ![(62964295829261/100000000000000 : ℝ), (6444339852569/100000000000000 : ℝ), (3823920537257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68299641/100000000 : ℝ)|^91 ≤ (62964295829261/100000000000000 : ℝ)^75
        have hw : |(68299641/100000000 : ℝ)|=(68299641/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130455883/1250000000 : ℝ)|^91 ≤ (6444339852569/100000000000000 : ℝ)^75
        have hw : |(-130455883/1250000000 : ℝ)|=(130455883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3767411029/10000000000 : ℝ)|^91 ≤ (3823920537257/12500000000000 : ℝ)^75
        have hw : |(-3767411029/10000000000 : ℝ)|=(3767411029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327022_s0_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2461019371/10000000000 : ℝ)*x 0 + (2710834039/5000000000 : ℝ)*x 1 + (825470939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2461019371/10000000000 : ℝ)^91 ≤ (4562045169299/25000000000000 : ℝ)^75 := by
    have hnat : (2461019371 : ℕ)^91*25000000000000^75 ≤ 4562045169299^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2461019371 10000000000 4562045169299 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710834039/5000000000 : ℝ)^91 ≤ (47578924065943/100000000000000 : ℝ)^75 := by
    have hnat : (2710834039 : ℕ)^91*100000000000000^75 ≤ 47578924065943^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710834039 5000000000 47578924065943 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825470939/2000000000 : ℝ)^91 ≤ (17086447617751/50000000000000 : ℝ)^75 := by
    have hnat : (825470939 : ℕ)^91*50000000000000^75 ≤ 17086447617751^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825470939 2000000000 17086447617751 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2461019371/10000000000 : ℝ), (2710834039/5000000000 : ℝ), (825470939/2000000000 : ℝ)] ![(4562045169299/25000000000000 : ℝ), (47578924065943/100000000000000 : ℝ), (17086447617751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2461019371/10000000000 : ℝ)|^91 ≤ (4562045169299/25000000000000 : ℝ)^75
        have hw : |(2461019371/10000000000 : ℝ)|=(2461019371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710834039/5000000000 : ℝ)|^91 ≤ (47578924065943/100000000000000 : ℝ)^75
        have hw : |(2710834039/5000000000 : ℝ)|=(2710834039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(825470939/2000000000 : ℝ)|^91 ≤ (17086447617751/50000000000000 : ℝ)^75
        have hw : |(825470939/2000000000 : ℝ)|=(825470939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327022_s0_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3445272399/10000000000 : ℝ)*x 0 + (3246601367/5000000000 : ℝ)*x 1 + (-1900413683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3445272399/10000000000 : ℝ)^91 ≤ (27447192322327/100000000000000 : ℝ)^75 := by
    have hnat : (3445272399 : ℕ)^91*100000000000000^75 ≤ 27447192322327^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3445272399 10000000000 27447192322327 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3246601367/5000000000 : ℝ)^91 ≤ (59217519025003/100000000000000 : ℝ)^75 := by
    have hnat : (3246601367 : ℕ)^91*100000000000000^75 ≤ 59217519025003^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3246601367 5000000000 59217519025003 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1900413683/10000000000 : ℝ)^91 ≤ (2667057728287/20000000000000 : ℝ)^75 := by
    have hnat : (1900413683 : ℕ)^91*20000000000000^75 ≤ 2667057728287^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900413683 10000000000 2667057728287 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3445272399/10000000000 : ℝ), (3246601367/5000000000 : ℝ), (-1900413683/10000000000 : ℝ)] ![(27447192322327/100000000000000 : ℝ), (59217519025003/100000000000000 : ℝ), (2667057728287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3445272399/10000000000 : ℝ)|^91 ≤ (27447192322327/100000000000000 : ℝ)^75
        have hw : |(3445272399/10000000000 : ℝ)|=(3445272399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3246601367/5000000000 : ℝ)|^91 ≤ (59217519025003/100000000000000 : ℝ)^75
        have hw : |(3246601367/5000000000 : ℝ)|=(3246601367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1900413683/10000000000 : ℝ)|^91 ≤ (2667057728287/20000000000000 : ℝ)^75
        have hw : |(-1900413683/10000000000 : ℝ)|=(1900413683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327022 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-692477841/2500000000 : ℝ)*X 0 0+(1162502993/2500000000 : ℝ)*X 0 1+(-4645394833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327022_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((68299641/100000000 : ℝ)*X 1 0+(-130455883/1250000000 : ℝ)*X 1 1+(-3767411029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327022_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2461019371/10000000000 : ℝ)*X 2 0+(2710834039/5000000000 : ℝ)*X 2 1+(825470939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327022_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3445272399/10000000000 : ℝ)*X 0 0+(3246601367/5000000000 : ℝ)*X 0 1+(-1900413683/10000000000 : ℝ)*X 0 2+(3445272399/10000000000 : ℝ)*X 1 0+(3246601367/5000000000 : ℝ)*X 1 1+(-1900413683/10000000000 : ℝ)*X 1 2+(3445272399/10000000000 : ℝ)*X 2 0+(3246601367/5000000000 : ℝ)*X 2 1+(-1900413683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327022_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-96701600393369961274743/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (487/1000000000000 : ℝ)*(base25) + (5437/1000000000000 : ℝ)*(base29) + (530442222217/1000000000000 : ℝ)*(base39) + (43777551943/500000000000 : ℝ)*(base49) + (348738762149/500000000000 : ℝ)*(base50) + (74577612401/500000000000 : ℝ)*(base60) + (211611/100000 : ℝ)*(major_s0_0) + (211611/100000 : ℝ)*(major_s0_1) + (211611/100000 : ℝ)*(major_s0_2) + (3223386672683/1000000000000 : ℝ)*(sp_s0_0) + (1611693334261/500000000000 : ℝ)*(sp_s0_1) + (3223386667057/1000000000000 : ℝ)*(sp_s0_2) + (999999994563/1000000000000 : ℝ)*(sp_s0_6) + (644677333509/200000000000 : ℝ)*(f.sum) + (109444119/400000000000000000000 : ℝ)*base63 + (2125988229/5000000000000000000000 : ℝ)*base64 + (6423340141601/1250000000000000000000 : ℝ)*base67 + (9770993651117/10000000000000000000000 : ℝ)*base68 + (1204860227/5000000000000000000000 : ℝ)*base70 + (2200854327/10000000000000000000000 : ℝ)*base73 + (38818531/625000000000000000000 : ℝ)*base75 + (44533377/625000000000000000000 : ℝ)*base77 + (4670011457/5000000000000000000000 : ℝ)*base79 + (2569/500000000000 : ℝ)*base81 + (977/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c327023_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-24933611/80000000 : ℝ)*x 0 + (542968411/1000000000 : ℝ)*x 1 + (350559733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24933611/80000000 : ℝ)^91 ≤ (12152160718983/50000000000000 : ℝ)^75 := by
    have hnat : (24933611 : ℕ)^91*50000000000000^75 ≤ 12152160718983^75*80000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24933611 80000000 12152160718983 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542968411/1000000000 : ℝ)^91 ≤ (23832145503733/50000000000000 : ℝ)^75 := by
    have hnat : (542968411 : ℕ)^91*50000000000000^75 ≤ 23832145503733^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542968411 1000000000 23832145503733 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (350559733/1000000000 : ℝ)^91 ≤ (28031387544173/100000000000000 : ℝ)^75 := by
    have hnat : (350559733 : ℕ)^91*100000000000000^75 ≤ 28031387544173^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350559733 1000000000 28031387544173 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24933611/80000000 : ℝ), (542968411/1000000000 : ℝ), (350559733/1000000000 : ℝ)] ![(12152160718983/50000000000000 : ℝ), (23832145503733/50000000000000 : ℝ), (28031387544173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24933611/80000000 : ℝ)|^91 ≤ (12152160718983/50000000000000 : ℝ)^75
        have hw : |(-24933611/80000000 : ℝ)|=(24933611/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542968411/1000000000 : ℝ)|^91 ≤ (23832145503733/50000000000000 : ℝ)^75
        have hw : |(542968411/1000000000 : ℝ)|=(542968411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(350559733/1000000000 : ℝ)|^91 ≤ (28031387544173/100000000000000 : ℝ)^75
        have hw : |(350559733/1000000000 : ℝ)|=(350559733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (926531/1562500 : ℝ)*x 0 + (13/1000000000 : ℝ)*x 1 + (1340816149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926531/1562500 : ℝ)^91 ≤ (53042230685853/100000000000000 : ℝ)^75 := by
    have hnat : (926531 : ℕ)^91*100000000000000^75 ≤ 53042230685853^75*1562500^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926531 1562500 53042230685853 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13/1000000000 : ℝ)^91 ≤ (13507/50000000000000 : ℝ)^75 := by
    have hnat : (13 : ℕ)^91*50000000000000^75 ≤ 13507^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13 1000000000 13507 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1340816149/2500000000 : ℝ)^91 ≤ (46957769282239/100000000000000 : ℝ)^75 := by
    have hnat : (1340816149 : ℕ)^91*100000000000000^75 ≤ 46957769282239^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340816149 2500000000 46957769282239 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(926531/1562500 : ℝ), (13/1000000000 : ℝ), (1340816149/2500000000 : ℝ)] ![(53042230685853/100000000000000 : ℝ), (13507/50000000000000 : ℝ), (46957769282239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(926531/1562500 : ℝ)|^91 ≤ (53042230685853/100000000000000 : ℝ)^75
        have hw : |(926531/1562500 : ℝ)|=(926531/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13/1000000000 : ℝ)|^91 ≤ (13507/50000000000000 : ℝ)^75
        have hw : |(13/1000000000 : ℝ)|=(13/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1340816149/2500000000 : ℝ)|^91 ≤ (46957769282239/100000000000000 : ℝ)^75
        have hw : |(1340816149/2500000000 : ℝ)|=(1340816149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (108997357/400000000 : ℝ)*x 0 + (6158592637/10000000000 : ℝ)*x 1 + (-383118237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108997357/400000000 : ℝ)^91 ≤ (5162244766911/25000000000000 : ℝ)^75 := by
    have hnat : (108997357 : ℕ)^91*25000000000000^75 ≤ 5162244766911^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108997357 400000000 5162244766911 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6158592637/10000000000 : ℝ)^91 ≤ (55535522277087/100000000000000 : ℝ)^75 := by
    have hnat : (6158592637 : ℕ)^91*100000000000000^75 ≤ 55535522277087^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6158592637 10000000000 55535522277087 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383118237/1250000000 : ℝ)^91 ≤ (2976937331153/12500000000000 : ℝ)^75 := by
    have hnat : (383118237 : ℕ)^91*12500000000000^75 ≤ 2976937331153^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383118237 1250000000 2976937331153 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108997357/400000000 : ℝ), (6158592637/10000000000 : ℝ), (-383118237/1250000000 : ℝ)] ![(5162244766911/25000000000000 : ℝ), (55535522277087/100000000000000 : ℝ), (2976937331153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108997357/400000000 : ℝ)|^91 ≤ (5162244766911/25000000000000 : ℝ)^75
        have hw : |(108997357/400000000 : ℝ)|=(108997357/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6158592637/10000000000 : ℝ)|^91 ≤ (55535522277087/100000000000000 : ℝ)^75
        have hw : |(6158592637/10000000000 : ℝ)|=(6158592637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-383118237/1250000000 : ℝ)|^91 ≤ (2976937331153/12500000000000 : ℝ)^75
        have hw : |(-383118237/1250000000 : ℝ)|=(383118237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3463736311/10000000000 : ℝ)*x 0 + (2287671443/10000000000 : ℝ)*x 1 + (3085608207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3463736311/10000000000 : ℝ)^91 ≤ (6906442385391/25000000000000 : ℝ)^75 := by
    have hnat : (3463736311 : ℕ)^91*25000000000000^75 ≤ 6906442385391^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3463736311 10000000000 6906442385391 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287671443/10000000000 : ℝ)^91 ≤ (8350278635659/50000000000000 : ℝ)^75 := by
    have hnat : (2287671443 : ℕ)^91*50000000000000^75 ≤ 8350278635659^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287671443 10000000000 8350278635659 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3085608207/5000000000 : ℝ)^91 ≤ (55673673177361/100000000000000 : ℝ)^75 := by
    have hnat : (3085608207 : ℕ)^91*100000000000000^75 ≤ 55673673177361^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3085608207 5000000000 55673673177361 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3463736311/10000000000 : ℝ), (2287671443/10000000000 : ℝ), (3085608207/5000000000 : ℝ)] ![(6906442385391/25000000000000 : ℝ), (8350278635659/50000000000000 : ℝ), (55673673177361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3463736311/10000000000 : ℝ)|^91 ≤ (6906442385391/25000000000000 : ℝ)^75
        have hw : |(-3463736311/10000000000 : ℝ)|=(3463736311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2287671443/10000000000 : ℝ)|^91 ≤ (8350278635659/50000000000000 : ℝ)^75
        have hw : |(2287671443/10000000000 : ℝ)|=(2287671443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3085608207/5000000000 : ℝ)|^91 ≤ (55673673177361/100000000000000 : ℝ)^75
        have hw : |(3085608207/5000000000 : ℝ)|=(3085608207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2411034061/5000000000 : ℝ)*x 0 + (1721/400000000 : ℝ)*x 1 + (3224460667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2411034061/5000000000 : ℝ)^91 ≤ (41272089272681/100000000000000 : ℝ)^75 := by
    have hnat : (2411034061 : ℕ)^91*100000000000000^75 ≤ 41272089272681^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411034061 5000000000 41272089272681 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1721/400000000 : ℝ)^91 ≤ (30825823/100000000000000 : ℝ)^75 := by
    have hnat : (1721 : ℕ)^91*100000000000000^75 ≤ 30825823^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721 400000000 30825823 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3224460667/5000000000 : ℝ)^91 ≤ (14681969974033/25000000000000 : ℝ)^75 := by
    have hnat : (3224460667 : ℕ)^91*25000000000000^75 ≤ 14681969974033^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224460667 5000000000 14681969974033 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2411034061/5000000000 : ℝ), (1721/400000000 : ℝ), (3224460667/5000000000 : ℝ)] ![(41272089272681/100000000000000 : ℝ), (30825823/100000000000000 : ℝ), (14681969974033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2411034061/5000000000 : ℝ)|^91 ≤ (41272089272681/100000000000000 : ℝ)^75
        have hw : |(2411034061/5000000000 : ℝ)|=(2411034061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1721/400000000 : ℝ)|^91 ≤ (30825823/100000000000000 : ℝ)^75
        have hw : |(1721/400000000 : ℝ)|=(1721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3224460667/5000000000 : ℝ)|^91 ≤ (14681969974033/25000000000000 : ℝ)^75
        have hw : |(3224460667/5000000000 : ℝ)|=(3224460667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1047562019/10000000000 : ℝ)*x 0 + (8296924413/10000000000 : ℝ)*x 1 + (-1954450139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047562019/10000000000 : ℝ)^91 ≤ (647368290249/10000000000000 : ℝ)^75 := by
    have hnat : (1047562019 : ℕ)^91*10000000000000^75 ≤ 647368290249^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047562019 10000000000 647368290249 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8296924413/10000000000 : ℝ)^91 ≤ (79729576161529/100000000000000 : ℝ)^75 := by
    have hnat : (8296924413 : ℕ)^91*100000000000000^75 ≤ 79729576161529^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8296924413 10000000000 79729576161529 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954450139/10000000000 : ℝ)^91 ≤ (13796740921363/100000000000000 : ℝ)^75 := by
    have hnat : (1954450139 : ℕ)^91*100000000000000^75 ≤ 13796740921363^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954450139 10000000000 13796740921363 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047562019/10000000000 : ℝ), (8296924413/10000000000 : ℝ), (-1954450139/10000000000 : ℝ)] ![(647368290249/10000000000000 : ℝ), (79729576161529/100000000000000 : ℝ), (13796740921363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047562019/10000000000 : ℝ)|^91 ≤ (647368290249/10000000000000 : ℝ)^75
        have hw : |(1047562019/10000000000 : ℝ)|=(1047562019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8296924413/10000000000 : ℝ)|^91 ≤ (79729576161529/100000000000000 : ℝ)^75
        have hw : |(8296924413/10000000000 : ℝ)|=(8296924413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1954450139/10000000000 : ℝ)|^91 ≤ (13796740921363/100000000000000 : ℝ)^75
        have hw : |(-1954450139/10000000000 : ℝ)|=(1954450139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1107345191/5000000000 : ℝ)*x 0 + (6660772287/10000000000 : ℝ)*x 1 + (2963965043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107345191/5000000000 : ℝ)^91 ≤ (2007042074011/12500000000000 : ℝ)^75 := by
    have hnat : (1107345191 : ℕ)^91*12500000000000^75 ≤ 2007042074011^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107345191 5000000000 2007042074011 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6660772287/10000000000 : ℝ)^91 ≤ (30538415712497/50000000000000 : ℝ)^75 := by
    have hnat : (6660772287 : ℕ)^91*50000000000000^75 ≤ 30538415712497^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6660772287 10000000000 30538415712497 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2963965043/10000000000 : ℝ)^91 ≤ (11433415983033/50000000000000 : ℝ)^75 := by
    have hnat : (2963965043 : ℕ)^91*50000000000000^75 ≤ 11433415983033^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963965043 10000000000 11433415983033 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1107345191/5000000000 : ℝ), (6660772287/10000000000 : ℝ), (2963965043/10000000000 : ℝ)] ![(2007042074011/12500000000000 : ℝ), (30538415712497/50000000000000 : ℝ), (11433415983033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1107345191/5000000000 : ℝ)|^91 ≤ (2007042074011/12500000000000 : ℝ)^75
        have hw : |(1107345191/5000000000 : ℝ)|=(1107345191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6660772287/10000000000 : ℝ)|^91 ≤ (30538415712497/50000000000000 : ℝ)^75
        have hw : |(6660772287/10000000000 : ℝ)|=(6660772287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2963965043/10000000000 : ℝ)|^91 ≤ (11433415983033/50000000000000 : ℝ)^75
        have hw : |(2963965043/10000000000 : ℝ)|=(2963965043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2706443833/5000000000 : ℝ)*x 0 + (2013923181/5000000000 : ℝ)*x 1 + (2581612449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706443833/5000000000 : ℝ)^91 ≤ (1899417909439/4000000000000 : ℝ)^75 := by
    have hnat : (2706443833 : ℕ)^91*4000000000000^75 ≤ 1899417909439^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706443833 5000000000 1899417909439 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013923181/5000000000 : ℝ)^91 ≤ (16587914393721/50000000000000 : ℝ)^75 := by
    have hnat : (2013923181 : ℕ)^91*50000000000000^75 ≤ 16587914393721^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013923181 5000000000 16587914393721 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2581612449/10000000000 : ℝ)^91 ≤ (4834680866621/25000000000000 : ℝ)^75 := by
    have hnat : (2581612449 : ℕ)^91*25000000000000^75 ≤ 4834680866621^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581612449 10000000000 4834680866621 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2706443833/5000000000 : ℝ), (2013923181/5000000000 : ℝ), (2581612449/10000000000 : ℝ)] ![(1899417909439/4000000000000 : ℝ), (16587914393721/50000000000000 : ℝ), (4834680866621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2706443833/5000000000 : ℝ)|^91 ≤ (1899417909439/4000000000000 : ℝ)^75
        have hw : |(-2706443833/5000000000 : ℝ)|=(2706443833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2013923181/5000000000 : ℝ)|^91 ≤ (16587914393721/50000000000000 : ℝ)^75
        have hw : |(2013923181/5000000000 : ℝ)|=(2013923181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2581612449/10000000000 : ℝ)|^91 ≤ (4834680866621/25000000000000 : ℝ)^75
        have hw : |(2581612449/10000000000 : ℝ)|=(2581612449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3445156607/5000000000 : ℝ)*x 0 + (1255983/10000000000 : ℝ)*x 1 + (43436913/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3445156607/5000000000 : ℝ)^91 ≤ (63639966617359/100000000000000 : ℝ)^75 := by
    have hnat : (3445156607 : ℕ)^91*100000000000000^75 ≤ 63639966617359^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3445156607 5000000000 63639966617359 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255983/10000000000 : ℝ)^91 ≤ (924138297/50000000000000 : ℝ)^75 := by
    have hnat : (1255983 : ℕ)^91*50000000000000^75 ≤ 924138297^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255983 10000000000 924138297 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43436913/100000000 : ℝ)^91 ≤ (36358185097781/100000000000000 : ℝ)^75 := by
    have hnat : (43436913 : ℕ)^91*100000000000000^75 ≤ 36358185097781^75*100000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43436913 100000000 36358185097781 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3445156607/5000000000 : ℝ), (1255983/10000000000 : ℝ), (43436913/100000000 : ℝ)] ![(63639966617359/100000000000000 : ℝ), (924138297/50000000000000 : ℝ), (36358185097781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3445156607/5000000000 : ℝ)|^91 ≤ (63639966617359/100000000000000 : ℝ)^75
        have hw : |(3445156607/5000000000 : ℝ)|=(3445156607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255983/10000000000 : ℝ)|^91 ≤ (924138297/50000000000000 : ℝ)^75
        have hw : |(1255983/10000000000 : ℝ)|=(1255983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43436913/100000000 : ℝ)|^91 ≤ (36358185097781/100000000000000 : ℝ)^75
        have hw : |(43436913/100000000 : ℝ)|=(43436913/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (23604833/312500000 : ℝ)*x 0 + (5664268053/10000000000 : ℝ)*x 1 + (-522304639/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23604833/312500000 : ℝ)^91 ≤ (87066903747/2000000000000 : ℝ)^75 := by
    have hnat : (23604833 : ℕ)^91*2000000000000^75 ≤ 87066903747^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23604833 312500000 87066903747 2000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5664268053/10000000000 : ℝ)^91 ≤ (6271784882807/12500000000000 : ℝ)^75 := by
    have hnat : (5664268053 : ℕ)^91*12500000000000^75 ≤ 6271784882807^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664268053 10000000000 6271784882807 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522304639/1000000000 : ℝ)^91 ≤ (45472375745683/100000000000000 : ℝ)^75 := by
    have hnat : (522304639 : ℕ)^91*100000000000000^75 ≤ 45472375745683^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522304639 1000000000 45472375745683 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(23604833/312500000 : ℝ), (5664268053/10000000000 : ℝ), (-522304639/1000000000 : ℝ)] ![(87066903747/2000000000000 : ℝ), (6271784882807/12500000000000 : ℝ), (45472375745683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(23604833/312500000 : ℝ)|^91 ≤ (87066903747/2000000000000 : ℝ)^75
        have hw : |(23604833/312500000 : ℝ)|=(23604833/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5664268053/10000000000 : ℝ)|^91 ≤ (6271784882807/12500000000000 : ℝ)^75
        have hw : |(5664268053/10000000000 : ℝ)|=(5664268053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522304639/1000000000 : ℝ)|^91 ≤ (45472375745683/100000000000000 : ℝ)^75
        have hw : |(-522304639/1000000000 : ℝ)|=(522304639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1279817601/5000000000 : ℝ)*x 0 + (129442707/250000000 : ℝ)*x 1 + (1073816187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1279817601/5000000000 : ℝ)^91 ≤ (19139153700123/100000000000000 : ℝ)^75 := by
    have hnat : (1279817601 : ℕ)^91*100000000000000^75 ≤ 19139153700123^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279817601 5000000000 19139153700123 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129442707/250000000 : ℝ)^91 ≤ (11248473856549/25000000000000 : ℝ)^75 := by
    have hnat : (129442707 : ℕ)^91*25000000000000^75 ≤ 11248473856549^75*250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129442707 250000000 11248473856549 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073816187/2500000000 : ℝ)^91 ≤ (35866950855169/100000000000000 : ℝ)^75 := by
    have hnat : (1073816187 : ℕ)^91*100000000000000^75 ≤ 35866950855169^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073816187 2500000000 35866950855169 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1279817601/5000000000 : ℝ), (129442707/250000000 : ℝ), (1073816187/2500000000 : ℝ)] ![(19139153700123/100000000000000 : ℝ), (11248473856549/25000000000000 : ℝ), (35866950855169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1279817601/5000000000 : ℝ)|^91 ≤ (19139153700123/100000000000000 : ℝ)^75
        have hw : |(1279817601/5000000000 : ℝ)|=(1279817601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129442707/250000000 : ℝ)|^91 ≤ (11248473856549/25000000000000 : ℝ)^75
        have hw : |(129442707/250000000 : ℝ)|=(129442707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1073816187/2500000000 : ℝ)|^91 ≤ (35866950855169/100000000000000 : ℝ)^75
        have hw : |(1073816187/2500000000 : ℝ)|=(1073816187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2299366557/10000000000 : ℝ)*x 0 + (3134997513/5000000000 : ℝ)*x 1 + (3340634091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2299366557/10000000000 : ℝ)^91 ≤ (16804204654669/100000000000000 : ℝ)^75 := by
    have hnat : (2299366557 : ℕ)^91*100000000000000^75 ≤ 16804204654669^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299366557 10000000000 16804204654669 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3134997513/5000000000 : ℝ)^91 ≤ (5675675164019/10000000000000 : ℝ)^75 := by
    have hnat : (3134997513 : ℕ)^91*10000000000000^75 ≤ 5675675164019^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134997513 5000000000 5675675164019 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3340634091/10000000000 : ℝ)^91 ≤ (6609760924253/25000000000000 : ℝ)^75 := by
    have hnat : (3340634091 : ℕ)^91*25000000000000^75 ≤ 6609760924253^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3340634091 10000000000 6609760924253 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2299366557/10000000000 : ℝ), (3134997513/5000000000 : ℝ), (3340634091/10000000000 : ℝ)] ![(16804204654669/100000000000000 : ℝ), (5675675164019/10000000000000 : ℝ), (6609760924253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2299366557/10000000000 : ℝ)|^91 ≤ (16804204654669/100000000000000 : ℝ)^75
        have hw : |(-2299366557/10000000000 : ℝ)|=(2299366557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3134997513/5000000000 : ℝ)|^91 ≤ (5675675164019/10000000000000 : ℝ)^75
        have hw : |(3134997513/5000000000 : ℝ)|=(3134997513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3340634091/10000000000 : ℝ)|^91 ≤ (6609760924253/25000000000000 : ℝ)^75
        have hw : |(3340634091/10000000000 : ℝ)|=(3340634091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3994210339/5000000000 : ℝ)*x 0 + (-1/2500000000 : ℝ)*x 1 + (153446343/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3994210339/5000000000 : ℝ)^91 ≤ (19036740958557/25000000000000 : ℝ)^75 := by
    have hnat : (3994210339 : ℕ)^91*25000000000000^75 ≤ 19036740958557^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3994210339 5000000000 19036740958557 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1/2500000000 : ℝ)^91 ≤ (99/25000000000000 : ℝ)^75 := by
    have hnat : (1 : ℕ)^91*25000000000000^75 ≤ 99^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 2500000000 99 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153446343/500000000 : ℝ)^91 ≤ (11926518076591/50000000000000 : ℝ)^75 := by
    have hnat : (153446343 : ℕ)^91*50000000000000^75 ≤ 11926518076591^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153446343 500000000 11926518076591 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3994210339/5000000000 : ℝ), (-1/2500000000 : ℝ), (153446343/500000000 : ℝ)] ![(19036740958557/25000000000000 : ℝ), (99/25000000000000 : ℝ), (11926518076591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3994210339/5000000000 : ℝ)|^91 ≤ (19036740958557/25000000000000 : ℝ)^75
        have hw : |(3994210339/5000000000 : ℝ)|=(3994210339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1/2500000000 : ℝ)|^91 ≤ (99/25000000000000 : ℝ)^75
        have hw : |(-1/2500000000 : ℝ)|=(1/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153446343/500000000 : ℝ)|^91 ≤ (11926518076591/50000000000000 : ℝ)^75
        have hw : |(153446343/500000000 : ℝ)|=(153446343/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (295384737/5000000000 : ℝ)*x 0 + (7843192861/10000000000 : ℝ)*x 1 + (-2903122003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (295384737/5000000000 : ℝ)^91 ≤ (1615439015001/50000000000000 : ℝ)^75 := by
    have hnat : (295384737 : ℕ)^91*50000000000000^75 ≤ 1615439015001^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295384737 5000000000 1615439015001 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7843192861/10000000000 : ℝ)^91 ≤ (9308821973527/12500000000000 : ℝ)^75 := by
    have hnat : (7843192861 : ℕ)^91*12500000000000^75 ≤ 9308821973527^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7843192861 10000000000 9308821973527 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2903122003/10000000000 : ℝ)^91 ≤ (4459709233767/20000000000000 : ℝ)^75 := by
    have hnat : (2903122003 : ℕ)^91*20000000000000^75 ≤ 4459709233767^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2903122003 10000000000 4459709233767 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(295384737/5000000000 : ℝ), (7843192861/10000000000 : ℝ), (-2903122003/10000000000 : ℝ)] ![(1615439015001/50000000000000 : ℝ), (9308821973527/12500000000000 : ℝ), (4459709233767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(295384737/5000000000 : ℝ)|^91 ≤ (1615439015001/50000000000000 : ℝ)^75
        have hw : |(295384737/5000000000 : ℝ)|=(295384737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7843192861/10000000000 : ℝ)|^91 ≤ (9308821973527/12500000000000 : ℝ)^75
        have hw : |(7843192861/10000000000 : ℝ)|=(7843192861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2903122003/10000000000 : ℝ)|^91 ≤ (4459709233767/20000000000000 : ℝ)^75
        have hw : |(-2903122003/10000000000 : ℝ)|=(2903122003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s0_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6420634433/10000000000 : ℝ)*x 0 + (389012499/1250000000 : ℝ)*x 1 + (235779883/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6420634433/10000000000 : ℝ)^91 ≤ (58415473967547/100000000000000 : ℝ)^75 := by
    have hnat : (6420634433 : ℕ)^91*100000000000000^75 ≤ 58415473967547^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6420634433 10000000000 58415473967547 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389012499/1250000000 : ℝ)^91 ≤ (6065197866279/25000000000000 : ℝ)^75 := by
    have hnat : (389012499 : ℕ)^91*25000000000000^75 ≤ 6065197866279^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389012499 1250000000 6065197866279 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235779883/1000000000 : ℝ)^91 ≤ (1732373456103/10000000000000 : ℝ)^75 := by
    have hnat : (235779883 : ℕ)^91*10000000000000^75 ≤ 1732373456103^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235779883 1000000000 1732373456103 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6420634433/10000000000 : ℝ), (389012499/1250000000 : ℝ), (235779883/1000000000 : ℝ)] ![(58415473967547/100000000000000 : ℝ), (6065197866279/25000000000000 : ℝ), (1732373456103/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6420634433/10000000000 : ℝ)|^91 ≤ (58415473967547/100000000000000 : ℝ)^75
        have hw : |(6420634433/10000000000 : ℝ)|=(6420634433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(389012499/1250000000 : ℝ)|^91 ≤ (6065197866279/25000000000000 : ℝ)^75
        have hw : |(389012499/1250000000 : ℝ)|=(389012499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235779883/1000000000 : ℝ)|^91 ≤ (1732373456103/10000000000000 : ℝ)^75
        have hw : |(235779883/1000000000 : ℝ)|=(235779883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3328944709/10000000000 : ℝ)*x 0 + (325601587/625000000 : ℝ)*x 1 + (1768817571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3328944709/10000000000 : ℝ)^91 ≤ (13163417536399/50000000000000 : ℝ)^75 := by
    have hnat : (3328944709 : ℕ)^91*50000000000000^75 ≤ 13163417536399^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3328944709 10000000000 13163417536399 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325601587/625000000 : ℝ)^91 ≤ (45330643205469/100000000000000 : ℝ)^75 := by
    have hnat : (325601587 : ℕ)^91*100000000000000^75 ≤ 45330643205469^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325601587 625000000 45330643205469 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768817571/5000000000 : ℝ)^91 ≤ (3542815212691/12500000000000 : ℝ)^75 := by
    have hnat : (1768817571 : ℕ)^91*12500000000000^75 ≤ 3542815212691^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768817571 5000000000 3542815212691 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3328944709/10000000000 : ℝ), (325601587/625000000 : ℝ), (1768817571/5000000000 : ℝ)] ![(13163417536399/50000000000000 : ℝ), (45330643205469/100000000000000 : ℝ), (3542815212691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3328944709/10000000000 : ℝ)|^91 ≤ (13163417536399/50000000000000 : ℝ)^75
        have hw : |(-3328944709/10000000000 : ℝ)|=(3328944709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325601587/625000000 : ℝ)|^91 ≤ (45330643205469/100000000000000 : ℝ)^75
        have hw : |(325601587/625000000 : ℝ)|=(325601587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1768817571/5000000000 : ℝ)|^91 ≤ (3542815212691/12500000000000 : ℝ)^75
        have hw : |(1768817571/5000000000 : ℝ)|=(1768817571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5548590081/10000000000 : ℝ)*x 0 + (-471489089/5000000000 : ℝ)*x 1 + (2606590947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5548590081/10000000000 : ℝ)^91 ≤ (48933724358903/100000000000000 : ℝ)^75 := by
    have hnat : (5548590081 : ℕ)^91*100000000000000^75 ≤ 48933724358903^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548590081 10000000000 48933724358903 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471489089/5000000000 : ℝ)^91 ≤ (5698081539291/100000000000000 : ℝ)^75 := by
    have hnat : (471489089 : ℕ)^91*100000000000000^75 ≤ 5698081539291^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471489089 5000000000 5698081539291 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606590947/5000000000 : ℝ)^91 ≤ (11342048522901/25000000000000 : ℝ)^75 := by
    have hnat : (2606590947 : ℕ)^91*25000000000000^75 ≤ 11342048522901^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606590947 5000000000 11342048522901 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5548590081/10000000000 : ℝ), (-471489089/5000000000 : ℝ), (2606590947/5000000000 : ℝ)] ![(48933724358903/100000000000000 : ℝ), (5698081539291/100000000000000 : ℝ), (11342048522901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5548590081/10000000000 : ℝ)|^91 ≤ (48933724358903/100000000000000 : ℝ)^75
        have hw : |(5548590081/10000000000 : ℝ)|=(5548590081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471489089/5000000000 : ℝ)|^91 ≤ (5698081539291/100000000000000 : ℝ)^75
        have hw : |(-471489089/5000000000 : ℝ)|=(471489089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606590947/5000000000 : ℝ)|^91 ≤ (11342048522901/25000000000000 : ℝ)^75
        have hw : |(2606590947/5000000000 : ℝ)|=(2606590947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1575258469/5000000000 : ℝ)*x 0 + (5542199887/10000000000 : ℝ)*x 1 + (-1674010897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1575258469/5000000000 : ℝ)^91 ≤ (12312321421569/50000000000000 : ℝ)^75 := by
    have hnat : (1575258469 : ℕ)^91*50000000000000^75 ≤ 12312321421569^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1575258469 5000000000 12312321421569 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5542199887/10000000000 : ℝ)^91 ≤ (48865354224833/100000000000000 : ℝ)^75 := by
    have hnat : (5542199887 : ℕ)^91*100000000000000^75 ≤ 48865354224833^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5542199887 10000000000 48865354224833 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674010897/5000000000 : ℝ)^91 ≤ (26510002905851/100000000000000 : ℝ)^75 := by
    have hnat : (1674010897 : ℕ)^91*100000000000000^75 ≤ 26510002905851^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674010897 5000000000 26510002905851 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1575258469/5000000000 : ℝ), (5542199887/10000000000 : ℝ), (-1674010897/5000000000 : ℝ)] ![(12312321421569/50000000000000 : ℝ), (48865354224833/100000000000000 : ℝ), (26510002905851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1575258469/5000000000 : ℝ)|^91 ≤ (12312321421569/50000000000000 : ℝ)^75
        have hw : |(1575258469/5000000000 : ℝ)|=(1575258469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5542199887/10000000000 : ℝ)|^91 ≤ (48865354224833/100000000000000 : ℝ)^75
        have hw : |(5542199887/10000000000 : ℝ)|=(5542199887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1674010897/5000000000 : ℝ)|^91 ≤ (26510002905851/100000000000000 : ℝ)^75
        have hw : |(-1674010897/5000000000 : ℝ)|=(1674010897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327023_s1_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (938702553/2500000000 : ℝ)*x 0 + (4823355309/10000000000 : ℝ)*x 1 + (3527834697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (938702553/2500000000 : ℝ)^91 ≤ (7616815518207/25000000000000 : ℝ)^75 := by
    have hnat : (938702553 : ℕ)^91*25000000000000^75 ≤ 7616815518207^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938702553 2500000000 7616815518207 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4823355309/10000000000 : ℝ)^91 ≤ (41285456989947/100000000000000 : ℝ)^75 := by
    have hnat : (4823355309 : ℕ)^91*100000000000000^75 ≤ 41285456989947^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823355309 10000000000 41285456989947 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3527834697/10000000000 : ℝ)^91 ≤ (5649456185093/20000000000000 : ℝ)^75 := by
    have hnat : (3527834697 : ℕ)^91*20000000000000^75 ≤ 5649456185093^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3527834697 10000000000 5649456185093 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(938702553/2500000000 : ℝ), (4823355309/10000000000 : ℝ), (3527834697/10000000000 : ℝ)] ![(7616815518207/25000000000000 : ℝ), (41285456989947/100000000000000 : ℝ), (5649456185093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(938702553/2500000000 : ℝ)|^91 ≤ (7616815518207/25000000000000 : ℝ)^75
        have hw : |(938702553/2500000000 : ℝ)|=(938702553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4823355309/10000000000 : ℝ)|^91 ≤ (41285456989947/100000000000000 : ℝ)^75
        have hw : |(4823355309/10000000000 : ℝ)|=(4823355309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3527834697/10000000000 : ℝ)|^91 ≤ (5649456185093/20000000000000 : ℝ)^75
        have hw : |(3527834697/10000000000 : ℝ)|=(3527834697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327023 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (32523/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-24933611/80000000 : ℝ)*X 0 0+(542968411/1000000000 : ℝ)*X 0 1+(350559733/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((926531/1562500 : ℝ)*X 1 0+(13/1000000000 : ℝ)*X 1 1+(1340816149/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((108997357/400000000 : ℝ)*X 2 0+(6158592637/10000000000 : ℝ)*X 2 1+(-383118237/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3463736311/10000000000 : ℝ)*X 0 0+(2287671443/10000000000 : ℝ)*X 0 1+(3085608207/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2411034061/5000000000 : ℝ)*X 1 0+(1721/400000000 : ℝ)*X 1 1+(3224460667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1047562019/10000000000 : ℝ)*X 2 0+(8296924413/10000000000 : ℝ)*X 2 1+(-1954450139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1107345191/5000000000 : ℝ)*X 0 0+(6660772287/10000000000 : ℝ)*X 0 1+(2963965043/10000000000 : ℝ)*X 0 2+(1107345191/5000000000 : ℝ)*X 1 0+(6660772287/10000000000 : ℝ)*X 1 1+(2963965043/10000000000 : ℝ)*X 1 2+(1107345191/5000000000 : ℝ)*X 2 0+(6660772287/10000000000 : ℝ)*X 2 1+(2963965043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2706443833/5000000000 : ℝ)*X 0 0+(2013923181/5000000000 : ℝ)*X 0 1+(2581612449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3445156607/5000000000 : ℝ)*X 1 0+(1255983/10000000000 : ℝ)*X 1 1+(43436913/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((23604833/312500000 : ℝ)*X 2 0+(5664268053/10000000000 : ℝ)*X 2 1+(-522304639/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1279817601/5000000000 : ℝ)*X 0 0+(129442707/250000000 : ℝ)*X 0 1+(1073816187/2500000000 : ℝ)*X 0 2+(1279817601/5000000000 : ℝ)*X 1 0+(129442707/250000000 : ℝ)*X 1 1+(1073816187/2500000000 : ℝ)*X 1 2+(1279817601/5000000000 : ℝ)*X 2 0+(129442707/250000000 : ℝ)*X 2 1+(1073816187/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-2299366557/10000000000 : ℝ)*X 0 0+(3134997513/5000000000 : ℝ)*X 0 1+(3340634091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3994210339/5000000000 : ℝ)*X 1 0+(-1/2500000000 : ℝ)*X 1 1+(153446343/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((295384737/5000000000 : ℝ)*X 2 0+(7843192861/10000000000 : ℝ)*X 2 1+(-2903122003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6420634433/10000000000 : ℝ)*X 0 0+(389012499/1250000000 : ℝ)*X 0 1+(235779883/1000000000 : ℝ)*X 0 2+(6420634433/10000000000 : ℝ)*X 1 0+(389012499/1250000000 : ℝ)*X 1 1+(235779883/1000000000 : ℝ)*X 1 2+(6420634433/10000000000 : ℝ)*X 2 0+(389012499/1250000000 : ℝ)*X 2 1+(235779883/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((27907/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27907/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23305785306844058154201/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216555072421/1000000000000 : ℝ)*(base7) + (1043599/125000000000 : ℝ)*(base49) + (229639768523/1000000000000 : ℝ)*(base50) + (879239/125000000000 : ℝ)*(base53) + (15795851407/500000000000 : ℝ)*(base60) + (819851235167/500000000000 : ℝ)*(major_s0_0) + (819851235167/500000000000 : ℝ)*(major_s0_1) + (819847718211/500000000000 : ℝ)*(major_s0_2) + (14760465003/8000000000 : ℝ)*(sp_s0_7) + (115318227919/62500000000 : ℝ)*(sp_s0_8) + (1845060769021/1000000000000 : ℝ)*(sp_s0_9) + (398284288117/200000000000 : ℝ)*(sp_s0_13) + (33521329/1000000000000 : ℝ)*(sp_s0_21) + (7582319/200000000000 : ℝ)*(sp_s0_23) + (774866368163/1000000000000 : ℝ)*(f.failure) + (230637335077/125000000000 : ℝ)*(f.sum) + (102942659470843/312500000000000000000000000 : ℝ)*base63 + (1350798847284217/2500000000000000000000000000 : ℝ)*base64 + (856709427092051/2500000000000000000000000000 : ℝ)*base66 + (722211291084807/1250000000000000000000000000 : ℝ)*base68 + (13068589758823/100000000000000000000000000 : ℝ)*base70 + (793854481657949/2500000000000000000000000000 : ℝ)*base72 + (106035220843179/1250000000000000000000000000 : ℝ)*base75 + (715937566093179/1250000000000000000000000000 : ℝ)*base76 + (2487801451/10000000000000000000000 : ℝ)*base78 + (59407/100000000000000000 : ℝ)*base86 + (59407/100000000000000000 : ℝ)*base88 + (59407/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(481/2000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(481/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13379159594268110927973/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40242541/1000000000000 : ℝ)*(base3) + (44405035839/100000000000 : ℝ)*(base7) + (294389064751/1000000000000 : ℝ)*(base40) + (52735220303/125000000000 : ℝ)*(base49) + (924405041/50000000000 : ℝ)*(base60) + (1736200519147/1000000000000 : ℝ)*(major_s0_0) + (1736200519147/1000000000000 : ℝ)*(major_s0_1) + (1736200519147/1000000000000 : ℝ)*(major_s0_2) + (2699197/1000000000000 : ℝ)*(sp_s0_0) + (36511977/500000000000 : ℝ)*(sp_s0_1) + (602807321039/250000000000 : ℝ)*(sp_s0_14) + (2411199201939/1000000000000 : ℝ)*(sp_s0_15) + (2411231983353/1000000000000 : ℝ)*(sp_s0_16) + (1264478106241/1000000000000 : ℝ)*(sp_s0_20) + (820467990391/1000000000000 : ℝ)*(f.failure) + (2411231983353/1000000000000 : ℝ)*(f.sum) + (4263420089/10000000000000000000000 : ℝ)*base63 + (4539195863149009/5000000000000000000000000000 : ℝ)*base64 + (306510891149009/5000000000000000000000000000 : ℝ)*base67 + (935161468294561/2500000000000000000000000000 : ℝ)*base69 + (2256909770059887/5000000000000000000000000000 : ℝ)*base70 + (2477585828149009/5000000000000000000000000000 : ℝ)*base72 + (799918587794561/2500000000000000000000000000 : ℝ)*base74 + (583490021955439/2500000000000000000000000000 : ℝ)*base76 + (169673299/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (70099/100000000000000000 : ℝ)*base86 + (70099/100000000000000000 : ℝ)*base88 + (70099/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12173/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12173/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1266849464563095574629/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (768619/1000000000000 : ℝ)*(base3) + (251594158073/200000000000 : ℝ)*(base7) + (320627/100000000000 : ℝ)*(base11) + (257075243989/1000000000000 : ℝ)*(base40) + (62816283373/500000000000 : ℝ)*(base50) + (188550165869/100000000000 : ℝ)*(major_s0_0) + (188550165869/100000000000 : ℝ)*(major_s0_1) + (188550165869/100000000000 : ℝ)*(major_s0_2) + (1786073/250000000000 : ℝ)*(sp_s0_2) + (12268731/500000000000 : ℝ)*(sp_s0_9) + (439618567413/200000000000 : ℝ)*(sp_s0_21) + (1099048405977/500000000000 : ℝ)*(sp_s0_22) + (2198064361581/1000000000000 : ℝ)*(sp_s0_23) + (107449626943/50000000000 : ℝ)*(sp_s0_27) + (445511258557/500000000000 : ℝ)*(f.failure) + (439619208667/200000000000 : ℝ)*(f.sum) + (156178753/400000000000000000000 : ℝ)*base63 + (24873964308457/500000000000000000000000000 : ℝ)*base65 + (181326190558457/500000000000000000000000000 : ℝ)*base66 + (56273721743847/250000000000000000000000000 : ℝ)*base69 + (439636593292696151/500000000000000000000000000 : ℝ)*base71 + (14780557191543/500000000000000000000000000 : ℝ)*base72 + (77419832156153/250000000000000000000000000 : ℝ)*base75 + (10687502731153/250000000000000000000000000 : ℝ)*base76 + (2426734207/10000000000000000000000 : ℝ)*base78 + (5327/50000000000000000 : ℝ)*base87 + (5327/50000000000000000 : ℝ)*base89 + (5327/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (27907/50000 : ℝ) ^ (89/16 : ℝ) ≤ (1950871954154513147/50000000000000000000 : ℝ) := by
    have hpowers : (27907/50000 : ℝ)^89 ≤ (1950871954154513147/50000000000000000000 : ℝ)^16 := by
      have hnat : (27907 : ℕ)^89*50000000000000000000^16 ≤ 1950871954154513147^16*50000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27907 50000 1950871954154513147 50000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27907/50000 : ℝ)) (X := (1950871954154513147/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (51950871954154513147/50000000000000000000 : ℝ) ≤ (5034523582604649/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (51950871954154513147/50000000000000000000 : ℝ)^16 ≤ (5034523582604649/5000000000000000 : ℝ)^89 := by
      have hnat : (51950871954154513147 : ℕ)^16*5000000000000000^89 ≤ 5034523582604649^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51950871954154513147 50000000000000000000 5034523582604649 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5034523582604649/5000000000000000 : ℝ)) (X := (51950871954154513147/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (26950871954154513147/25000000000000000000 : ℝ) ≤ (10135999324809557/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (26950871954154513147/25000000000000000000 : ℝ)^16 ≤ (10135999324809557/10000000000000000 : ℝ)^89 := by
      have hnat : (26950871954154513147 : ℕ)^16*10000000000000000^89 ≤ 10135999324809557^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26950871954154513147 25000000000000000000 10135999324809557 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10135999324809557/10000000000000000 : ℝ)) (X := (26950871954154513147/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(34523582604649/2790700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(66952159600259/5581400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (27907/50000 : ℝ)) (alpha := (34523582604649/2790700000000000 : ℝ)) (beta := (66952159600259/5581400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (27907/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(34523582604649/2790700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(66952159600259/5581400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (481/2000 : ℝ) ^ (89/16 : ℝ) ≤ (36095464622868029/100000000000000000000 : ℝ) := by
    have hpowers : (481/2000 : ℝ)^89 ≤ (36095464622868029/100000000000000000000 : ℝ)^16 := by
      have hnat : (481 : ℕ)^89*100000000000000000000^16 ≤ 36095464622868029^16*2000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        481 2000 36095464622868029 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (481/2000 : ℝ)) (X := (36095464622868029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100036095464622868029/100000000000000000000 : ℝ) ≤ (5000324405595599/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (100036095464622868029/100000000000000000000 : ℝ)^16 ≤ (5000324405595599/5000000000000000 : ℝ)^89 := by
      have hnat : (100036095464622868029 : ℕ)^16*5000000000000000^89 ≤ 5000324405595599^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036095464622868029 100000000000000000000 5000324405595599 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000324405595599/5000000000000000 : ℝ)) (X := (100036095464622868029/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50036095464622868029/50000000000000000000 : ℝ) ≤ (400051897215621/400000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (50036095464622868029/50000000000000000000 : ℝ)^16 ≤ (400051897215621/400000000000000 : ℝ)^89 := by
      have hnat : (50036095464622868029 : ℕ)^16*400000000000000^89 ≤ 400051897215621^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036095464622868029 50000000000000000000 400051897215621 400000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400051897215621/400000000000000 : ℝ)) (X := (50036095464622868029/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(324405595599/1202500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(648619199327/2405000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (481/2000 : ℝ)) (alpha := (324405595599/1202500000000000 : ℝ)) (beta := (648619199327/2405000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (481/2000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(324405595599/1202500000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(648619199327/2405000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (12173/20000 : ℝ) ^ (89/16 : ℝ) ≤ (1579373803531570697/25000000000000000000 : ℝ) := by
    have hpowers : (12173/20000 : ℝ)^89 ≤ (1579373803531570697/25000000000000000000 : ℝ)^16 := by
      have hnat : (12173 : ℕ)^89*25000000000000000000^16 ≤ 1579373803531570697^16*20000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12173 20000 1579373803531570697 25000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12173/20000 : ℝ)) (X := (1579373803531570697/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (26579373803531570697/25000000000000000000 : ℝ) ≤ (10110738402734261/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (26579373803531570697/25000000000000000000 : ℝ)^16 ≤ (10110738402734261/10000000000000000 : ℝ)^89 := by
      have hnat : (26579373803531570697 : ℕ)^16*10000000000000000^89 ≤ 10110738402734261^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26579373803531570697 25000000000000000000 10110738402734261 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10110738402734261/10000000000000000 : ℝ)) (X := (26579373803531570697/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (14079373803531570697/12500000000000000000 : ℝ) ≤ (5108102356708131/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (14079373803531570697/12500000000000000000 : ℝ)^16 ≤ (5108102356708131/5000000000000000 : ℝ)^89 := by
      have hnat : (14079373803531570697 : ℕ)^16*5000000000000000^89 ≤ 5108102356708131^89*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14079373803531570697 12500000000000000000 5108102356708131 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5108102356708131/5000000000000000 : ℝ)) (X := (14079373803531570697/12500000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(110738402734261/6086500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(105466310682001/6086500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (12173/20000 : ℝ)) (alpha := (110738402734261/6086500000000000 : ℝ)) (beta := (105466310682001/6086500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (12173/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(110738402734261/6086500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(105466310682001/6086500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3328944709/10000000000 : ℝ)*X 0 0+(325601587/625000000 : ℝ)*X 0 1+(1768817571/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5548590081/10000000000 : ℝ)*X 1 0+(-471489089/5000000000 : ℝ)*X 1 1+(2606590947/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1575258469/5000000000 : ℝ)*X 2 0+(5542199887/10000000000 : ℝ)*X 2 1+(-1674010897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((938702553/2500000000 : ℝ)*X 0 0+(4823355309/10000000000 : ℝ)*X 0 1+(3527834697/10000000000 : ℝ)*X 0 2+(938702553/2500000000 : ℝ)*X 1 0+(4823355309/10000000000 : ℝ)*X 1 1+(3527834697/10000000000 : ℝ)*X 1 2+(938702553/2500000000 : ℝ)*X 2 0+(4823355309/10000000000 : ℝ)*X 2 1+(3527834697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327023_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-53101936156297973350096349760201/5520318553750000000000000000000 : ℝ) := by norm_num
    linear_combination (15487/1000000000000 : ℝ)*(base7) + (15799/1000000000000 : ℝ)*(base11) + (7993/1000000000000 : ℝ)*(base15) + (6531/200000000000 : ℝ)*(base24) + (23425586413/200000000000 : ℝ)*(base40) + (3395722523/2500000000 : ℝ)*(base49) + (729859467649/1000000000000 : ℝ)*(base50) + (2871/125000000000 : ℝ)*(ratio_s0_2) + (211611/100000 : ℝ)*(major_s1_0) + (211611/100000 : ℝ)*(major_s1_1) + (211611/100000 : ℝ)*(major_s1_2) + (320645359131/100000000000 : ℝ)*(sp_s1_0) + (3206453599117/1000000000000 : ℝ)*(sp_s1_1) + (641290714891/200000000000 : ℝ)*(sp_s1_2) + (1000000015487/1000000000000 : ℝ)*(sp_s1_6) + (3206453607109/1000000000000 : ℝ)*(f.sum) + (563086670055523/791245000000000000000000000 : ℝ)*base62 + (36327807141481/121730000000000000000000000 : ℝ)*base65 + (1684309431221/4810000000000000000000000 : ℝ)*base67 + (93445086379733/121730000000000000000000000 : ℝ)*base68 + (198602627301163473/3397119110000000000000000000000 : ℝ)*base71 + (21328118287441/279070000000000000000000000 : ℝ)*base73 + (990102754177/2405000000000000000000000 : ℝ)*base74 + (14009609624169/69767500000000000000000000 : ℝ)*base76 + (42419779785627877/134232670000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p027_b009 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 24)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=22 ∨ c=23 := by omega
  rcases hc with rfl|rfl
  · exact collision_c327022 p hpa (by linarith only [hpb]) X hX
  · exact collision_c327023 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 24)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b009 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

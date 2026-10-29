-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b009
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:14.007281+00:00
-- url     : https://prove2.me/submissions/f7fede02-a70b-466a-8d6a-3832278d2040

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
theorem collision_support_c322021_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920337987/5000000000 : ℝ)*x 0 + (3706017833/10000000000 : ℝ)*x 1 + (1190582241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920337987/5000000000 : ℝ)^21 ≤ (30663465617101/100000000000000 : ℝ)^17 := by
    have hnat : (1920337987 : ℕ)^21*100000000000000^17 ≤ 30663465617101^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920337987 5000000000 30663465617101 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3706017833/10000000000 : ℝ)^21 ≤ (29340936837899/100000000000000 : ℝ)^17 := by
    have hnat : (3706017833 : ℕ)^21*100000000000000^17 ≤ 29340936837899^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3706017833 10000000000 29340936837899 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190582241/2500000000 : ℝ)^21 ≤ (39995597537499/100000000000000 : ℝ)^17 := by
    have hnat : (1190582241 : ℕ)^21*100000000000000^17 ≤ 39995597537499^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190582241 2500000000 39995597537499 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920337987/5000000000 : ℝ), (3706017833/10000000000 : ℝ), (1190582241/2500000000 : ℝ)] ![(30663465617101/100000000000000 : ℝ), (29340936837899/100000000000000 : ℝ), (39995597537499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920337987/5000000000 : ℝ)|^21 ≤ (30663465617101/100000000000000 : ℝ)^17
        have hw : |(-1920337987/5000000000 : ℝ)|=(1920337987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3706017833/10000000000 : ℝ)|^21 ≤ (29340936837899/100000000000000 : ℝ)^17
        have hw : |(3706017833/10000000000 : ℝ)|=(3706017833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1190582241/2500000000 : ℝ)|^21 ≤ (39995597537499/100000000000000 : ℝ)^17
        have hw : |(1190582241/2500000000 : ℝ)|=(1190582241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5968088791/10000000000 : ℝ)*x 0 + (-988416829/10000000000 : ℝ)*x 1 + (979651469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5968088791/10000000000 : ℝ)^21 ≤ (13213888670171/25000000000000 : ℝ)^17 := by
    have hnat : (5968088791 : ℕ)^21*25000000000000^17 ≤ 13213888670171^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5968088791 10000000000 13213888670171 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (988416829/10000000000 : ℝ)^21 ≤ (1146794105023/20000000000000 : ℝ)^17 := by
    have hnat : (988416829 : ℕ)^21*20000000000000^17 ≤ 1146794105023^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988416829 10000000000 1146794105023 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979651469/2000000000 : ℝ)^21 ≤ (41410474775883/100000000000000 : ℝ)^17 := by
    have hnat : (979651469 : ℕ)^21*100000000000000^17 ≤ 41410474775883^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979651469 2000000000 41410474775883 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5968088791/10000000000 : ℝ), (-988416829/10000000000 : ℝ), (979651469/2000000000 : ℝ)] ![(13213888670171/25000000000000 : ℝ), (1146794105023/20000000000000 : ℝ), (41410474775883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5968088791/10000000000 : ℝ)|^21 ≤ (13213888670171/25000000000000 : ℝ)^17
        have hw : |(5968088791/10000000000 : ℝ)|=(5968088791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-988416829/10000000000 : ℝ)|^21 ≤ (1146794105023/20000000000000 : ℝ)^17
        have hw : |(-988416829/10000000000 : ℝ)|=(988416829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(979651469/2000000000 : ℝ)|^21 ≤ (41410474775883/100000000000000 : ℝ)^17
        have hw : |(979651469/2000000000 : ℝ)|=(979651469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1890108097/10000000000 : ℝ)*x 0 + (7541414893/10000000000 : ℝ)*x 1 + (-1171840139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1890108097/10000000000 : ℝ)^21 ≤ (2554337040881/20000000000000 : ℝ)^17 := by
    have hnat : (1890108097 : ℕ)^21*20000000000000^17 ≤ 2554337040881^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890108097 10000000000 2554337040881 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7541414893/10000000000 : ℝ)^21 ≤ (35284844787549/50000000000000 : ℝ)^17 := by
    have hnat : (7541414893 : ℕ)^21*50000000000000^17 ≤ 35284844787549^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7541414893 10000000000 35284844787549 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171840139/5000000000 : ℝ)^21 ≤ (16658625206321/100000000000000 : ℝ)^17 := by
    have hnat : (1171840139 : ℕ)^21*100000000000000^17 ≤ 16658625206321^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171840139 5000000000 16658625206321 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1890108097/10000000000 : ℝ), (7541414893/10000000000 : ℝ), (-1171840139/5000000000 : ℝ)] ![(2554337040881/20000000000000 : ℝ), (35284844787549/50000000000000 : ℝ), (16658625206321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1890108097/10000000000 : ℝ)|^21 ≤ (2554337040881/20000000000000 : ℝ)^17
        have hw : |(1890108097/10000000000 : ℝ)|=(1890108097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7541414893/10000000000 : ℝ)|^21 ≤ (35284844787549/50000000000000 : ℝ)^17
        have hw : |(7541414893/10000000000 : ℝ)|=(7541414893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1171840139/5000000000 : ℝ)|^21 ≤ (16658625206321/100000000000000 : ℝ)^17
        have hw : |(-1171840139/5000000000 : ℝ)|=(1171840139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083868263/5000000000 : ℝ)*x 0 + (307577979/1000000000 : ℝ)*x 1 + (1005663319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083868263/5000000000 : ℝ)^21 ≤ (8480179224483/25000000000000 : ℝ)^17 := by
    have hnat : (2083868263 : ℕ)^21*25000000000000^17 ≤ 8480179224483^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083868263 5000000000 8480179224483 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307577979/1000000000 : ℝ)^21 ≤ (23306342198731/100000000000000 : ℝ)^17 := by
    have hnat : (307577979 : ℕ)^21*100000000000000^17 ≤ 23306342198731^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307577979 1000000000 23306342198731 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005663319/2000000000 : ℝ)^21 ≤ (8554588177499/20000000000000 : ℝ)^17 := by
    have hnat : (1005663319 : ℕ)^21*20000000000000^17 ≤ 8554588177499^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005663319 2000000000 8554588177499 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083868263/5000000000 : ℝ), (307577979/1000000000 : ℝ), (1005663319/2000000000 : ℝ)] ![(8480179224483/25000000000000 : ℝ), (23306342198731/100000000000000 : ℝ), (8554588177499/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083868263/5000000000 : ℝ)|^21 ≤ (8480179224483/25000000000000 : ℝ)^17
        have hw : |(-2083868263/5000000000 : ℝ)|=(2083868263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307577979/1000000000 : ℝ)|^21 ≤ (23306342198731/100000000000000 : ℝ)^17
        have hw : |(307577979/1000000000 : ℝ)|=(307577979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005663319/2000000000 : ℝ)|^21 ≤ (8554588177499/20000000000000 : ℝ)^17
        have hw : |(1005663319/2000000000 : ℝ)|=(1005663319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2801838779/5000000000 : ℝ)*x 0 + (-22921747/625000000 : ℝ)*x 1 + (1130360593/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2801838779/5000000000 : ℝ)^21 ≤ (48897915574127/100000000000000 : ℝ)^17 := by
    have hnat : (2801838779 : ℕ)^21*100000000000000^17 ≤ 48897915574127^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801838779 5000000000 48897915574127 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22921747/625000000 : ℝ)^21 ≤ (1684891197601/100000000000000 : ℝ)^17 := by
    have hnat : (22921747 : ℕ)^21*100000000000000^17 ≤ 1684891197601^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22921747 625000000 1684891197601 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130360593/2000000000 : ℝ)^21 ≤ (49417193211413/100000000000000 : ℝ)^17 := by
    have hnat : (1130360593 : ℕ)^21*100000000000000^17 ≤ 49417193211413^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130360593 2000000000 49417193211413 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2801838779/5000000000 : ℝ), (-22921747/625000000 : ℝ), (1130360593/2000000000 : ℝ)] ![(48897915574127/100000000000000 : ℝ), (1684891197601/100000000000000 : ℝ), (49417193211413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2801838779/5000000000 : ℝ)|^21 ≤ (48897915574127/100000000000000 : ℝ)^17
        have hw : |(2801838779/5000000000 : ℝ)|=(2801838779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-22921747/625000000 : ℝ)|^21 ≤ (1684891197601/100000000000000 : ℝ)^17
        have hw : |(-22921747/625000000 : ℝ)|=(22921747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130360593/2000000000 : ℝ)|^21 ≤ (49417193211413/100000000000000 : ℝ)^17
        have hw : |(1130360593/2000000000 : ℝ)|=(1130360593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (51770349/500000000 : ℝ)*x 0 + (8873142199/10000000000 : ℝ)*x 1 + (-124920423/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51770349/500000000 : ℝ)^21 ≤ (1518142469247/25000000000000 : ℝ)^17 := by
    have hnat : (51770349 : ℕ)^21*25000000000000^17 ≤ 1518142469247^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51770349 500000000 1518142469247 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8873142199/10000000000 : ℝ)^21 ≤ (21567528349043/25000000000000 : ℝ)^17 := by
    have hnat : (8873142199 : ℕ)^21*25000000000000^17 ≤ 21567528349043^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8873142199 10000000000 21567528349043 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124920423/1000000000 : ℝ)^21 ≤ (7657316707749/100000000000000 : ℝ)^17 := by
    have hnat : (124920423 : ℕ)^21*100000000000000^17 ≤ 7657316707749^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124920423 1000000000 7657316707749 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51770349/500000000 : ℝ), (8873142199/10000000000 : ℝ), (-124920423/1000000000 : ℝ)] ![(1518142469247/25000000000000 : ℝ), (21567528349043/25000000000000 : ℝ), (7657316707749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51770349/500000000 : ℝ)|^21 ≤ (1518142469247/25000000000000 : ℝ)^17
        have hw : |(51770349/500000000 : ℝ)|=(51770349/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8873142199/10000000000 : ℝ)|^21 ≤ (21567528349043/25000000000000 : ℝ)^17
        have hw : |(8873142199/10000000000 : ℝ)|=(8873142199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124920423/1000000000 : ℝ)|^21 ≤ (7657316707749/100000000000000 : ℝ)^17
        have hw : |(-124920423/1000000000 : ℝ)|=(124920423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_12 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4444350909/10000000000 : ℝ)*x 0 + (3377647101/10000000000 : ℝ)*x 1 + (4482519807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4444350909/10000000000 : ℝ)^21 ≤ (18361566114139/50000000000000 : ℝ)^17 := by
    have hnat : (4444350909 : ℕ)^21*50000000000000^17 ≤ 18361566114139^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444350909 10000000000 18361566114139 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3377647101/10000000000 : ℝ)^21 ≤ (26163749554523/100000000000000 : ℝ)^17 := by
    have hnat : (3377647101 : ℕ)^21*100000000000000^17 ≤ 26163749554523^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3377647101 10000000000 26163749554523 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482519807/10000000000 : ℝ)^21 ≤ (9278279551469/25000000000000 : ℝ)^17 := by
    have hnat : (4482519807 : ℕ)^21*25000000000000^17 ≤ 9278279551469^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482519807 10000000000 9278279551469 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4444350909/10000000000 : ℝ), (3377647101/10000000000 : ℝ), (4482519807/10000000000 : ℝ)] ![(18361566114139/50000000000000 : ℝ), (26163749554523/100000000000000 : ℝ), (9278279551469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4444350909/10000000000 : ℝ)|^21 ≤ (18361566114139/50000000000000 : ℝ)^17
        have hw : |(4444350909/10000000000 : ℝ)|=(4444350909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3377647101/10000000000 : ℝ)|^21 ≤ (26163749554523/100000000000000 : ℝ)^17
        have hw : |(3377647101/10000000000 : ℝ)|=(3377647101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482519807/10000000000 : ℝ)|^21 ≤ (9278279551469/25000000000000 : ℝ)^17
        have hw : |(4482519807/10000000000 : ℝ)|=(4482519807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153620917/5000000000 : ℝ)*x 0 + (859947753/2500000000 : ℝ)*x 1 + (912085657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153620917/5000000000 : ℝ)^21 ≤ (1104024000731/3125000000000 : ℝ)^17 := by
    have hnat : (2153620917 : ℕ)^21*3125000000000^17 ≤ 1104024000731^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153620917 5000000000 1104024000731 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859947753/2500000000 : ℝ)^21 ≤ (26759671438017/100000000000000 : ℝ)^17 := by
    have hnat : (859947753 : ℕ)^21*100000000000000^17 ≤ 26759671438017^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859947753 2500000000 26759671438017 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912085657/2000000000 : ℝ)^21 ≤ (118473626647/312500000000 : ℝ)^17 := by
    have hnat : (912085657 : ℕ)^21*312500000000^17 ≤ 118473626647^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912085657 2000000000 118473626647 312500000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153620917/5000000000 : ℝ), (859947753/2500000000 : ℝ), (912085657/2000000000 : ℝ)] ![(1104024000731/3125000000000 : ℝ), (26759671438017/100000000000000 : ℝ), (118473626647/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153620917/5000000000 : ℝ)|^21 ≤ (1104024000731/3125000000000 : ℝ)^17
        have hw : |(-2153620917/5000000000 : ℝ)|=(2153620917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(859947753/2500000000 : ℝ)|^21 ≤ (26759671438017/100000000000000 : ℝ)^17
        have hw : |(859947753/2500000000 : ℝ)|=(859947753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(912085657/2000000000 : ℝ)|^21 ≤ (118473626647/312500000000 : ℝ)^17
        have hw : |(912085657/2000000000 : ℝ)|=(912085657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3115372231/5000000000 : ℝ)*x 0 + (-976820659/10000000000 : ℝ)*x 1 + (4627860639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3115372231/5000000000 : ℝ)^21 ≤ (55743777645331/100000000000000 : ℝ)^17 := by
    have hnat : (3115372231 : ℕ)^21*100000000000000^17 ≤ 55743777645331^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115372231 5000000000 55743777645331 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976820659/10000000000 : ℝ)^21 ≤ (176593303493/3125000000000 : ℝ)^17 := by
    have hnat : (976820659 : ℕ)^21*3125000000000^17 ≤ 176593303493^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976820659 10000000000 176593303493 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4627860639/10000000000 : ℝ)^21 ≤ (3860523662971/10000000000000 : ℝ)^17 := by
    have hnat : (4627860639 : ℕ)^21*10000000000000^17 ≤ 3860523662971^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4627860639 10000000000 3860523662971 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3115372231/5000000000 : ℝ), (-976820659/10000000000 : ℝ), (4627860639/10000000000 : ℝ)] ![(55743777645331/100000000000000 : ℝ), (176593303493/3125000000000 : ℝ), (3860523662971/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3115372231/5000000000 : ℝ)|^21 ≤ (55743777645331/100000000000000 : ℝ)^17
        have hw : |(3115372231/5000000000 : ℝ)|=(3115372231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976820659/10000000000 : ℝ)|^21 ≤ (176593303493/3125000000000 : ℝ)^17
        have hw : |(-976820659/10000000000 : ℝ)|=(976820659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4627860639/10000000000 : ℝ)|^21 ≤ (3860523662971/10000000000000 : ℝ)^17
        have hw : |(4627860639/10000000000 : ℝ)|=(4627860639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1463826729/10000000000 : ℝ)*x 0 + (7520690503/10000000000 : ℝ)*x 1 + (-689139669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1463826729/10000000000 : ℝ)^21 ≤ (2328489643123/25000000000000 : ℝ)^17 := by
    have hnat : (1463826729 : ℕ)^21*25000000000000^17 ≤ 2328489643123^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463826729 10000000000 2328489643123 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7520690503/10000000000 : ℝ)^21 ≤ (3516510265819/5000000000000 : ℝ)^17 := by
    have hnat : (7520690503 : ℕ)^21*5000000000000^17 ≤ 3516510265819^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7520690503 10000000000 3516510265819 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689139669/2500000000 : ℝ)^21 ≤ (20355836087569/100000000000000 : ℝ)^17 := by
    have hnat : (689139669 : ℕ)^21*100000000000000^17 ≤ 20355836087569^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689139669 2500000000 20355836087569 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1463826729/10000000000 : ℝ), (7520690503/10000000000 : ℝ), (-689139669/2500000000 : ℝ)] ![(2328489643123/25000000000000 : ℝ), (3516510265819/5000000000000 : ℝ), (20355836087569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1463826729/10000000000 : ℝ)|^21 ≤ (2328489643123/25000000000000 : ℝ)^17
        have hw : |(1463826729/10000000000 : ℝ)|=(1463826729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7520690503/10000000000 : ℝ)|^21 ≤ (3516510265819/5000000000000 : ℝ)^17
        have hw : |(7520690503/10000000000 : ℝ)|=(7520690503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-689139669/2500000000 : ℝ)|^21 ≤ (20355836087569/100000000000000 : ℝ)^17
        have hw : |(-689139669/2500000000 : ℝ)|=(689139669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_19 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4275211861/10000000000 : ℝ)*x 0 + (900729143/2500000000 : ℝ)*x 1 + (2219060007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275211861/10000000000 : ℝ)^21 ≤ (8751130371593/25000000000000 : ℝ)^17 := by
    have hnat : (4275211861 : ℕ)^21*25000000000000^17 ≤ 8751130371593^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275211861 10000000000 8751130371593 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900729143/2500000000 : ℝ)^21 ≤ (14167967525791/50000000000000 : ℝ)^17 := by
    have hnat : (900729143 : ℕ)^21*50000000000000^17 ≤ 14167967525791^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900729143 2500000000 14167967525791 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219060007/5000000000 : ℝ)^21 ≤ (7331908688943/20000000000000 : ℝ)^17 := by
    have hnat : (2219060007 : ℕ)^21*20000000000000^17 ≤ 7331908688943^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219060007 5000000000 7331908688943 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275211861/10000000000 : ℝ), (900729143/2500000000 : ℝ), (2219060007/5000000000 : ℝ)] ![(8751130371593/25000000000000 : ℝ), (14167967525791/50000000000000 : ℝ), (7331908688943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275211861/10000000000 : ℝ)|^21 ≤ (8751130371593/25000000000000 : ℝ)^17
        have hw : |(4275211861/10000000000 : ℝ)|=(4275211861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900729143/2500000000 : ℝ)|^21 ≤ (14167967525791/50000000000000 : ℝ)^17
        have hw : |(900729143/2500000000 : ℝ)|=(900729143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2219060007/5000000000 : ℝ)|^21 ≤ (7331908688943/20000000000000 : ℝ)^17
        have hw : |(2219060007/5000000000 : ℝ)|=(2219060007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3133893817/10000000000 : ℝ)*x 0 + (3640136011/10000000000 : ℝ)*x 1 + (546901821/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3133893817/10000000000 : ℝ)^21 ≤ (11925754823187/50000000000000 : ℝ)^17 := by
    have hnat : (3133893817 : ℕ)^21*50000000000000^17 ≤ 11925754823187^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3133893817 10000000000 11925754823187 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3640136011/10000000000 : ℝ)^21 ≤ (1434898464741/5000000000000 : ℝ)^17 := by
    have hnat : (3640136011 : ℕ)^21*5000000000000^17 ≤ 1434898464741^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3640136011 10000000000 1434898464741 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546901821/1000000000 : ℝ)^21 ≤ (4745052105331/10000000000000 : ℝ)^17 := by
    have hnat : (546901821 : ℕ)^21*10000000000000^17 ≤ 4745052105331^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546901821 1000000000 4745052105331 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3133893817/10000000000 : ℝ), (3640136011/10000000000 : ℝ), (546901821/1000000000 : ℝ)] ![(11925754823187/50000000000000 : ℝ), (1434898464741/5000000000000 : ℝ), (4745052105331/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3133893817/10000000000 : ℝ)|^21 ≤ (11925754823187/50000000000000 : ℝ)^17
        have hw : |(-3133893817/10000000000 : ℝ)|=(3133893817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3640136011/10000000000 : ℝ)|^21 ≤ (1434898464741/5000000000000 : ℝ)^17
        have hw : |(3640136011/10000000000 : ℝ)|=(3640136011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546901821/1000000000 : ℝ)|^21 ≤ (4745052105331/10000000000000 : ℝ)^17
        have hw : |(546901821/1000000000 : ℝ)|=(546901821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (718533507/1000000000 : ℝ)*x 0 + (-421419151/10000000000 : ℝ)*x 1 + (981895397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (718533507/1000000000 : ℝ)^21 ≤ (8309595197841/12500000000000 : ℝ)^17 := by
    have hnat : (718533507 : ℕ)^21*12500000000000^17 ≤ 8309595197841^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718533507 1000000000 8309595197841 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421419151/10000000000 : ℝ)^21 ≤ (400080717711/20000000000000 : ℝ)^17 := by
    have hnat : (421419151 : ℕ)^21*20000000000000^17 ≤ 400080717711^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421419151 10000000000 400080717711 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (981895397/2500000000 : ℝ)^21 ≤ (3940354351163/12500000000000 : ℝ)^17 := by
    have hnat : (981895397 : ℕ)^21*12500000000000^17 ≤ 3940354351163^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981895397 2500000000 3940354351163 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(718533507/1000000000 : ℝ), (-421419151/10000000000 : ℝ), (981895397/2500000000 : ℝ)] ![(8309595197841/12500000000000 : ℝ), (400080717711/20000000000000 : ℝ), (3940354351163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(718533507/1000000000 : ℝ)|^21 ≤ (8309595197841/12500000000000 : ℝ)^17
        have hw : |(718533507/1000000000 : ℝ)|=(718533507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421419151/10000000000 : ℝ)|^21 ≤ (400080717711/20000000000000 : ℝ)^17
        have hw : |(-421419151/10000000000 : ℝ)|=(421419151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(981895397/2500000000 : ℝ)|^21 ≤ (3940354351163/12500000000000 : ℝ)^17
        have hw : |(981895397/2500000000 : ℝ)|=(981895397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1022093219/10000000000 : ℝ)*x 0 + (426359951/500000000 : ℝ)*x 1 + (-1783674481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022093219/10000000000 : ℝ)^21 ≤ (2988129768981/50000000000000 : ℝ)^17 := by
    have hnat : (1022093219 : ℕ)^21*50000000000000^17 ≤ 2988129768981^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022093219 10000000000 2988129768981 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426359951/500000000 : ℝ)^21 ≤ (1026681094869/1250000000000 : ℝ)^17 := by
    have hnat : (426359951 : ℕ)^21*1250000000000^17 ≤ 1026681094869^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426359951 500000000 1026681094869 1250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783674481/10000000000 : ℝ)^21 ≤ (594462642539/5000000000000 : ℝ)^17 := by
    have hnat : (1783674481 : ℕ)^21*5000000000000^17 ≤ 594462642539^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783674481 10000000000 594462642539 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1022093219/10000000000 : ℝ), (426359951/500000000 : ℝ), (-1783674481/10000000000 : ℝ)] ![(2988129768981/50000000000000 : ℝ), (1026681094869/1250000000000 : ℝ), (594462642539/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1022093219/10000000000 : ℝ)|^21 ≤ (2988129768981/50000000000000 : ℝ)^17
        have hw : |(1022093219/10000000000 : ℝ)|=(1022093219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(426359951/500000000 : ℝ)|^21 ≤ (1026681094869/1250000000000 : ℝ)^17
        have hw : |(426359951/500000000 : ℝ)|=(426359951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1783674481/10000000000 : ℝ)|^21 ≤ (594462642539/5000000000000 : ℝ)^17
        have hw : |(-1783674481/10000000000 : ℝ)|=(1783674481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s0_25 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3082043527/5000000000 : ℝ)*x 0 + (2596680789/10000000000 : ℝ)*x 1 + (26323097/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3082043527/5000000000 : ℝ)^21 ≤ (27504016760377/50000000000000 : ℝ)^17 := by
    have hnat : (3082043527 : ℕ)^21*50000000000000^17 ≤ 27504016760377^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3082043527 5000000000 27504016760377 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596680789/10000000000 : ℝ)^21 ≤ (18907525632833/100000000000000 : ℝ)^17 := by
    have hnat : (2596680789 : ℕ)^21*100000000000000^17 ≤ 18907525632833^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596680789 10000000000 18907525632833 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26323097/78125000 : ℝ)^21 ≤ (26084440825557/100000000000000 : ℝ)^17 := by
    have hnat : (26323097 : ℕ)^21*100000000000000^17 ≤ 26084440825557^17*78125000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26323097 78125000 26084440825557 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3082043527/5000000000 : ℝ), (2596680789/10000000000 : ℝ), (26323097/78125000 : ℝ)] ![(27504016760377/50000000000000 : ℝ), (18907525632833/100000000000000 : ℝ), (26084440825557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3082043527/5000000000 : ℝ)|^21 ≤ (27504016760377/50000000000000 : ℝ)^17
        have hw : |(3082043527/5000000000 : ℝ)|=(3082043527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596680789/10000000000 : ℝ)|^21 ≤ (18907525632833/100000000000000 : ℝ)^17
        have hw : |(2596680789/10000000000 : ℝ)|=(2596680789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26323097/78125000 : ℝ)|^21 ≤ (26084440825557/100000000000000 : ℝ)^17
        have hw : |(26323097/78125000 : ℝ)|=(26323097/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-6172377/15625000 : ℝ)*x 0 + (1009721303/2500000000 : ℝ)*x 1 + (1084028963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6172377/15625000 : ℝ)^21 ≤ (31748440621663/100000000000000 : ℝ)^17 := by
    have hnat : (6172377 : ℕ)^21*100000000000000^17 ≤ 31748440621663^17*15625000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6172377 15625000 31748440621663 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009721303/2500000000 : ℝ)^21 ≤ (16315003234531/50000000000000 : ℝ)^17 := by
    have hnat : (1009721303 : ℕ)^21*50000000000000^17 ≤ 16315003234531^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009721303 2500000000 16315003234531 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084028963/2500000000 : ℝ)^21 ≤ (4452694111229/12500000000000 : ℝ)^17 := by
    have hnat : (1084028963 : ℕ)^21*12500000000000^17 ≤ 4452694111229^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084028963 2500000000 4452694111229 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6172377/15625000 : ℝ), (1009721303/2500000000 : ℝ), (1084028963/2500000000 : ℝ)] ![(31748440621663/100000000000000 : ℝ), (16315003234531/50000000000000 : ℝ), (4452694111229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6172377/15625000 : ℝ)|^21 ≤ (31748440621663/100000000000000 : ℝ)^17
        have hw : |(-6172377/15625000 : ℝ)|=(6172377/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1009721303/2500000000 : ℝ)|^21 ≤ (16315003234531/50000000000000 : ℝ)^17
        have hw : |(1009721303/2500000000 : ℝ)|=(1009721303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084028963/2500000000 : ℝ)|^21 ≤ (4452694111229/12500000000000 : ℝ)^17
        have hw : |(1084028963/2500000000 : ℝ)|=(1084028963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1052901441/2000000000 : ℝ)*x 0 + (-2133377973/10000000000 : ℝ)*x 1 + (148533471/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052901441/2000000000 : ℝ)^21 ≤ (11317091955239/25000000000000 : ℝ)^17 := by
    have hnat : (1052901441 : ℕ)^21*25000000000000^17 ≤ 11317091955239^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052901441 2000000000 11317091955239 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2133377973/10000000000 : ℝ)^21 ≤ (14832057767867/100000000000000 : ℝ)^17 := by
    have hnat : (2133377973 : ℕ)^21*100000000000000^17 ≤ 14832057767867^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133377973 10000000000 14832057767867 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148533471/312500000 : ℝ)^21 ≤ (39899574399163/100000000000000 : ℝ)^17 := by
    have hnat : (148533471 : ℕ)^21*100000000000000^17 ≤ 39899574399163^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148533471 312500000 39899574399163 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052901441/2000000000 : ℝ), (-2133377973/10000000000 : ℝ), (148533471/312500000 : ℝ)] ![(11317091955239/25000000000000 : ℝ), (14832057767867/100000000000000 : ℝ), (39899574399163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052901441/2000000000 : ℝ)|^21 ≤ (11317091955239/25000000000000 : ℝ)^17
        have hw : |(1052901441/2000000000 : ℝ)|=(1052901441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2133377973/10000000000 : ℝ)|^21 ≤ (14832057767867/100000000000000 : ℝ)^17
        have hw : |(-2133377973/10000000000 : ℝ)|=(2133377973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148533471/312500000 : ℝ)|^21 ≤ (39899574399163/100000000000000 : ℝ)^17
        have hw : |(148533471/312500000 : ℝ)|=(148533471/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2861926087/10000000000 : ℝ)*x 0 + (1535311951/2500000000 : ℝ)*x 1 + (-1570713139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2861926087/10000000000 : ℝ)^21 ≤ (21321282974749/100000000000000 : ℝ)^17 := by
    have hnat : (2861926087 : ℕ)^21*100000000000000^17 ≤ 21321282974749^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2861926087 10000000000 21321282974749 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1535311951/2500000000 : ℝ)^21 ≤ (54756370134903/100000000000000 : ℝ)^17 := by
    have hnat : (1535311951 : ℕ)^21*100000000000000^17 ≤ 54756370134903^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535311951 2500000000 54756370134903 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570713139/5000000000 : ℝ)^21 ≤ (23922346876793/100000000000000 : ℝ)^17 := by
    have hnat : (1570713139 : ℕ)^21*100000000000000^17 ≤ 23922346876793^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570713139 5000000000 23922346876793 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2861926087/10000000000 : ℝ), (1535311951/2500000000 : ℝ), (-1570713139/5000000000 : ℝ)] ![(21321282974749/100000000000000 : ℝ), (54756370134903/100000000000000 : ℝ), (23922346876793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2861926087/10000000000 : ℝ)|^21 ≤ (21321282974749/100000000000000 : ℝ)^17
        have hw : |(2861926087/10000000000 : ℝ)|=(2861926087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1535311951/2500000000 : ℝ)|^21 ≤ (54756370134903/100000000000000 : ℝ)^17
        have hw : |(1535311951/2500000000 : ℝ)|=(1535311951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1570713139/5000000000 : ℝ)|^21 ≤ (23922346876793/100000000000000 : ℝ)^17
        have hw : |(-1570713139/5000000000 : ℝ)|=(1570713139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322021_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2237461641/5000000000 : ℝ)*x 0 + (3805965023/10000000000 : ℝ)*x 1 + (4040193617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237461641/5000000000 : ℝ)^21 ≤ (37035439150041/100000000000000 : ℝ)^17 := by
    have hnat : (2237461641 : ℕ)^21*100000000000000^17 ≤ 37035439150041^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237461641 5000000000 37035439150041 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3805965023/10000000000 : ℝ)^21 ≤ (3790187014807/12500000000000 : ℝ)^17 := by
    have hnat : (3805965023 : ℕ)^21*12500000000000^17 ≤ 3790187014807^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805965023 10000000000 3790187014807 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4040193617/10000000000 : ℝ)^21 ≤ (8160766178181/25000000000000 : ℝ)^17 := by
    have hnat : (4040193617 : ℕ)^21*25000000000000^17 ≤ 8160766178181^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4040193617 10000000000 8160766178181 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2237461641/5000000000 : ℝ), (3805965023/10000000000 : ℝ), (4040193617/10000000000 : ℝ)] ![(37035439150041/100000000000000 : ℝ), (3790187014807/12500000000000 : ℝ), (8160766178181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2237461641/5000000000 : ℝ)|^21 ≤ (37035439150041/100000000000000 : ℝ)^17
        have hw : |(2237461641/5000000000 : ℝ)|=(2237461641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3805965023/10000000000 : ℝ)|^21 ≤ (3790187014807/12500000000000 : ℝ)^17
        have hw : |(3805965023/10000000000 : ℝ)|=(3805965023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4040193617/10000000000 : ℝ)|^21 ≤ (8160766178181/25000000000000 : ℝ)^17
        have hw : |(4040193617/10000000000 : ℝ)|=(4040193617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322021 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1920337987/5000000000 : ℝ)*X 0 0+(3706017833/10000000000 : ℝ)*X 0 1+(1190582241/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5968088791/10000000000 : ℝ)*X 1 0+(-988416829/10000000000 : ℝ)*X 1 1+(979651469/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1890108097/10000000000 : ℝ)*X 2 0+(7541414893/10000000000 : ℝ)*X 2 1+(-1171840139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2083868263/5000000000 : ℝ)*X 0 0+(307577979/1000000000 : ℝ)*X 0 1+(1005663319/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2801838779/5000000000 : ℝ)*X 1 0+(-22921747/625000000 : ℝ)*X 1 1+(1130360593/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((51770349/500000000 : ℝ)*X 2 0+(8873142199/10000000000 : ℝ)*X 2 1+(-124920423/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((4444350909/10000000000 : ℝ)*X 0 0+(3377647101/10000000000 : ℝ)*X 0 1+(4482519807/10000000000 : ℝ)*X 0 2+(4444350909/10000000000 : ℝ)*X 1 0+(3377647101/10000000000 : ℝ)*X 1 1+(4482519807/10000000000 : ℝ)*X 1 2+(4444350909/10000000000 : ℝ)*X 2 0+(3377647101/10000000000 : ℝ)*X 2 1+(4482519807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2153620917/5000000000 : ℝ)*X 0 0+(859947753/2500000000 : ℝ)*X 0 1+(912085657/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3115372231/5000000000 : ℝ)*X 1 0+(-976820659/10000000000 : ℝ)*X 1 1+(4627860639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1463826729/10000000000 : ℝ)*X 2 0+(7520690503/10000000000 : ℝ)*X 2 1+(-689139669/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((4275211861/10000000000 : ℝ)*X 0 0+(900729143/2500000000 : ℝ)*X 0 1+(2219060007/5000000000 : ℝ)*X 0 2+(4275211861/10000000000 : ℝ)*X 1 0+(900729143/2500000000 : ℝ)*X 1 1+(2219060007/5000000000 : ℝ)*X 1 2+(4275211861/10000000000 : ℝ)*X 2 0+(900729143/2500000000 : ℝ)*X 2 1+(2219060007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-3133893817/10000000000 : ℝ)*X 0 0+(3640136011/10000000000 : ℝ)*X 0 1+(546901821/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((718533507/1000000000 : ℝ)*X 1 0+(-421419151/10000000000 : ℝ)*X 1 1+(981895397/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1022093219/10000000000 : ℝ)*X 2 0+(426359951/500000000 : ℝ)*X 2 1+(-1783674481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((3082043527/5000000000 : ℝ)*X 0 0+(2596680789/10000000000 : ℝ)*X 0 1+(26323097/78125000 : ℝ)*X 0 2+(3082043527/5000000000 : ℝ)*X 1 0+(2596680789/10000000000 : ℝ)*X 1 1+(26323097/78125000 : ℝ)*X 1 2+(3082043527/5000000000 : ℝ)*X 2 0+(2596680789/10000000000 : ℝ)*X 2 1+(26323097/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((26253/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26253/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (70471517287189487707971/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76364580909/1000000000000 : ℝ)*(base40) + (30771978107/31250000000 : ℝ)*(base49) + (604079654209/500000000000 : ℝ)*(base50) + (428840676099/500000000000 : ℝ)*(base59) + (3119429335871/1000000000000 : ℝ)*(major_s0_0) + (3119429335871/1000000000000 : ℝ)*(major_s0_1) + (3119429335871/1000000000000 : ℝ)*(major_s0_2) + (288902455761/62500000000 : ℝ)*(sp_s0_7) + (1155621398499/250000000000 : ℝ)*(sp_s0_8) + (4622395683701/1000000000000 : ℝ)*(sp_s0_9) + (808044720807/500000000000 : ℝ)*(sp_s0_12) + (69734507/250000000000 : ℝ)*(sp_s0_19) + (2315091/50000000000 : ℝ)*(sp_s0_20) + (11238787/125000000000 : ℝ)*(sp_s0_22) + (808184189821/500000000000 : ℝ)*(f.failure) + (1155621398499/250000000000 : ℝ)*(f.sum) + (678904859/5000000000000000000000 : ℝ)*base62 + (573940183859583/2000000000000000000000000000 : ℝ)*base65 + (304476239859583/2000000000000000000000000000 : ℝ)*base67 + (302820854324857/2500000000000000000000000000 : ℝ)*base69 + (2777862590597343/10000000000000000000000000000 : ℝ)*base71 + (122587192140417/2000000000000000000000000000 : ℝ)*base73 + (297323864324857/2500000000000000000000000000 : ℝ)*base74 + (1361966757425143/2500000000000000000000000000 : ℝ)*base76 + (132017679/2500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (479/5000000000000000 : ℝ)*base87 + (479/5000000000000000 : ℝ)*base89 + (479/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5327/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(5327/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7522969176726270401283/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174653/125000000000 : ℝ)*(base3) + (53543865567/125000000000 : ℝ)*(base40) + (112266238351/250000000000 : ℝ)*(base59) + (599900077017/250000000000 : ℝ)*(major_s0_0) + (599900077017/250000000000 : ℝ)*(major_s0_1) + (599900077017/250000000000 : ℝ)*(major_s0_2) + (82161937/500000000000 : ℝ)*(sp_s0_1) + (39096317/1000000000000 : ℝ)*(sp_s0_2) + (343973929/1000000000000 : ℝ)*(sp_s0_12) + (222238622771/62500000000 : ℝ)*(sp_s0_13) + (1777827518843/500000000000 : ℝ)*(sp_s0_14) + (3555764608757/1000000000000 : ℝ)*(sp_s0_15) + (77689704657/62500000000 : ℝ)*(sp_s0_19) + (14259263/1000000000000 : ℝ)*(sp_s0_22) + (38855645177/31250000000 : ℝ)*(f.failure) + (222238622771/62500000000 : ℝ)*(f.sum) + (2377606069/10000000000000000000000 : ℝ)*base62 + (37468852079241/500000000000000000000000000 : ℝ)*base65 + (136093543220759/500000000000000000000000000 : ℝ)*base66 + (102585915346861/625000000000000000000000000 : ℝ)*base68 + (1032622348241239/2500000000000000000000000000 : ℝ)*base70 + (138752073920759/500000000000000000000000000 : ℝ)*base73 + (226254712840639/625000000000000000000000000 : ℝ)*base74 + (910712118221861/625000000000000000000000000 : ℝ)*base76 + (395483449/1000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (327/312500000000000 : ℝ)*base86 + (327/312500000000000 : ℝ)*base88 + (327/312500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(881/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(881/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6401447270286211178727/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2873097/500000000000 : ℝ)*(base11) + (1058467301781/1000000000000 : ℝ)*(base40) + (461134603453/500000000000 : ℝ)*(base49) + (1605834119649/1000000000000 : ℝ)*(base50) + (968492704797/1000000000000 : ℝ)*(base59) + (4178356107533/1000000000000 : ℝ)*(major_s0_0) + (4178356107533/1000000000000 : ℝ)*(major_s0_1) + (4178356107533/1000000000000 : ℝ)*(major_s0_2) + (51559817/1000000000000 : ℝ)*(sp_s0_0) + (6496167/500000000000 : ℝ)*(sp_s0_15) + (247663569789/40000000000 : ℝ)*(sp_s0_20) + (386977909421/62500000000 : ℝ)*(sp_s0_21) + (6191633558401/1000000000000 : ℝ)*(sp_s0_22) + (2165063530511/1000000000000 : ℝ)*(sp_s0_25) + (2165063530511/1000000000000 : ℝ)*(f.failure) + (386977909421/62500000000 : ℝ)*(f.sum) + (2636002511/10000000000000000000000 : ℝ)*base62 + (115144751807091/2000000000000000000000000000 : ℝ)*base64 + (197429508392909/2000000000000000000000000000 : ℝ)*base67 + (77200321349211/2500000000000000000000000000 : ℝ)*base69 + (3686652687638611/10000000000000000000000000000 : ℝ)*base70 + (768620940007091/2000000000000000000000000000 : ℝ)*base73 + (178499925400789/2500000000000000000000000000 : ℝ)*base75 + (1784598299599211/2500000000000000000000000000 : ℝ)*base77 + (753553911/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (1789/10000000000000000 : ℝ)*base87 + (1789/10000000000000000 : ℝ)*base89 + (1789/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (26253/100000 : ℝ) ^ (41/8 : ℝ) ≤ (26377405074512061/25000000000000000000 : ℝ) := by
    have hpowers : (26253/100000 : ℝ)^41 ≤ (26377405074512061/25000000000000000000 : ℝ)^8 := by
      have hnat : (26253 : ℕ)^41*25000000000000000000^8 ≤ 26377405074512061^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26253 100000 26377405074512061 25000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26253/100000 : ℝ)) (X := (26377405074512061/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25026377405074512061/25000000000000000000 : ℝ) ≤ (10002057850694173/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (25026377405074512061/25000000000000000000 : ℝ)^8 ≤ (10002057850694173/10000000000000000 : ℝ)^41 := by
      have hnat : (25026377405074512061 : ℕ)^8*10000000000000000^41 ≤ 10002057850694173^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026377405074512061 25000000000000000000 10002057850694173 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002057850694173/10000000000000000 : ℝ)) (X := (25026377405074512061/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12526377405074512061/12500000000000000000 : ℝ) ≤ (2501028489098587/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (12526377405074512061/12500000000000000000 : ℝ)^8 ≤ (2501028489098587/2500000000000000 : ℝ)^41 := by
      have hnat : (12526377405074512061 : ℕ)^8*2500000000000000^41 ≤ 2501028489098587^41*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12526377405074512061 12500000000000000000 2501028489098587 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501028489098587/2500000000000000 : ℝ)) (X := (12526377405074512061/12500000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(685950231391/875100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(27414742669/35004000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (26253/100000 : ℝ)) (alpha := (685950231391/875100000000000 : ℝ)) (beta := (27414742669/35004000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (26253/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(685950231391/875100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(27414742669/35004000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5327/100000 : ℝ) ^ (41/8 : ℝ) ≤ (29731979249049/100000000000000000000 : ℝ) := by
    have hpowers : (5327/100000 : ℝ)^41 ≤ (29731979249049/100000000000000000000 : ℝ)^8 := by
      have hnat : (5327 : ℕ)^41*100000000000000000000^8 ≤ 29731979249049^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5327 100000 29731979249049 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5327/100000 : ℝ)) (X := (29731979249049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100000029731979249049/100000000000000000000 : ℝ) ≤ (625000036258507/625000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100000029731979249049/100000000000000000000 : ℝ)^8 ≤ (625000036258507/625000000000000 : ℝ)^41 := by
      have hnat : (100000029731979249049 : ℕ)^8*625000000000000^41 ≤ 625000036258507^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000029731979249049 100000000000000000000 625000036258507 625000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000036258507/625000000000000 : ℝ)) (X := (100000029731979249049/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50000029731979249049/50000000000000000000 : ℝ) ≤ (2500000290068021/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50000029731979249049/50000000000000000000 : ℝ)^8 ≤ (2500000290068021/2500000000000000 : ℝ)^41 := by
      have hnat : (50000029731979249049 : ℕ)^8*2500000000000000^41 ≤ 2500000290068021^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000029731979249049 50000000000000000000 2500000290068021 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000290068021/2500000000000000 : ℝ)) (X := (50000029731979249049/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(36258507/33293750000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(145033993/133175000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (5327/100000 : ℝ)) (alpha := (36258507/33293750000000 : ℝ)) (beta := (145033993/133175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (5327/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(36258507/33293750000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(145033993/133175000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (881/2500 : ℝ) ^ (41/8 : ℝ) ≤ (23852230111844123/5000000000000000000 : ℝ) := by
    have hpowers : (881/2500 : ℝ)^41 ≤ (23852230111844123/5000000000000000000 : ℝ)^8 := by
      have hnat : (881 : ℕ)^41*5000000000000000000^8 ≤ 23852230111844123^8*2500^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        881 2500 23852230111844123 5000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (881/2500 : ℝ)) (X := (23852230111844123/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (5023852230111844123/5000000000000000000 : ℝ) ≤ (625580648030749/625000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (5023852230111844123/5000000000000000000 : ℝ)^8 ≤ (625580648030749/625000000000000 : ℝ)^41 := by
      have hnat : (5023852230111844123 : ℕ)^8*625000000000000^41 ≤ 625580648030749^41*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5023852230111844123 5000000000000000000 625580648030749 625000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625580648030749/625000000000000 : ℝ)) (X := (5023852230111844123/5000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2523852230111844123/2500000000000000000 : ℝ) ≤ (2003709060470843/2000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2523852230111844123/2500000000000000000 : ℝ)^8 ≤ (2003709060470843/2000000000000000 : ℝ)^41 := by
      have hnat : (2523852230111844123 : ℕ)^8*2000000000000000^41 ≤ 2003709060470843^41*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2523852230111844123 2500000000000000000 2003709060470843 2000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003709060470843/2000000000000000 : ℝ)) (X := (2523852230111844123/2500000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(580648030749/220250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(9254933862231/3524000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (881/2500 : ℝ)) (alpha := (580648030749/220250000000000 : ℝ)) (beta := (9254933862231/3524000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (881/2500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(580648030749/220250000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(9254933862231/3524000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-6172377/15625000 : ℝ)*X 0 0+(1009721303/2500000000 : ℝ)*X 0 1+(1084028963/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1052901441/2000000000 : ℝ)*X 1 0+(-2133377973/10000000000 : ℝ)*X 1 1+(148533471/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2861926087/10000000000 : ℝ)*X 2 0+(1535311951/2500000000 : ℝ)*X 2 1+(-1570713139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2237461641/5000000000 : ℝ)*X 0 0+(3805965023/10000000000 : ℝ)*X 0 1+(4040193617/10000000000 : ℝ)*X 0 2+(2237461641/5000000000 : ℝ)*X 1 0+(3805965023/10000000000 : ℝ)*X 1 1+(4040193617/10000000000 : ℝ)*X 1 2+(2237461641/5000000000 : ℝ)*X 2 0+(3805965023/10000000000 : ℝ)*X 2 1+(4040193617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322021_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-41443477931708676355637082593979/4889190992500000000000000000000 : ℝ) := by norm_num
    linear_combination (147041/1000000000000 : ℝ)*(base3) + (75251/1000000000000 : ℝ)*(base8) + (5161/200000000000 : ℝ)*(base19) + (36880748411/200000000000 : ℝ)*(base40) + (487232611097/500000000000 : ℝ)*(base49) + (2631888799/3906250000 : ℝ)*(base50) + (201520630247/500000000000 : ℝ)*(base59) + (6127/1000000000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (2825517002129/1000000000000 : ℝ)*(sp_s1_0) + (353189649827/125000000000 : ℝ)*(sp_s1_1) + (141275853869/50000000000 : ℝ)*(sp_s1_2) + (999999852959/1000000000000 : ℝ)*(sp_s1_6) + (141275853869/50000000000 : ℝ)*(f.sum) + (1639646991363119/3352205000000000000000000000 : ℝ)*base62 + (523730799161/1762000000000000000000000 : ℝ)*base64 + (4545586164029/7610000000000000000000000 : ℝ)*base67 + (2686811535779/4405000000000000000000000 : ℝ)*base68 + (8597534891154253/25698770000000000000000000000 : ℝ)*base70 + (157711991313/5834000000000000000000000 : ℝ)*base73 + (2571847980989/3805000000000000000000000 : ℝ)*base74 + (15531179225109/29170000000000000000000000 : ℝ)*base76 + (19285826442423269/22198370000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p022_b009 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 21 ≤ c.val) (hhi : c.val < 22)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=21 := by omega
  rcases hc with rfl
  · exact collision_c322021 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 21 ≤ c.val) (hhi : c.val < 22)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b009 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

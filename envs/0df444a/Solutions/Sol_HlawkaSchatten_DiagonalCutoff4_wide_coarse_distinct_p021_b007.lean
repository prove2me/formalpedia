-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p021_b007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:43:41.169152+00:00
-- url     : https://prove2.me/submissions/ad008d43-4097-4d81-be1e-d810d30266d2

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
theorem collision_support_c321017_s0_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5244483717/10000000000 : ℝ)*x 0 + (675400813/2000000000 : ℝ)*x 1 + (1840174917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244483717/10000000000 : ℝ)^83 ≤ (44953766205091/100000000000000 : ℝ)^67 := by
    have hnat : (5244483717 : ℕ)^83*100000000000000^67 ≤ 44953766205091^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244483717 10000000000 44953766205091 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675400813/2000000000 : ℝ)^83 ≤ (13029030931757/50000000000000 : ℝ)^67 := by
    have hnat : (675400813 : ℕ)^83*50000000000000^67 ≤ 13029030931757^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675400813 2000000000 13029030931757 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1840174917/5000000000 : ℝ)^83 ≤ (14494085956783/50000000000000 : ℝ)^67 := by
    have hnat : (1840174917 : ℕ)^83*50000000000000^67 ≤ 14494085956783^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840174917 5000000000 14494085956783 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5244483717/10000000000 : ℝ), (675400813/2000000000 : ℝ), (1840174917/5000000000 : ℝ)] ![(44953766205091/100000000000000 : ℝ), (13029030931757/50000000000000 : ℝ), (14494085956783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5244483717/10000000000 : ℝ)|^83 ≤ (44953766205091/100000000000000 : ℝ)^67
        have hw : |(-5244483717/10000000000 : ℝ)|=(5244483717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675400813/2000000000 : ℝ)|^83 ≤ (13029030931757/50000000000000 : ℝ)^67
        have hw : |(675400813/2000000000 : ℝ)|=(675400813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1840174917/5000000000 : ℝ)|^83 ≤ (14494085956783/50000000000000 : ℝ)^67
        have hw : |(1840174917/5000000000 : ℝ)|=(1840174917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321017_s0_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3826266969/10000000000 : ℝ)*x 0 + (-2463792397/10000000000 : ℝ)*x 1 + (589392251/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3826266969/10000000000 : ℝ)^83 ≤ (15209310152733/50000000000000 : ℝ)^67 := by
    have hnat : (3826266969 : ℕ)^83*50000000000000^67 ≤ 15209310152733^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3826266969 10000000000 15209310152733 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463792397/10000000000 : ℝ)^83 ≤ (8816283446751/50000000000000 : ℝ)^67 := by
    have hnat : (2463792397 : ℕ)^83*50000000000000^67 ≤ 8816283446751^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463792397 10000000000 8816283446751 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589392251/1000000000 : ℝ)^83 ≤ (12987203197321/25000000000000 : ℝ)^67 := by
    have hnat : (589392251 : ℕ)^83*25000000000000^67 ≤ 12987203197321^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589392251 1000000000 12987203197321 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3826266969/10000000000 : ℝ), (-2463792397/10000000000 : ℝ), (589392251/1000000000 : ℝ)] ![(15209310152733/50000000000000 : ℝ), (8816283446751/50000000000000 : ℝ), (12987203197321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3826266969/10000000000 : ℝ)|^83 ≤ (15209310152733/50000000000000 : ℝ)^67
        have hw : |(3826266969/10000000000 : ℝ)|=(3826266969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2463792397/10000000000 : ℝ)|^83 ≤ (8816283446751/50000000000000 : ℝ)^67
        have hw : |(-2463792397/10000000000 : ℝ)|=(2463792397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(589392251/1000000000 : ℝ)|^83 ≤ (12987203197321/25000000000000 : ℝ)^67
        have hw : |(589392251/1000000000 : ℝ)|=(589392251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321017_s0_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (894298247/2500000000 : ℝ)*x 0 + (243130369/400000000 : ℝ)*x 1 + (-2510317951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894298247/2500000000 : ℝ)^83 ≤ (699625503033/2500000000000 : ℝ)^67 := by
    have hnat : (894298247 : ℕ)^83*2500000000000^67 ≤ 699625503033^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894298247 2500000000 699625503033 2500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243130369/400000000 : ℝ)^83 ≤ (10793800825601/20000000000000 : ℝ)^67 := by
    have hnat : (243130369 : ℕ)^83*20000000000000^67 ≤ 10793800825601^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243130369 400000000 10793800825601 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510317951/10000000000 : ℝ)^83 ≤ (9022987868241/50000000000000 : ℝ)^67 := by
    have hnat : (2510317951 : ℕ)^83*50000000000000^67 ≤ 9022987868241^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510317951 10000000000 9022987868241 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(894298247/2500000000 : ℝ), (243130369/400000000 : ℝ), (-2510317951/10000000000 : ℝ)] ![(699625503033/2500000000000 : ℝ), (10793800825601/20000000000000 : ℝ), (9022987868241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(894298247/2500000000 : ℝ)|^83 ≤ (699625503033/2500000000000 : ℝ)^67
        have hw : |(894298247/2500000000 : ℝ)|=(894298247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243130369/400000000 : ℝ)|^83 ≤ (10793800825601/20000000000000 : ℝ)^67
        have hw : |(243130369/400000000 : ℝ)|=(243130369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2510317951/10000000000 : ℝ)|^83 ≤ (9022987868241/50000000000000 : ℝ)^67
        have hw : |(-2510317951/10000000000 : ℝ)|=(2510317951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321017_s0_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2898996117/10000000000 : ℝ)*x 0 + (4925887407/10000000000 : ℝ)*x 1 + (4465568819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2898996117/10000000000 : ℝ)^83 ≤ (10784478834431/50000000000000 : ℝ)^67 := by
    have hnat : (2898996117 : ℕ)^83*50000000000000^67 ≤ 10784478834431^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2898996117 10000000000 10784478834431 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4925887407/10000000000 : ℝ)^83 ≤ (10398913065549/25000000000000 : ℝ)^67 := by
    have hnat : (4925887407 : ℕ)^83*25000000000000^67 ≤ 10398913065549^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4925887407 10000000000 10398913065549 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4465568819/10000000000 : ℝ)^83 ≤ (36835390057503/100000000000000 : ℝ)^67 := by
    have hnat : (4465568819 : ℕ)^83*100000000000000^67 ≤ 36835390057503^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4465568819 10000000000 36835390057503 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2898996117/10000000000 : ℝ), (4925887407/10000000000 : ℝ), (4465568819/10000000000 : ℝ)] ![(10784478834431/50000000000000 : ℝ), (10398913065549/25000000000000 : ℝ), (36835390057503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2898996117/10000000000 : ℝ)|^83 ≤ (10784478834431/50000000000000 : ℝ)^67
        have hw : |(2898996117/10000000000 : ℝ)|=(2898996117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4925887407/10000000000 : ℝ)|^83 ≤ (10398913065549/25000000000000 : ℝ)^67
        have hw : |(4925887407/10000000000 : ℝ)|=(4925887407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4465568819/10000000000 : ℝ)|^83 ≤ (36835390057503/100000000000000 : ℝ)^67
        have hw : |(4465568819/10000000000 : ℝ)|=(4465568819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321017 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-5244483717/10000000000 : ℝ)*X 0 0+(675400813/2000000000 : ℝ)*X 0 1+(1840174917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321017_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3826266969/10000000000 : ℝ)*X 1 0+(-2463792397/10000000000 : ℝ)*X 1 1+(589392251/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321017_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((894298247/2500000000 : ℝ)*X 2 0+(243130369/400000000 : ℝ)*X 2 1+(-2510317951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321017_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2898996117/10000000000 : ℝ)*X 0 0+(4925887407/10000000000 : ℝ)*X 0 1+(4465568819/10000000000 : ℝ)*X 0 2+(2898996117/10000000000 : ℝ)*X 1 0+(4925887407/10000000000 : ℝ)*X 1 1+(4465568819/10000000000 : ℝ)*X 1 2+(2898996117/10000000000 : ℝ)*X 2 0+(4925887407/10000000000 : ℝ)*X 2 1+(4465568819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321017_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-26316/3125 : ℝ) < ((-11897/6250 : ℝ)*P 0+(-11897/6250 : ℝ)*P 1+(-11897/6250 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-26316/3125 : ℝ) < (-41712003065740696541469/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (192349/1000000000000 : ℝ)*(base5) + (4153/1000000000000 : ℝ)*(base8) + (94911/1000000000000 : ℝ)*(base13) + (42461/1000000000000 : ℝ)*(base29) + (295537896393/500000000000 : ℝ)*(base49) + (42445406803/125000000000 : ℝ)*(base50) + (280067981481/500000000000 : ℝ)*(base59) + (8446900797/31250000000 : ℝ)*(base60) + (11897/6250 : ℝ)*(major_s0_0) + (11897/6250 : ℝ)*(major_s0_1) + (11897/6250 : ℝ)*(major_s0_2) + (695200026329/250000000000 : ℝ)*(sp_s0_0) + (139040010219/50000000000 : ℝ)*(sp_s0_1) + (2780800396729/1000000000000 : ℝ)*(sp_s0_2) + (99999976519/100000000000 : ℝ)*(sp_s0_6) + (139040010219/50000000000 : ℝ)*(f.sum) + (3742921989/5000000000000000000000 : ℝ)*base62 + (443246861/1000000000000000000000 : ℝ)*base65 + (2669093837/5000000000000000000000 : ℝ)*base66 + (57049961/1000000000000000000000 : ℝ)*base68 + (268828517/1000000000000000000000 : ℝ)*base71 + (96125511/1000000000000000000000 : ℝ)*base73 + (237844179/5000000000000000000000 : ℝ)*base75 + (424714161/2000000000000000000000 : ℝ)*base77 + (3055228331/10000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c321018_s0_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4829080311/10000000000 : ℝ)*x 0 + (-396252481/2000000000 : ℝ)*x 1 + (-5338533091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4829080311/10000000000 : ℝ)^83 ≤ (8117071318483/20000000000000 : ℝ)^67 := by
    have hnat : (4829080311 : ℕ)^83*20000000000000^67 ≤ 8117071318483^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829080311 10000000000 8117071318483 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396252481/2000000000 : ℝ)^83 ≤ (1682509649679/12500000000000 : ℝ)^67 := by
    have hnat : (396252481 : ℕ)^83*12500000000000^67 ≤ 1682509649679^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396252481 2000000000 1682509649679 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5338533091/10000000000 : ℝ)^83 ≤ (45954566193651/100000000000000 : ℝ)^67 := by
    have hnat : (5338533091 : ℕ)^83*100000000000000^67 ≤ 45954566193651^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5338533091 10000000000 45954566193651 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4829080311/10000000000 : ℝ), (-396252481/2000000000 : ℝ), (-5338533091/10000000000 : ℝ)] ![(8117071318483/20000000000000 : ℝ), (1682509649679/12500000000000 : ℝ), (45954566193651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4829080311/10000000000 : ℝ)|^83 ≤ (8117071318483/20000000000000 : ℝ)^67
        have hw : |(4829080311/10000000000 : ℝ)|=(4829080311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396252481/2000000000 : ℝ)|^83 ≤ (1682509649679/12500000000000 : ℝ)^67
        have hw : |(-396252481/2000000000 : ℝ)|=(396252481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5338533091/10000000000 : ℝ)|^83 ≤ (45954566193651/100000000000000 : ℝ)^67
        have hw : |(-5338533091/10000000000 : ℝ)|=(5338533091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (777436727/2000000000 : ℝ)*x 0 + (5400421283/10000000000 : ℝ)*x 1 + (2985047231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (777436727/2000000000 : ℝ)^83 ≤ (31019690443383/100000000000000 : ℝ)^67 := by
    have hnat : (777436727 : ℕ)^83*100000000000000^67 ≤ 31019690443383^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777436727 2000000000 31019690443383 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400421283/10000000000 : ℝ)^83 ≤ (46615437350267/100000000000000 : ℝ)^67 := by
    have hnat : (5400421283 : ℕ)^83*100000000000000^67 ≤ 46615437350267^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400421283 10000000000 46615437350267 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2985047231/10000000000 : ℝ)^83 ≤ (11182436099691/50000000000000 : ℝ)^67 := by
    have hnat : (2985047231 : ℕ)^83*50000000000000^67 ≤ 11182436099691^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985047231 10000000000 11182436099691 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(777436727/2000000000 : ℝ), (5400421283/10000000000 : ℝ), (2985047231/10000000000 : ℝ)] ![(31019690443383/100000000000000 : ℝ), (46615437350267/100000000000000 : ℝ), (11182436099691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(777436727/2000000000 : ℝ)|^83 ≤ (31019690443383/100000000000000 : ℝ)^67
        have hw : |(777436727/2000000000 : ℝ)|=(777436727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400421283/10000000000 : ℝ)|^83 ≤ (46615437350267/100000000000000 : ℝ)^67
        have hw : |(5400421283/10000000000 : ℝ)|=(5400421283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2985047231/10000000000 : ℝ)|^83 ≤ (11182436099691/50000000000000 : ℝ)^67
        have hw : |(2985047231/10000000000 : ℝ)|=(2985047231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2292289993/5000000000 : ℝ)*x 0 + (1326826593/5000000000 : ℝ)*x 1 + (-251148613/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292289993/5000000000 : ℝ)^83 ≤ (38055362709133/100000000000000 : ℝ)^67 := by
    have hnat : (2292289993 : ℕ)^83*100000000000000^67 ≤ 38055362709133^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292289993 5000000000 38055362709133 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1326826593/5000000000 : ℝ)^83 ≤ (151023572607/781250000000 : ℝ)^67 := by
    have hnat : (1326826593 : ℕ)^83*781250000000^67 ≤ 151023572607^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326826593 5000000000 151023572607 781250000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251148613/500000000 : ℝ)^83 ≤ (1065340499509/2500000000000 : ℝ)^67 := by
    have hnat : (251148613 : ℕ)^83*2500000000000^67 ≤ 1065340499509^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251148613 500000000 1065340499509 2500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2292289993/5000000000 : ℝ), (1326826593/5000000000 : ℝ), (-251148613/500000000 : ℝ)] ![(38055362709133/100000000000000 : ℝ), (151023572607/781250000000 : ℝ), (1065340499509/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2292289993/5000000000 : ℝ)|^83 ≤ (38055362709133/100000000000000 : ℝ)^67
        have hw : |(-2292289993/5000000000 : ℝ)|=(2292289993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1326826593/5000000000 : ℝ)|^83 ≤ (151023572607/781250000000 : ℝ)^67
        have hw : |(1326826593/5000000000 : ℝ)|=(1326826593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251148613/500000000 : ℝ)|^83 ≤ (1065340499509/2500000000000 : ℝ)^67
        have hw : |(-251148613/500000000 : ℝ)|=(251148613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (509816011/1000000000 : ℝ)*x 0 + (-837971419/10000000000 : ℝ)*x 1 + (-5894886751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509816011/1000000000 : ℝ)^83 ≤ (21702614934937/50000000000000 : ℝ)^67 := by
    have hnat : (509816011 : ℕ)^83*50000000000000^67 ≤ 21702614934937^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509816011 1000000000 21702614934937 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837971419/10000000000 : ℝ)^83 ≤ (4635428773221/100000000000000 : ℝ)^67 := by
    have hnat : (837971419 : ℕ)^83*100000000000000^67 ≤ 4635428773221^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837971419 10000000000 4635428773221 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5894886751/10000000000 : ℝ)^83 ≤ (51959341339479/100000000000000 : ℝ)^67 := by
    have hnat : (5894886751 : ℕ)^83*100000000000000^67 ≤ 51959341339479^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5894886751 10000000000 51959341339479 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(509816011/1000000000 : ℝ), (-837971419/10000000000 : ℝ), (-5894886751/10000000000 : ℝ)] ![(21702614934937/50000000000000 : ℝ), (4635428773221/100000000000000 : ℝ), (51959341339479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(509816011/1000000000 : ℝ)|^83 ≤ (21702614934937/50000000000000 : ℝ)^67
        have hw : |(509816011/1000000000 : ℝ)|=(509816011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-837971419/10000000000 : ℝ)|^83 ≤ (4635428773221/100000000000000 : ℝ)^67
        have hw : |(-837971419/10000000000 : ℝ)|=(837971419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5894886751/10000000000 : ℝ)|^83 ≤ (51959341339479/100000000000000 : ℝ)^67
        have hw : |(-5894886751/10000000000 : ℝ)|=(5894886751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2791135489/10000000000 : ℝ)*x 0 + (1517832037/2500000000 : ℝ)*x 1 + (166071873/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2791135489/10000000000 : ℝ)^83 ≤ (20579276078329/100000000000000 : ℝ)^67 := by
    have hnat : (2791135489 : ℕ)^83*100000000000000^67 ≤ 20579276078329^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791135489 10000000000 20579276078329 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1517832037/2500000000 : ℝ)^83 ≤ (6736597114261/12500000000000 : ℝ)^67 := by
    have hnat : (1517832037 : ℕ)^83*12500000000000^67 ≤ 6736597114261^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517832037 2500000000 6736597114261 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166071873/500000000 : ℝ)^83 ≤ (1595496687243/6250000000000 : ℝ)^67 := by
    have hnat : (166071873 : ℕ)^83*6250000000000^67 ≤ 1595496687243^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166071873 500000000 1595496687243 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2791135489/10000000000 : ℝ), (1517832037/2500000000 : ℝ), (166071873/500000000 : ℝ)] ![(20579276078329/100000000000000 : ℝ), (6736597114261/12500000000000 : ℝ), (1595496687243/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2791135489/10000000000 : ℝ)|^83 ≤ (20579276078329/100000000000000 : ℝ)^67
        have hw : |(2791135489/10000000000 : ℝ)|=(2791135489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1517832037/2500000000 : ℝ)|^83 ≤ (6736597114261/12500000000000 : ℝ)^67
        have hw : |(1517832037/2500000000 : ℝ)|=(1517832037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166071873/500000000 : ℝ)|^83 ≤ (1595496687243/6250000000000 : ℝ)^67
        have hw : |(166071873/500000000 : ℝ)|=(166071873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-657101/10000000000 : ℝ)*x 0 + (9155171537/10000000000 : ℝ)*x 1 + (-801761527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657101/10000000000 : ℝ)^83 ≤ (164739491/25000000000000 : ℝ)^67 := by
    have hnat : (657101 : ℕ)^83*25000000000000^67 ≤ 164739491^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657101 10000000000 164739491 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9155171537/10000000000 : ℝ)^83 ≤ (89642139615939/100000000000000 : ℝ)^67 := by
    have hnat : (9155171537 : ℕ)^83*100000000000000^67 ≤ 89642139615939^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9155171537 10000000000 89642139615939 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801761527/5000000000 : ℝ)^83 ≤ (10357201417611/100000000000000 : ℝ)^67 := by
    have hnat : (801761527 : ℕ)^83*100000000000000^67 ≤ 10357201417611^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801761527 5000000000 10357201417611 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-657101/10000000000 : ℝ), (9155171537/10000000000 : ℝ), (-801761527/5000000000 : ℝ)] ![(164739491/25000000000000 : ℝ), (89642139615939/100000000000000 : ℝ), (10357201417611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-657101/10000000000 : ℝ)|^83 ≤ (164739491/25000000000000 : ℝ)^67
        have hw : |(-657101/10000000000 : ℝ)|=(657101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9155171537/10000000000 : ℝ)|^83 ≤ (89642139615939/100000000000000 : ℝ)^67
        have hw : |(9155171537/10000000000 : ℝ)|=(9155171537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-801761527/5000000000 : ℝ)|^83 ≤ (10357201417611/100000000000000 : ℝ)^67
        have hw : |(-801761527/5000000000 : ℝ)|=(801761527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2494246189/5000000000 : ℝ)*x 0 + (605993547/2500000000 : ℝ)*x 1 + (-963565327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2494246189/5000000000 : ℝ)^83 ≤ (165045092893/390625000000 : ℝ)^67 := by
    have hnat : (2494246189 : ℕ)^83*390625000000^67 ≤ 165045092893^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494246189 5000000000 165045092893 390625000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605993547/2500000000 : ℝ)^83 ≤ (4320058315639/25000000000000 : ℝ)^67 := by
    have hnat : (605993547 : ℕ)^83*25000000000000^67 ≤ 4320058315639^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605993547 2500000000 4320058315639 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963565327/2000000000 : ℝ)^83 ≤ (5058527866959/12500000000000 : ℝ)^67 := by
    have hnat : (963565327 : ℕ)^83*12500000000000^67 ≤ 5058527866959^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963565327 2000000000 5058527866959 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2494246189/5000000000 : ℝ), (605993547/2500000000 : ℝ), (-963565327/2000000000 : ℝ)] ![(165045092893/390625000000 : ℝ), (4320058315639/25000000000000 : ℝ), (5058527866959/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2494246189/5000000000 : ℝ)|^83 ≤ (165045092893/390625000000 : ℝ)^67
        have hw : |(-2494246189/5000000000 : ℝ)|=(2494246189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605993547/2500000000 : ℝ)|^83 ≤ (4320058315639/25000000000000 : ℝ)^67
        have hw : |(605993547/2500000000 : ℝ)|=(605993547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-963565327/2000000000 : ℝ)|^83 ≤ (5058527866959/12500000000000 : ℝ)^67
        have hw : |(-963565327/2000000000 : ℝ)|=(963565327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (371880857/625000000 : ℝ)*x 0 + (-613481613/10000000000 : ℝ)*x 1 + (-647701207/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371880857/625000000 : ℝ)^83 ≤ (1051256611451/2000000000000 : ℝ)^67 := by
    have hnat : (371880857 : ℕ)^83*2000000000000^67 ≤ 1051256611451^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371880857 625000000 1051256611451 2000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613481613/10000000000 : ℝ)^83 ≤ (196879882471/6250000000000 : ℝ)^67 := by
    have hnat : (613481613 : ℕ)^83*6250000000000^67 ≤ 196879882471^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613481613 10000000000 196879882471 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647701207/1250000000 : ℝ)^83 ≤ (8857418258769/20000000000000 : ℝ)^67 := by
    have hnat : (647701207 : ℕ)^83*20000000000000^67 ≤ 8857418258769^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647701207 1250000000 8857418258769 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(371880857/625000000 : ℝ), (-613481613/10000000000 : ℝ), (-647701207/1250000000 : ℝ)] ![(1051256611451/2000000000000 : ℝ), (196879882471/6250000000000 : ℝ), (8857418258769/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(371880857/625000000 : ℝ)|^83 ≤ (1051256611451/2000000000000 : ℝ)^67
        have hw : |(371880857/625000000 : ℝ)|=(371880857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-613481613/10000000000 : ℝ)|^83 ≤ (196879882471/6250000000000 : ℝ)^67
        have hw : |(-613481613/10000000000 : ℝ)|=(613481613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-647701207/1250000000 : ℝ)|^83 ≤ (8857418258769/20000000000000 : ℝ)^67
        have hw : |(-647701207/1250000000 : ℝ)|=(647701207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (52202157/200000000 : ℝ)*x 0 + (6599291151/10000000000 : ℝ)*x 1 + (1435091779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52202157/200000000 : ℝ)^83 ≤ (4734706006297/25000000000000 : ℝ)^67 := by
    have hnat : (52202157 : ℕ)^83*25000000000000^67 ≤ 4734706006297^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52202157 200000000 4734706006297 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6599291151/10000000000 : ℝ)^83 ≤ (3734841549343/6250000000000 : ℝ)^67 := by
    have hnat : (6599291151 : ℕ)^83*6250000000000^67 ≤ 3734841549343^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6599291151 10000000000 3734841549343 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1435091779/5000000000 : ℝ)^83 ≤ (4260742235739/20000000000000 : ℝ)^67 := by
    have hnat : (1435091779 : ℕ)^83*20000000000000^67 ≤ 4260742235739^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435091779 5000000000 4260742235739 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52202157/200000000 : ℝ), (6599291151/10000000000 : ℝ), (1435091779/5000000000 : ℝ)] ![(4734706006297/25000000000000 : ℝ), (3734841549343/6250000000000 : ℝ), (4260742235739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52202157/200000000 : ℝ)|^83 ≤ (4734706006297/25000000000000 : ℝ)^67
        have hw : |(52202157/200000000 : ℝ)|=(52202157/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6599291151/10000000000 : ℝ)|^83 ≤ (3734841549343/6250000000000 : ℝ)^67
        have hw : |(6599291151/10000000000 : ℝ)|=(6599291151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1435091779/5000000000 : ℝ)|^83 ≤ (4260742235739/20000000000000 : ℝ)^67
        have hw : |(1435091779/5000000000 : ℝ)|=(1435091779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-9489309/5000000000 : ℝ)*x 0 + (3287686861/5000000000 : ℝ)*x 1 + (-963565327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9489309/5000000000 : ℝ)^83 ≤ (42491094511/100000000000000 : ℝ)^67 := by
    have hnat : (9489309 : ℕ)^83*100000000000000^67 ≤ 42491094511^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9489309 5000000000 42491094511 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3287686861/5000000000 : ℝ)^83 ≤ (7436160743883/12500000000000 : ℝ)^67 := by
    have hnat : (3287686861 : ℕ)^83*12500000000000^67 ≤ 7436160743883^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3287686861 5000000000 7436160743883 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963565327/2000000000 : ℝ)^83 ≤ (5058527866959/12500000000000 : ℝ)^67 := by
    have hnat : (963565327 : ℕ)^83*12500000000000^67 ≤ 5058527866959^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963565327 2000000000 5058527866959 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9489309/5000000000 : ℝ), (3287686861/5000000000 : ℝ), (-963565327/2000000000 : ℝ)] ![(42491094511/100000000000000 : ℝ), (7436160743883/12500000000000 : ℝ), (5058527866959/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9489309/5000000000 : ℝ)|^83 ≤ (42491094511/100000000000000 : ℝ)^67
        have hw : |(-9489309/5000000000 : ℝ)|=(9489309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3287686861/5000000000 : ℝ)|^83 ≤ (7436160743883/12500000000000 : ℝ)^67
        have hw : |(3287686861/5000000000 : ℝ)|=(3287686861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-963565327/2000000000 : ℝ)|^83 ≤ (5058527866959/12500000000000 : ℝ)^67
        have hw : |(-963565327/2000000000 : ℝ)|=(963565327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5566507421/10000000000 : ℝ)*x 0 + (119903207/400000000 : ℝ)*x 1 + (-1846970913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5566507421/10000000000 : ℝ)^83 ≤ (12099472950009/25000000000000 : ℝ)^67 := by
    have hnat : (5566507421 : ℕ)^83*25000000000000^67 ≤ 12099472950009^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5566507421 10000000000 12099472950009 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119903207/400000000 : ℝ)^83 ≤ (22481255062781/100000000000000 : ℝ)^67 := by
    have hnat : (119903207 : ℕ)^83*100000000000000^67 ≤ 22481255062781^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119903207 400000000 22481255062781 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1846970913/5000000000 : ℝ)^83 ≤ (29120853121117/100000000000000 : ℝ)^67 := by
    have hnat : (1846970913 : ℕ)^83*100000000000000^67 ≤ 29120853121117^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846970913 5000000000 29120853121117 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5566507421/10000000000 : ℝ), (119903207/400000000 : ℝ), (-1846970913/5000000000 : ℝ)] ![(12099472950009/25000000000000 : ℝ), (22481255062781/100000000000000 : ℝ), (29120853121117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5566507421/10000000000 : ℝ)|^83 ≤ (12099472950009/25000000000000 : ℝ)^67
        have hw : |(-5566507421/10000000000 : ℝ)|=(5566507421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119903207/400000000 : ℝ)|^83 ≤ (22481255062781/100000000000000 : ℝ)^67
        have hw : |(119903207/400000000 : ℝ)|=(119903207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1846970913/5000000000 : ℝ)|^83 ≤ (29120853121117/100000000000000 : ℝ)^67
        have hw : |(-1846970913/5000000000 : ℝ)|=(1846970913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4497162201/10000000000 : ℝ)*x 0 + (-1126831489/5000000000 : ℝ)*x 1 + (-1088251229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4497162201/10000000000 : ℝ)^83 ≤ (37158502706201/100000000000000 : ℝ)^67 := by
    have hnat : (4497162201 : ℕ)^83*100000000000000^67 ≤ 37158502706201^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497162201 10000000000 37158502706201 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126831489/5000000000 : ℝ)^83 ≤ (15789013394509/100000000000000 : ℝ)^67 := by
    have hnat : (1126831489 : ℕ)^83*100000000000000^67 ≤ 15789013394509^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126831489 5000000000 15789013394509 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088251229/2000000000 : ℝ)^83 ≤ (147039012151/312500000000 : ℝ)^67 := by
    have hnat : (1088251229 : ℕ)^83*312500000000^67 ≤ 147039012151^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088251229 2000000000 147039012151 312500000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4497162201/10000000000 : ℝ), (-1126831489/5000000000 : ℝ), (-1088251229/2000000000 : ℝ)] ![(37158502706201/100000000000000 : ℝ), (15789013394509/100000000000000 : ℝ), (147039012151/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4497162201/10000000000 : ℝ)|^83 ≤ (37158502706201/100000000000000 : ℝ)^67
        have hw : |(4497162201/10000000000 : ℝ)|=(4497162201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126831489/5000000000 : ℝ)|^83 ≤ (15789013394509/100000000000000 : ℝ)^67
        have hw : |(-1126831489/5000000000 : ℝ)|=(1126831489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088251229/2000000000 : ℝ)|^83 ≤ (147039012151/312500000000 : ℝ)^67
        have hw : |(-1088251229/2000000000 : ℝ)|=(1088251229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1408413831/2500000000 : ℝ)*x 0 + (258509101/625000000 : ℝ)*x 1 + (2435091437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1408413831/2500000000 : ℝ)^83 ≤ (24561082633577/50000000000000 : ℝ)^67 := by
    have hnat : (1408413831 : ℕ)^83*50000000000000^67 ≤ 24561082633577^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408413831 2500000000 24561082633577 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258509101/625000000 : ℝ)^83 ≤ (16749683966891/50000000000000 : ℝ)^67 := by
    have hnat : (258509101 : ℕ)^83*50000000000000^67 ≤ 16749683966891^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258509101 625000000 16749683966891 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2435091437/10000000000 : ℝ)^83 ≤ (17378466786183/100000000000000 : ℝ)^67 := by
    have hnat : (2435091437 : ℕ)^83*100000000000000^67 ≤ 17378466786183^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435091437 10000000000 17378466786183 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1408413831/2500000000 : ℝ), (258509101/625000000 : ℝ), (2435091437/10000000000 : ℝ)] ![(24561082633577/50000000000000 : ℝ), (16749683966891/50000000000000 : ℝ), (17378466786183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1408413831/2500000000 : ℝ)|^83 ≤ (24561082633577/50000000000000 : ℝ)^67
        have hw : |(1408413831/2500000000 : ℝ)|=(1408413831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258509101/625000000 : ℝ)|^83 ≤ (16749683966891/50000000000000 : ℝ)^67
        have hw : |(258509101/625000000 : ℝ)|=(258509101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2435091437/10000000000 : ℝ)|^83 ≤ (17378466786183/100000000000000 : ℝ)^67
        have hw : |(2435091437/10000000000 : ℝ)|=(2435091437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s0_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1530433/1250000000 : ℝ)*x 0 + (9096913599/10000000000 : ℝ)*x 1 + (-1688240231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1530433/1250000000 : ℝ)^83 ≤ (12343788623/50000000000000 : ℝ)^67 := by
    have hnat : (1530433 : ℕ)^83*50000000000000^67 ≤ 12343788623^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530433 1250000000 12343788623 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9096913599/10000000000 : ℝ)^83 ≤ (22234006947067/25000000000000 : ℝ)^67 := by
    have hnat : (9096913599 : ℕ)^83*25000000000000^67 ≤ 22234006947067^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9096913599 10000000000 22234006947067 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1688240231/10000000000 : ℝ)^83 ≤ (1379910577951/12500000000000 : ℝ)^67 := by
    have hnat : (1688240231 : ℕ)^83*12500000000000^67 ≤ 1379910577951^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688240231 10000000000 1379910577951 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1530433/1250000000 : ℝ), (9096913599/10000000000 : ℝ), (-1688240231/10000000000 : ℝ)] ![(12343788623/50000000000000 : ℝ), (22234006947067/25000000000000 : ℝ), (1379910577951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1530433/1250000000 : ℝ)|^83 ≤ (12343788623/50000000000000 : ℝ)^67
        have hw : |(-1530433/1250000000 : ℝ)|=(1530433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9096913599/10000000000 : ℝ)|^83 ≤ (22234006947067/25000000000000 : ℝ)^67
        have hw : |(9096913599/10000000000 : ℝ)|=(9096913599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1688240231/10000000000 : ℝ)|^83 ≤ (1379910577951/12500000000000 : ℝ)^67
        have hw : |(-1688240231/10000000000 : ℝ)|=(1688240231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s1_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4589443017/10000000000 : ℝ)*x 0 + (1797239581/5000000000 : ℝ)*x 1 + (-4160309507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4589443017/10000000000 : ℝ)^83 ≤ (238158597261/625000000000 : ℝ)^67 := by
    have hnat : (4589443017 : ℕ)^83*625000000000^67 ≤ 238158597261^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4589443017 10000000000 238158597261 625000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1797239581/5000000000 : ℝ)^83 ≤ (225221151209/800000000000 : ℝ)^67 := by
    have hnat : (1797239581 : ℕ)^83*800000000000^67 ≤ 225221151209^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797239581 5000000000 225221151209 800000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4160309507/10000000000 : ℝ)^83 ≤ (16870990265487/50000000000000 : ℝ)^67 := by
    have hnat : (4160309507 : ℕ)^83*50000000000000^67 ≤ 16870990265487^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160309507 10000000000 16870990265487 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4589443017/10000000000 : ℝ), (1797239581/5000000000 : ℝ), (-4160309507/10000000000 : ℝ)] ![(238158597261/625000000000 : ℝ), (225221151209/800000000000 : ℝ), (16870990265487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4589443017/10000000000 : ℝ)|^83 ≤ (238158597261/625000000000 : ℝ)^67
        have hw : |(-4589443017/10000000000 : ℝ)|=(4589443017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1797239581/5000000000 : ℝ)|^83 ≤ (225221151209/800000000000 : ℝ)^67
        have hw : |(1797239581/5000000000 : ℝ)|=(1797239581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4160309507/10000000000 : ℝ)|^83 ≤ (16870990265487/50000000000000 : ℝ)^67
        have hw : |(-4160309507/10000000000 : ℝ)|=(4160309507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s1_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (527081237/1250000000 : ℝ)*x 0 + (-1627080181/5000000000 : ℝ)*x 1 + (-4849887217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527081237/1250000000 : ℝ)^83 ≤ (4288620003001/12500000000000 : ℝ)^67 := by
    have hnat : (527081237 : ℕ)^83*12500000000000^67 ≤ 4288620003001^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527081237 1250000000 4288620003001 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1627080181/5000000000 : ℝ)^83 ≤ (24888943475023/100000000000000 : ℝ)^67 := by
    have hnat : (1627080181 : ℕ)^83*100000000000000^67 ≤ 24888943475023^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627080181 5000000000 24888943475023 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4849887217/10000000000 : ℝ)^83 ≤ (8160419297849/20000000000000 : ℝ)^67 := by
    have hnat : (4849887217 : ℕ)^83*20000000000000^67 ≤ 8160419297849^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849887217 10000000000 8160419297849 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527081237/1250000000 : ℝ), (-1627080181/5000000000 : ℝ), (-4849887217/10000000000 : ℝ)] ![(4288620003001/12500000000000 : ℝ), (24888943475023/100000000000000 : ℝ), (8160419297849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527081237/1250000000 : ℝ)|^83 ≤ (4288620003001/12500000000000 : ℝ)^67
        have hw : |(527081237/1250000000 : ℝ)|=(527081237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1627080181/5000000000 : ℝ)|^83 ≤ (24888943475023/100000000000000 : ℝ)^67
        have hw : |(-1627080181/5000000000 : ℝ)|=(1627080181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4849887217/10000000000 : ℝ)|^83 ≤ (8160419297849/20000000000000 : ℝ)^67
        have hw : |(-4849887217/10000000000 : ℝ)|=(4849887217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s1_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (784465211/2000000000 : ℝ)*x 0 + (4855145459/10000000000 : ℝ)*x 1 + (1777785487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784465211/2000000000 : ℝ)^83 ≤ (31367470635227/100000000000000 : ℝ)^67 := by
    have hnat : (784465211 : ℕ)^83*100000000000000^67 ≤ 31367470635227^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784465211 2000000000 31367470635227 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4855145459/10000000000 : ℝ)^83 ≤ (40856905366007/100000000000000 : ℝ)^67 := by
    have hnat : (4855145459 : ℕ)^83*100000000000000^67 ≤ 40856905366007^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4855145459 10000000000 40856905366007 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1777785487/5000000000 : ℝ)^83 ≤ (27775623990823/100000000000000 : ℝ)^67 := by
    have hnat : (1777785487 : ℕ)^83*100000000000000^67 ≤ 27775623990823^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777785487 5000000000 27775623990823 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(784465211/2000000000 : ℝ), (4855145459/10000000000 : ℝ), (1777785487/5000000000 : ℝ)] ![(31367470635227/100000000000000 : ℝ), (40856905366007/100000000000000 : ℝ), (27775623990823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(784465211/2000000000 : ℝ)|^83 ≤ (31367470635227/100000000000000 : ℝ)^67
        have hw : |(784465211/2000000000 : ℝ)|=(784465211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4855145459/10000000000 : ℝ)|^83 ≤ (40856905366007/100000000000000 : ℝ)^67
        have hw : |(4855145459/10000000000 : ℝ)|=(4855145459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1777785487/5000000000 : ℝ)|^83 ≤ (27775623990823/100000000000000 : ℝ)^67
        have hw : |(1777785487/5000000000 : ℝ)|=(1777785487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321018_s1_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2985381789/10000000000 : ℝ)*x 0 + (2904850807/5000000000 : ℝ)*x 1 + (-3433712861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2985381789/10000000000 : ℝ)^83 ≤ (22367977443403/100000000000000 : ℝ)^67 := by
    have hnat : (2985381789 : ℕ)^83*100000000000000^67 ≤ 22367977443403^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985381789 10000000000 22367977443403 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2904850807/5000000000 : ℝ)^83 ≤ (5103079728349/10000000000000 : ℝ)^67 := by
    have hnat : (2904850807 : ℕ)^83*10000000000000^67 ≤ 5103079728349^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2904850807 5000000000 5103079728349 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3433712861/10000000000 : ℝ)^83 ≤ (26601225260813/100000000000000 : ℝ)^67 := by
    have hnat : (3433712861 : ℕ)^83*100000000000000^67 ≤ 26601225260813^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3433712861 10000000000 26601225260813 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2985381789/10000000000 : ℝ), (2904850807/5000000000 : ℝ), (-3433712861/10000000000 : ℝ)] ![(22367977443403/100000000000000 : ℝ), (5103079728349/10000000000000 : ℝ), (26601225260813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2985381789/10000000000 : ℝ)|^83 ≤ (22367977443403/100000000000000 : ℝ)^67
        have hw : |(2985381789/10000000000 : ℝ)|=(2985381789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2904850807/5000000000 : ℝ)|^83 ≤ (5103079728349/10000000000000 : ℝ)^67
        have hw : |(2904850807/5000000000 : ℝ)|=(2904850807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3433712861/10000000000 : ℝ)|^83 ≤ (26601225260813/100000000000000 : ℝ)^67
        have hw : |(-3433712861/10000000000 : ℝ)|=(3433712861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321018 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (168549/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1467340684240883/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4829080311/10000000000 : ℝ)*X 1 0+(-396252481/2000000000 : ℝ)*X 1 1+(-5338533091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((777436727/2000000000 : ℝ)*X 2 0+(5400421283/10000000000 : ℝ)*X 2 1+(2985047231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2292289993/5000000000 : ℝ)*X 0 0+(1326826593/5000000000 : ℝ)*X 0 1+(-251148613/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((509816011/1000000000 : ℝ)*X 1 0+(-837971419/10000000000 : ℝ)*X 1 1+(-5894886751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2791135489/10000000000 : ℝ)*X 2 0+(1517832037/2500000000 : ℝ)*X 2 1+(166071873/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-657101/10000000000 : ℝ)*X 0 0+(9155171537/10000000000 : ℝ)*X 0 1+(-801761527/5000000000 : ℝ)*X 0 2+(-657101/10000000000 : ℝ)*X 1 0+(9155171537/10000000000 : ℝ)*X 1 1+(-801761527/5000000000 : ℝ)*X 1 2+(-657101/10000000000 : ℝ)*X 2 0+(9155171537/10000000000 : ℝ)*X 2 1+(-801761527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2494246189/5000000000 : ℝ)*X 0 0+(605993547/2500000000 : ℝ)*X 0 1+(-963565327/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((371880857/625000000 : ℝ)*X 1 0+(-613481613/10000000000 : ℝ)*X 1 1+(-647701207/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((52202157/200000000 : ℝ)*X 2 0+(6599291151/10000000000 : ℝ)*X 2 1+(1435091779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-9489309/5000000000 : ℝ)*X 0 0+(3287686861/5000000000 : ℝ)*X 0 1+(-963565327/2000000000 : ℝ)*X 0 2+(-9489309/5000000000 : ℝ)*X 1 0+(3287686861/5000000000 : ℝ)*X 1 1+(-963565327/2000000000 : ℝ)*X 1 2+(-9489309/5000000000 : ℝ)*X 2 0+(3287686861/5000000000 : ℝ)*X 2 1+(-963565327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5566507421/10000000000 : ℝ)*X 0 0+(119903207/400000000 : ℝ)*X 0 1+(-1846970913/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4497162201/10000000000 : ℝ)*X 1 0+(-1126831489/5000000000 : ℝ)*X 1 1+(-1088251229/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1408413831/2500000000 : ℝ)*X 2 0+(258509101/625000000 : ℝ)*X 2 1+(2435091437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-1530433/1250000000 : ℝ)*X 0 0+(9096913599/10000000000 : ℝ)*X 0 1+(-1688240231/10000000000 : ℝ)*X 0 2+(-1530433/1250000000 : ℝ)*X 1 0+(9096913599/10000000000 : ℝ)*X 1 1+(-1688240231/10000000000 : ℝ)*X 1 2+(-1530433/1250000000 : ℝ)*X 2 0+(9096913599/10000000000 : ℝ)*X 2 1+(-1688240231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((22937/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22937/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (810602672120096216943/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (870569/1000000000000 : ℝ)*(base1) + (364388740353/500000000000 : ℝ)*(base7) + (774353527107/1000000000000 : ℝ)*(base50) + (1652199/500000000000 : ℝ)*(base53) + (89115023/12500000000 : ℝ)*(base60) + (633208757337/250000000000 : ℝ)*(major_s0_0) + (633208757337/250000000000 : ℝ)*(major_s0_1) + (2532831724949/1000000000000 : ℝ)*(major_s0_2) + (14422687/500000000000 : ℝ)*(sp_s0_1) + (831402819097/250000000000 : ℝ)*(sp_s0_7) + (831395390111/250000000000 : ℝ)*(sp_s0_8) + (415701713777/125000000000 : ℝ)*(sp_s0_9) + (257400275929/125000000000 : ℝ)*(sp_s0_13) + (180348189/1000000000000 : ℝ)*(sp_s0_27) + (332651486371/250000000000 : ℝ)*(f.failure) + (415701713777/125000000000 : ℝ)*(f.sum) + (4151507972675749/10000000000000000000000000000 : ℝ)*base63 + (579081253424863/5000000000000000000000000000 : ℝ)*base64 + (883599712469219/1250000000000000000000000000 : ℝ)*base67 + (7782111657110033/10000000000000000000000000000 : ℝ)*base69 + (1643390713207721/5000000000000000000000000000 : ℝ)*base70 + (528825704030781/1250000000000000000000000000 : ℝ)*base73 + (1163627824391429/2500000000000000000000000000 : ℝ)*base75 + (392487310858571/2500000000000000000000000000 : ℝ)*base77 + (2152837627/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (463/1562500000000000 : ℝ)*base86 + (463/1562500000000000 : ℝ)*base88 + (2199/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1247/2500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1247/2500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1242439594748541950937/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (106982759263/62500000000 : ℝ)*(base1) + (8929155463/8000000000 : ℝ)*(base7) + (410549051137/1000000000000 : ℝ)*(base39) + (5584951/1000000000000 : ℝ)*(base50) + (330648318951/1000000000000 : ℝ)*(base60) + (223032742491/125000000000 : ℝ)*(major_s0_0) + (223032742491/125000000000 : ℝ)*(major_s0_1) + (223032742491/125000000000 : ℝ)*(major_s0_2) + (1392063/50000000000 : ℝ)*(sp_s0_2) + (67954119/1000000000000 : ℝ)*(sp_s0_9) + (3715810630469/1000000000000 : ℝ)*(sp_s0_14) + (2004086482261/1000000000000 : ℝ)*(sp_s0_15) + (1001995343441/500000000000 : ℝ)*(sp_s0_16) + (170884477231/500000000000 : ℝ)*(sp_s0_20) + (187469733959/200000000000 : ℝ)*(f.failure) + (2004086482261/1000000000000 : ℝ)*(f.sum) + (53677528584553/625000000000000000000000000 : ℝ)*base62 + (313566140850417/625000000000000000000000000 : ℝ)*base64 + (7607106412917/625000000000000000000000000 : ℝ)*base67 + (412343617959553/1250000000000000000000000000 : ℝ)*base68 + (532969682616281/1250000000000000000000000000 : ℝ)*base70 + (94329308225417/625000000000000000000000000 : ℝ)*base72 + (132782612165447/1250000000000000000000000000 : ℝ)*base75 + (154225913790447/1250000000000000000000000000 : ℝ)*base76 + (1597719793/5000000000000000000000 : ℝ)*base78 + (223/1250000000000000 : ℝ)*base87 + (223/1250000000000000 : ℝ)*base89 + (223/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-159/250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-159/250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (62391540165910873749057/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (769163917851/1000000000000 : ℝ)*(base1) + (15060565293/12500000000 : ℝ)*(base7) + (440021/200000000000 : ℝ)*(base39) + (429510312713/1000000000000 : ℝ)*(base44) + (505335490699/1000000000000 : ℝ)*(base50) + (4054983/1000000000000 : ℝ)*(base60) + (526835346211/200000000000 : ℝ)*(major_s0_0) + (1102333209171/500000000000 : ℝ)*(major_s0_1) + (526835346211/200000000000 : ℝ)*(major_s0_2) + (80506161/500000000000 : ℝ)*(sp_s0_1) + (15534179601/3906250000 : ℝ)*(sp_s0_21) + (2777914734971/1000000000000 : ℝ)*(sp_s0_22) + (1603793030003/500000000000 : ℝ)*(sp_s0_23) + (1390016043653/1000000000000 : ℝ)*(sp_s0_27) + (1383845050777/1000000000000 : ℝ)*(f.failure) + (1603793030003/500000000000 : ℝ)*(f.sum) + (3605618536197551/10000000000000000000000000000 : ℝ)*base62 + (1312134164621943/1000000000000000000000000000 : ℝ)*base65 + (141423990822423/2500000000000000000000000000 : ℝ)*base66 + (1143835110455687/2000000000000000000000000000 : ℝ)*base69 + (1751407924188199/2000000000000000000000000000 : ℝ)*base71 + (238801846678057/1000000000000000000000000000 : ℝ)*base72 + (1972262364737993/5000000000000000000000000000 : ℝ)*base74 + (1194592856744313/2000000000000000000000000000 : ℝ)*base77 + (1256306975964869/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (219/6250000000000000 : ℝ)*base87 + (219/6250000000000000 : ℝ)*base89 + (219/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (22937/50000 : ℝ) ^ (81/16 : ℝ) ≤ (120937498613754489/6250000000000000000 : ℝ) := by
    have hpowers : (22937/50000 : ℝ)^81 ≤ (120937498613754489/6250000000000000000 : ℝ)^16 := by
      have hnat : (22937 : ℕ)^81*6250000000000000000^16 ≤ 120937498613754489^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22937 50000 120937498613754489 6250000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22937/50000 : ℝ)) (X := (120937498613754489/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (6370937498613754489/6250000000000000000 : ℝ) ≤ (5018964436319847/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (6370937498613754489/6250000000000000000 : ℝ)^16 ≤ (5018964436319847/5000000000000000 : ℝ)^81 := by
      have hnat : (6370937498613754489 : ℕ)^16*5000000000000000^81 ≤ 5018964436319847^81*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6370937498613754489 6250000000000000000 5018964436319847 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5018964436319847/5000000000000000 : ℝ)) (X := (6370937498613754489/6250000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3245937498613754489/3125000000000000000 : ℝ) ≤ (1007528430449803/1000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3245937498613754489/3125000000000000000 : ℝ)^16 ≤ (1007528430449803/1000000000000000 : ℝ)^81 := by
      have hnat : (3245937498613754489 : ℕ)^16*1000000000000000^81 ≤ 1007528430449803^81*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3245937498613754489 3125000000000000000 1007528430449803 1000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1007528430449803/1000000000000000 : ℝ)) (X := (3245937498613754489/3125000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(18964436319847/2293700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1167357245573/143356250000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (22937/50000 : ℝ)) (alpha := (18964436319847/2293700000000000 : ℝ)) (beta := (1167357245573/143356250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22937/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(18964436319847/2293700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1167357245573/143356250000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1247/2500 : ℝ) ^ (81/16 : ℝ) ≤ (1478164034508109201/50000000000000000000 : ℝ) := by
    have hpowers : (1247/2500 : ℝ)^81 ≤ (1478164034508109201/50000000000000000000 : ℝ)^16 := by
      have hnat : (1247 : ℕ)^81*50000000000000000000^16 ≤ 1478164034508109201^16*2500^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1247 2500 1478164034508109201 50000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1247/2500 : ℝ)) (X := (1478164034508109201/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (51478164034508109201/50000000000000000000 : ℝ) ≤ (10057715968916877/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (51478164034508109201/50000000000000000000 : ℝ)^16 ≤ (10057715968916877/10000000000000000 : ℝ)^81 := by
      have hnat : (51478164034508109201 : ℕ)^16*10000000000000000^81 ≤ 10057715968916877^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51478164034508109201 50000000000000000000 10057715968916877 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057715968916877/10000000000000000 : ℝ)) (X := (51478164034508109201/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (26478164034508109201/25000000000000000000 : ℝ) ≤ (2022823395522409/2000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (26478164034508109201/25000000000000000000 : ℝ)^16 ≤ (2022823395522409/2000000000000000 : ℝ)^81 := by
      have hnat : (26478164034508109201 : ℕ)^16*2000000000000000^81 ≤ 2022823395522409^81*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26478164034508109201 25000000000000000000 2022823395522409 2000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2022823395522409/2000000000000000 : ℝ)) (X := (26478164034508109201/25000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(57715968916877/4988000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(440632880431/38968750000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1247/2500 : ℝ)) (alpha := (57715968916877/4988000000000000 : ℝ)) (beta := (440632880431/38968750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1247/2500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(57715968916877/4988000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(440632880431/38968750000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (159/250 : ℝ) ^ (81/16 : ℝ) ≤ (2023166585595707217/20000000000000000000 : ℝ) := by
    have hpowers : (159/250 : ℝ)^81 ≤ (2023166585595707217/20000000000000000000 : ℝ)^16 := by
      have hnat : (159 : ℕ)^81*20000000000000000000^16 ≤ 2023166585595707217^16*250^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        159 250 2023166585595707217 20000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (159/250 : ℝ)) (X := (2023166585595707217/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (22023166585595707217/20000000000000000000 : ℝ) ≤ (2038433821749659/2000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (22023166585595707217/20000000000000000000 : ℝ)^16 ≤ (2038433821749659/2000000000000000 : ℝ)^81 := by
      have hnat : (22023166585595707217 : ℕ)^16*2000000000000000^81 ≤ 2038433821749659^81*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22023166585595707217 20000000000000000000 2038433821749659 2000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2038433821749659/2000000000000000 : ℝ)) (X := (22023166585595707217/20000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12023166585595707217/10000000000000000000 : ℝ) ≤ (10370655205315963/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (12023166585595707217/10000000000000000000 : ℝ)^16 ≤ (10370655205315963/10000000000000000 : ℝ)^81 := by
      have hnat : (12023166585595707217 : ℕ)^16*10000000000000000^81 ≤ 10370655205315963^81*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12023166585595707217 10000000000000000000 10370655205315963 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10370655205315963/10000000000000000 : ℝ)) (X := (12023166585595707217/10000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(12811273916553/424000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(14873841380639/530000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (159/250 : ℝ)) (alpha := (12811273916553/424000000000000 : ℝ)) (beta := (14873841380639/530000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (159/250 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(12811273916553/424000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(14873841380639/530000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4589443017/10000000000 : ℝ)*X 0 0+(1797239581/5000000000 : ℝ)*X 0 1+(-4160309507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((527081237/1250000000 : ℝ)*X 1 0+(-1627080181/5000000000 : ℝ)*X 1 1+(-4849887217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((784465211/2000000000 : ℝ)*X 2 0+(4855145459/10000000000 : ℝ)*X 2 1+(1777785487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2985381789/10000000000 : ℝ)*X 0 0+(2904850807/5000000000 : ℝ)*X 0 1+(-3433712861/10000000000 : ℝ)*X 0 2+(2985381789/10000000000 : ℝ)*X 1 0+(2904850807/5000000000 : ℝ)*X 1 1+(-3433712861/10000000000 : ℝ)*X 1 2+(2985381789/10000000000 : ℝ)*X 2 0+(2904850807/5000000000 : ℝ)*X 2 1+(-3433712861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321018_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-26316/3125 : ℝ) < ((-11897/6250 : ℝ)*P 0+(-11897/6250 : ℝ)*P 1+(-11897/6250 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-26316/3125 : ℝ) < (-8645289444344766430193895186977523/1045468460000000000000000000000000 : ℝ) := by norm_num
    linear_combination (505709/1000000000000 : ℝ)*(base11) + (56279/1000000000000 : ℝ)*(base18) + (207809460749/1000000000000 : ℝ)*(base39) + (208947/500000000000 : ℝ)*(base43) + (8360283531/125000000000 : ℝ)*(base49) + (501793761711/1000000000000 : ℝ)*(base50) + (256801/1000000000000 : ℝ)*(base53) + (385175548621/1000000000000 : ℝ)*(base60) + (11897/6250 : ℝ)*(major_s1_0) + (951759791053/500000000000 : ℝ)*(major_s1_1) + (1903519743199/1000000000000 : ℝ)*(major_s1_2) + (275643123087/100000000000 : ℝ)*(sp_s1_0) + (1378216049097/500000000000 : ℝ)*(sp_s1_1) + (2756431993379/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2756432411273/1000000000000 : ℝ)*(f.sum) + (375023935464691581/528728000000000000000000000000 : ℝ)*base62 + (419376049295839/530000000000000000000000000 : ℝ)*base64 + (178724043319631/155875000000000000000000000 : ℝ)*base67 + (258589559010647/424000000000000000000000000 : ℝ)*base68 + (4900438225530611143/12156610000000000000000000000000 : ℝ)*base70 + (43780072464913/114685000000000000000000000 : ℝ)*base73 + (1212470192644481/2494000000000000000000000000 : ℝ)*base74 + (43099381602543/229370000000000000000000000 : ℝ)*base77 + (789580241872456197/3575304875000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p021_b007 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 17 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=17 ∨ c=18 := by omega
  rcases hc with rfl|rfl
  · exact collision_c321017 p hpa (by linarith only [hpb]) X hX
  · exact collision_c321018 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 17 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p021_b007 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

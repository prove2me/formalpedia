-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_positive63
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:22:08.357588+00:00
-- url     : https://prove2.me/submissions/5a552de8-3a50-48bc-a525-14ab19da10b7

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
namespace HlawkaSchatten.DiagonalCutoff4
theorem positive_chart_nonnegative {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true)) :
    ∀ i h, 0 ≤ pair X i h := by
  intro i h
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hh.1.trans hh.2.1).trans hh.2.2
  · exact hh.1.trans hh.2.1
  · exact hh.1
theorem positive_chart_tailratio {p k A d rho : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true))
    (hm : ∀ i, orders i 0=i)
    (hbig : ∀ i, pair X i (orders i 1) ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i := by
  intro i h hih
  rw [abs_of_nonneg (positive_chart_nonnegative hX i h)]
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hih (hm i).symm).elim
  · exact hbig i
  · exact hh.2.1.trans (hbig i)
end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c328063_s0_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-38408089/2000000000 : ℝ)*x 0 + (5444040647/10000000000 : ℝ)*x 1 + (1435701761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38408089/2000000000 : ℝ)^93 ≤ (422342793327/50000000000000 : ℝ)^77 := by
    have hnat : (38408089 : ℕ)^93*50000000000000^77 ≤ 422342793327^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38408089 2000000000 422342793327 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444040647/10000000000 : ℝ)^93 ≤ (23989316795889/50000000000000 : ℝ)^77 := by
    have hnat : (5444040647 : ℕ)^93*50000000000000^77 ≤ 23989316795889^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444040647 10000000000 23989316795889 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1435701761/2500000000 : ℝ)^93 ≤ (51176680806371/100000000000000 : ℝ)^77 := by
    have hnat : (1435701761 : ℕ)^93*100000000000000^77 ≤ 51176680806371^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435701761 2500000000 51176680806371 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38408089/2000000000 : ℝ), (5444040647/10000000000 : ℝ), (1435701761/2500000000 : ℝ)] ![(422342793327/50000000000000 : ℝ), (23989316795889/50000000000000 : ℝ), (51176680806371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38408089/2000000000 : ℝ)|^93 ≤ (422342793327/50000000000000 : ℝ)^77
        have hw : |(-38408089/2000000000 : ℝ)|=(38408089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444040647/10000000000 : ℝ)|^93 ≤ (23989316795889/50000000000000 : ℝ)^77
        have hw : |(5444040647/10000000000 : ℝ)|=(5444040647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1435701761/2500000000 : ℝ)|^93 ≤ (51176680806371/100000000000000 : ℝ)^77
        have hw : |(1435701761/2500000000 : ℝ)|=(1435701761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1483249797/10000000000 : ℝ)*x 0 + (1188211747/10000000000 : ℝ)*x 1 + (1703649263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1483249797/10000000000 : ℝ)^93 ≤ (77945153567/781250000000 : ℝ)^77 := by
    have hnat : (1483249797 : ℕ)^93*781250000000^77 ≤ 77945153567^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483249797 10000000000 77945153567 781250000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1188211747/10000000000 : ℝ)^93 ≤ (7632450397217/100000000000000 : ℝ)^77 := by
    have hnat : (1188211747 : ℕ)^93*100000000000000^77 ≤ 7632450397217^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188211747 10000000000 7632450397217 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1703649263/2000000000 : ℝ)^93 ≤ (82390569936473/100000000000000 : ℝ)^77 := by
    have hnat : (1703649263 : ℕ)^93*100000000000000^77 ≤ 82390569936473^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703649263 2000000000 82390569936473 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1483249797/10000000000 : ℝ), (1188211747/10000000000 : ℝ), (1703649263/2000000000 : ℝ)] ![(77945153567/781250000000 : ℝ), (7632450397217/100000000000000 : ℝ), (82390569936473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1483249797/10000000000 : ℝ)|^93 ≤ (77945153567/781250000000 : ℝ)^77
        have hw : |(-1483249797/10000000000 : ℝ)|=(1483249797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1188211747/10000000000 : ℝ)|^93 ≤ (7632450397217/100000000000000 : ℝ)^77
        have hw : |(1188211747/10000000000 : ℝ)|=(1188211747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1703649263/2000000000 : ℝ)|^93 ≤ (82390569936473/100000000000000 : ℝ)^77
        have hw : |(1703649263/2000000000 : ℝ)|=(1703649263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2355503631/10000000000 : ℝ)*x 0 + (-25086217/5000000000 : ℝ)*x 1 + (2129561617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2355503631/10000000000 : ℝ)^93 ≤ (17442457761471/100000000000000 : ℝ)^77 := by
    have hnat : (2355503631 : ℕ)^93*100000000000000^77 ≤ 17442457761471^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355503631 10000000000 17442457761471 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25086217/5000000000 : ℝ)^93 ≤ (166970501347/100000000000000 : ℝ)^77 := by
    have hnat : (25086217 : ℕ)^93*100000000000000^77 ≤ 166970501347^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25086217 5000000000 166970501347 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129561617/2500000000 : ℝ)^93 ≤ (82390571723829/100000000000000 : ℝ)^77 := by
    have hnat : (2129561617 : ℕ)^93*100000000000000^77 ≤ 82390571723829^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129561617 2500000000 82390571723829 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2355503631/10000000000 : ℝ), (-25086217/5000000000 : ℝ), (2129561617/2500000000 : ℝ)] ![(17442457761471/100000000000000 : ℝ), (166970501347/100000000000000 : ℝ), (82390571723829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2355503631/10000000000 : ℝ)|^93 ≤ (17442457761471/100000000000000 : ℝ)^77
        have hw : |(2355503631/10000000000 : ℝ)|=(2355503631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25086217/5000000000 : ℝ)|^93 ≤ (166970501347/100000000000000 : ℝ)^77
        have hw : |(-25086217/5000000000 : ℝ)|=(25086217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2129561617/2500000000 : ℝ)|^93 ≤ (82390571723829/100000000000000 : ℝ)^77
        have hw : |(2129561617/2500000000 : ℝ)|=(2129561617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (47110029/200000000 : ℝ)*x 0 + (8518248173/10000000000 : ℝ)*x 1 + (-12543083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47110029/200000000 : ℝ)^93 ≤ (1090152390957/6250000000000 : ℝ)^77 := by
    have hnat : (47110029 : ℕ)^93*6250000000000^77 ≤ 1090152390957^77*200000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47110029 200000000 1090152390957 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8518248173/10000000000 : ℝ)^93 ≤ (41195295820873/50000000000000 : ℝ)^77 := by
    have hnat : (8518248173 : ℕ)^93*50000000000000^77 ≤ 41195295820873^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8518248173 10000000000 41195295820873 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12543083/2500000000 : ℝ)^93 ≤ (166970091363/100000000000000 : ℝ)^77 := by
    have hnat : (12543083 : ℕ)^93*100000000000000^77 ≤ 166970091363^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12543083 2500000000 166970091363 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(47110029/200000000 : ℝ), (8518248173/10000000000 : ℝ), (-12543083/2500000000 : ℝ)] ![(1090152390957/6250000000000 : ℝ), (41195295820873/50000000000000 : ℝ), (166970091363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(47110029/200000000 : ℝ)|^93 ≤ (1090152390957/6250000000000 : ℝ)^77
        have hw : |(47110029/200000000 : ℝ)|=(47110029/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8518248173/10000000000 : ℝ)|^93 ≤ (41195295820873/50000000000000 : ℝ)^77
        have hw : |(8518248173/10000000000 : ℝ)|=(8518248173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12543083/2500000000 : ℝ)|^93 ≤ (166970091363/100000000000000 : ℝ)^77
        have hw : |(-12543083/2500000000 : ℝ)|=(12543083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1566825153/5000000000 : ℝ)*x 0 + (7171827243/10000000000 : ℝ)*x 1 + (646067129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1566825153/5000000000 : ℝ)^93 ≤ (12311295683471/50000000000000 : ℝ)^77 := by
    have hnat : (1566825153 : ℕ)^93*50000000000000^77 ≤ 12311295683471^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566825153 5000000000 12311295683471 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7171827243/10000000000 : ℝ)^93 ≤ (13386308106809/20000000000000 : ℝ)^77 := by
    have hnat : (7171827243 : ℕ)^93*20000000000000^77 ≤ 13386308106809^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7171827243 10000000000 13386308106809 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646067129/5000000000 : ℝ)^93 ≤ (4222934039433/50000000000000 : ℝ)^77 := by
    have hnat : (646067129 : ℕ)^93*50000000000000^77 ≤ 4222934039433^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646067129 5000000000 4222934039433 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1566825153/5000000000 : ℝ), (7171827243/10000000000 : ℝ), (646067129/5000000000 : ℝ)] ![(12311295683471/50000000000000 : ℝ), (13386308106809/20000000000000 : ℝ), (4222934039433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1566825153/5000000000 : ℝ)|^93 ≤ (12311295683471/50000000000000 : ℝ)^77
        have hw : |(1566825153/5000000000 : ℝ)|=(1566825153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7171827243/10000000000 : ℝ)|^93 ≤ (13386308106809/20000000000000 : ℝ)^77
        have hw : |(7171827243/10000000000 : ℝ)|=(7171827243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646067129/5000000000 : ℝ)|^93 ≤ (4222934039433/50000000000000 : ℝ)^77
        have hw : |(646067129/5000000000 : ℝ)|=(646067129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5060157/2500000000 : ℝ)*x 0 + (572745351/2500000000 : ℝ)*x 1 + (4288489263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5060157/2500000000 : ℝ)^93 ≤ (27889987627/50000000000000 : ℝ)^77 := by
    have hnat : (5060157 : ℕ)^93*50000000000000^77 ≤ 27889987627^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060157 2500000000 27889987627 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572745351/2500000000 : ℝ)^93 ≤ (1686704609781/10000000000000 : ℝ)^77 := by
    have hnat : (572745351 : ℕ)^93*10000000000000^77 ≤ 1686704609781^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572745351 2500000000 1686704609781 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4288489263/5000000000 : ℝ)^93 ≤ (16615434783779/20000000000000 : ℝ)^77 := by
    have hnat : (4288489263 : ℕ)^93*20000000000000^77 ≤ 16615434783779^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288489263 5000000000 16615434783779 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5060157/2500000000 : ℝ), (572745351/2500000000 : ℝ), (4288489263/5000000000 : ℝ)] ![(27889987627/50000000000000 : ℝ), (1686704609781/10000000000000 : ℝ), (16615434783779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5060157/2500000000 : ℝ)|^93 ≤ (27889987627/50000000000000 : ℝ)^77
        have hw : |(-5060157/2500000000 : ℝ)|=(5060157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(572745351/2500000000 : ℝ)|^93 ≤ (1686704609781/10000000000000 : ℝ)^77
        have hw : |(572745351/2500000000 : ℝ)|=(572745351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4288489263/5000000000 : ℝ)|^93 ≤ (16615434783779/20000000000000 : ℝ)^77
        have hw : |(4288489263/5000000000 : ℝ)|=(4288489263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (538305507/5000000000 : ℝ)*x 0 + (-300842891/2000000000 : ℝ)*x 1 + (857697707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538305507/5000000000 : ℝ)^93 ≤ (6775294593459/100000000000000 : ℝ)^77 := by
    have hnat : (538305507 : ℕ)^93*100000000000000^77 ≤ 6775294593459^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538305507 5000000000 6775294593459 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300842891/2000000000 : ℝ)^93 ≤ (10147548507779/100000000000000 : ℝ)^77 := by
    have hnat : (300842891 : ℕ)^93*100000000000000^77 ≤ 10147548507779^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300842891 2000000000 10147548507779 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857697707/1000000000 : ℝ)^93 ≤ (83077156885509/100000000000000 : ℝ)^77 := by
    have hnat : (857697707 : ℕ)^93*100000000000000^77 ≤ 83077156885509^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857697707 1000000000 83077156885509 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538305507/5000000000 : ℝ), (-300842891/2000000000 : ℝ), (857697707/1000000000 : ℝ)] ![(6775294593459/100000000000000 : ℝ), (10147548507779/100000000000000 : ℝ), (83077156885509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538305507/5000000000 : ℝ)|^93 ≤ (6775294593459/100000000000000 : ℝ)^77
        have hw : |(538305507/5000000000 : ℝ)|=(538305507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300842891/2000000000 : ℝ)|^93 ≤ (10147548507779/100000000000000 : ℝ)^77
        have hw : |(-300842891/2000000000 : ℝ)|=(300842891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(857697707/1000000000 : ℝ)|^93 ≤ (83077156885509/100000000000000 : ℝ)^77
        have hw : |(857697707/1000000000 : ℝ)|=(857697707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8212420461/10000000000 : ℝ)*x 0 + (340924099/1250000000 : ℝ)*x 1 + (-92093617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8212420461/10000000000 : ℝ)^93 ≤ (78831348052159/100000000000000 : ℝ)^77 := by
    have hnat : (8212420461 : ℕ)^93*100000000000000^77 ≤ 78831348052159^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8212420461 10000000000 78831348052159 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340924099/1250000000 : ℝ)^93 ≤ (20820945857501/100000000000000 : ℝ)^77 := by
    have hnat : (340924099 : ℕ)^93*100000000000000^77 ≤ 20820945857501^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340924099 1250000000 20820945857501 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92093617/10000000000 : ℝ)^93 ≤ (347706084037/100000000000000 : ℝ)^77 := by
    have hnat : (92093617 : ℕ)^93*100000000000000^77 ≤ 347706084037^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92093617 10000000000 347706084037 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8212420461/10000000000 : ℝ), (340924099/1250000000 : ℝ), (-92093617/10000000000 : ℝ)] ![(78831348052159/100000000000000 : ℝ), (20820945857501/100000000000000 : ℝ), (347706084037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8212420461/10000000000 : ℝ)|^93 ≤ (78831348052159/100000000000000 : ℝ)^77
        have hw : |(8212420461/10000000000 : ℝ)|=(8212420461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340924099/1250000000 : ℝ)|^93 ≤ (20820945857501/100000000000000 : ℝ)^77
        have hw : |(340924099/1250000000 : ℝ)|=(340924099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92093617/10000000000 : ℝ)|^93 ≤ (347706084037/100000000000000 : ℝ)^77
        have hw : |(-92093617/10000000000 : ℝ)|=(92093617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (748774533/1000000000 : ℝ)*x 0 + (42859039/156250000 : ℝ)*x 1 + (260471621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (748774533/1000000000 : ℝ)^93 ≤ (14101723370211/20000000000000 : ℝ)^77 := by
    have hnat : (748774533 : ℕ)^93*20000000000000^77 ≤ 14101723370211^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748774533 1000000000 14101723370211 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42859039/156250000 : ℝ)^93 ≤ (327573998357/1562500000000 : ℝ)^77 := by
    have hnat : (42859039 : ℕ)^93*1562500000000^77 ≤ 327573998357^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42859039 156250000 327573998357 1562500000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260471621/2000000000 : ℝ)^93 ≤ (8526647241413/100000000000000 : ℝ)^77 := by
    have hnat : (260471621 : ℕ)^93*100000000000000^77 ≤ 8526647241413^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260471621 2000000000 8526647241413 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(748774533/1000000000 : ℝ), (42859039/156250000 : ℝ), (260471621/2000000000 : ℝ)] ![(14101723370211/20000000000000 : ℝ), (327573998357/1562500000000 : ℝ), (8526647241413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(748774533/1000000000 : ℝ)|^93 ≤ (14101723370211/20000000000000 : ℝ)^77
        have hw : |(748774533/1000000000 : ℝ)|=(748774533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42859039/156250000 : ℝ)|^93 ≤ (327573998357/1562500000000 : ℝ)^77
        have hw : |(42859039/156250000 : ℝ)|=(42859039/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260471621/2000000000 : ℝ)|^93 ≤ (8526647241413/100000000000000 : ℝ)^77
        have hw : |(260471621/2000000000 : ℝ)|=(260471621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-132639663/10000000000 : ℝ)*x 0 + (7273185617/10000000000 : ℝ)*x 1 + (478858149/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132639663/10000000000 : ℝ)^93 ≤ (540231088611/100000000000000 : ℝ)^77 := by
    have hnat : (132639663 : ℕ)^93*100000000000000^77 ≤ 540231088611^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132639663 10000000000 540231088611 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7273185617/10000000000 : ℝ)^93 ≤ (68075703077509/100000000000000 : ℝ)^77 := by
    have hnat : (7273185617 : ℕ)^93*100000000000000^77 ≤ 68075703077509^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7273185617 10000000000 68075703077509 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478858149/1250000000 : ℝ)^93 ≤ (15692032910383/50000000000000 : ℝ)^77 := by
    have hnat : (478858149 : ℕ)^93*50000000000000^77 ≤ 15692032910383^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478858149 1250000000 15692032910383 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132639663/10000000000 : ℝ), (7273185617/10000000000 : ℝ), (478858149/1250000000 : ℝ)] ![(540231088611/100000000000000 : ℝ), (68075703077509/100000000000000 : ℝ), (15692032910383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132639663/10000000000 : ℝ)|^93 ≤ (540231088611/100000000000000 : ℝ)^77
        have hw : |(-132639663/10000000000 : ℝ)|=(132639663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7273185617/10000000000 : ℝ)|^93 ≤ (68075703077509/100000000000000 : ℝ)^77
        have hw : |(7273185617/10000000000 : ℝ)|=(7273185617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478858149/1250000000 : ℝ)|^93 ≤ (15692032910383/50000000000000 : ℝ)^77
        have hw : |(478858149/1250000000 : ℝ)|=(478858149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8161105099/10000000000 : ℝ)*x 0 + (-7390343/5000000000 : ℝ)*x 1 + (282508733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8161105099/10000000000 : ℝ)^93 ≤ (39118401412657/50000000000000 : ℝ)^77 := by
    have hnat : (8161105099 : ℕ)^93*50000000000000^77 ≤ 39118401412657^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8161105099 10000000000 39118401412657 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7390343/5000000000 : ℝ)^93 ≤ (19078717861/50000000000000 : ℝ)^77 := by
    have hnat : (7390343 : ℕ)^93*50000000000000^77 ≤ 19078717861^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7390343 5000000000 19078717861 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282508733/1000000000 : ℝ)^93 ≤ (2172503972341/10000000000000 : ℝ)^77 := by
    have hnat : (282508733 : ℕ)^93*10000000000000^77 ≤ 2172503972341^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282508733 1000000000 2172503972341 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8161105099/10000000000 : ℝ), (-7390343/5000000000 : ℝ), (282508733/1000000000 : ℝ)] ![(39118401412657/50000000000000 : ℝ), (19078717861/50000000000000 : ℝ), (2172503972341/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8161105099/10000000000 : ℝ)|^93 ≤ (39118401412657/50000000000000 : ℝ)^77
        have hw : |(8161105099/10000000000 : ℝ)|=(8161105099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7390343/5000000000 : ℝ)|^93 ≤ (19078717861/50000000000000 : ℝ)^77
        have hw : |(-7390343/5000000000 : ℝ)|=(7390343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282508733/1000000000 : ℝ)|^93 ≤ (2172503972341/10000000000000 : ℝ)^77
        have hw : |(282508733/1000000000 : ℝ)|=(282508733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (105016193/1250000000 : ℝ)*x 0 + (4359305967/5000000000 : ℝ)*x 1 + (-378935791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105016193/1250000000 : ℝ)^93 ≤ (1004300750059/20000000000000 : ℝ)^77 := by
    have hnat : (105016193 : ℕ)^93*20000000000000^77 ≤ 1004300750059^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105016193 1250000000 1004300750059 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4359305967/5000000000 : ℝ)^93 ≤ (10592117346069/12500000000000 : ℝ)^77 := by
    have hnat : (4359305967 : ℕ)^93*12500000000000^77 ≤ 10592117346069^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359305967 5000000000 10592117346069 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378935791/2500000000 : ℝ)^93 ≤ (2560389367999/25000000000000 : ℝ)^77 := by
    have hnat : (378935791 : ℕ)^93*25000000000000^77 ≤ 2560389367999^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378935791 2500000000 2560389367999 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105016193/1250000000 : ℝ), (4359305967/5000000000 : ℝ), (-378935791/2500000000 : ℝ)] ![(1004300750059/20000000000000 : ℝ), (10592117346069/12500000000000 : ℝ), (2560389367999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105016193/1250000000 : ℝ)|^93 ≤ (1004300750059/20000000000000 : ℝ)^77
        have hw : |(105016193/1250000000 : ℝ)|=(105016193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4359305967/5000000000 : ℝ)|^93 ≤ (10592117346069/12500000000000 : ℝ)^77
        have hw : |(4359305967/5000000000 : ℝ)|=(4359305967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378935791/2500000000 : ℝ)|^93 ≤ (2560389367999/25000000000000 : ℝ)^77
        have hw : |(-378935791/2500000000 : ℝ)|=(378935791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s0_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1898956749/2500000000 : ℝ)*x 0 + (291909411/1250000000 : ℝ)*x 1 + (160793623/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898956749/2500000000 : ℝ)^93 ≤ (8967461207309/12500000000000 : ℝ)^77 := by
    have hnat : (1898956749 : ℕ)^93*12500000000000^77 ≤ 8967461207309^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898956749 2500000000 8967461207309 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291909411/1250000000 : ℝ)^93 ≤ (17261703773093/100000000000000 : ℝ)^77 := by
    have hnat : (291909411 : ℕ)^93*100000000000000^77 ≤ 17261703773093^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291909411 1250000000 17261703773093 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160793623/1000000000 : ℝ)^93 ≤ (439944262297/4000000000000 : ℝ)^77 := by
    have hnat : (160793623 : ℕ)^93*4000000000000^77 ≤ 439944262297^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160793623 1000000000 439944262297 4000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1898956749/2500000000 : ℝ), (291909411/1250000000 : ℝ), (160793623/1000000000 : ℝ)] ![(8967461207309/12500000000000 : ℝ), (17261703773093/100000000000000 : ℝ), (439944262297/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1898956749/2500000000 : ℝ)|^93 ≤ (8967461207309/12500000000000 : ℝ)^77
        have hw : |(1898956749/2500000000 : ℝ)|=(1898956749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(291909411/1250000000 : ℝ)|^93 ≤ (17261703773093/100000000000000 : ℝ)^77
        have hw : |(291909411/1250000000 : ℝ)|=(291909411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160793623/1000000000 : ℝ)|^93 ≤ (439944262297/4000000000000 : ℝ)^77
        have hw : |(160793623/1000000000 : ℝ)|=(160793623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-980855679/10000000000 : ℝ)*x 0 + (533633159/1000000000 : ℝ)*x 1 + (670301687/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980855679/10000000000 : ℝ)^93 ≤ (6054363757017/100000000000000 : ℝ)^77 := by
    have hnat : (980855679 : ℕ)^93*100000000000000^77 ≤ 6054363757017^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980855679 10000000000 6054363757017 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533633159/1000000000 : ℝ)^93 ≤ (46834510870121/100000000000000 : ℝ)^77 := by
    have hnat : (533633159 : ℕ)^93*100000000000000^77 ≤ 46834510870121^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533633159 1000000000 46834510870121 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (670301687/1250000000 : ℝ)^93 ≤ (736111333751/1562500000000 : ℝ)^77 := by
    have hnat : (670301687 : ℕ)^93*1562500000000^77 ≤ 736111333751^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670301687 1250000000 736111333751 1562500000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-980855679/10000000000 : ℝ), (533633159/1000000000 : ℝ), (670301687/1250000000 : ℝ)] ![(6054363757017/100000000000000 : ℝ), (46834510870121/100000000000000 : ℝ), (736111333751/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-980855679/10000000000 : ℝ)|^93 ≤ (6054363757017/100000000000000 : ℝ)^77
        have hw : |(-980855679/10000000000 : ℝ)|=(980855679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(533633159/1000000000 : ℝ)|^93 ≤ (46834510870121/100000000000000 : ℝ)^77
        have hw : |(533633159/1000000000 : ℝ)|=(533633159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(670301687/1250000000 : ℝ)|^93 ≤ (736111333751/1562500000000 : ℝ)^77
        have hw : |(670301687/1250000000 : ℝ)|=(670301687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5336215961/10000000000 : ℝ)*x 0 + (-979695833/10000000000 : ℝ)*x 1 + (5363343783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5336215961/10000000000 : ℝ)^93 ≤ (46833285178559/100000000000000 : ℝ)^77 := by
    have hnat : (5336215961 : ℕ)^93*100000000000000^77 ≤ 46833285178559^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336215961 10000000000 46833285178559 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979695833/10000000000 : ℝ)^93 ≤ (302285900447/5000000000000 : ℝ)^77 := by
    have hnat : (979695833 : ℕ)^93*5000000000000^77 ≤ 302285900447^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979695833 10000000000 302285900447 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5363343783/10000000000 : ℝ)^93 ≤ (11780249198151/25000000000000 : ℝ)^77 := by
    have hnat : (5363343783 : ℕ)^93*25000000000000^77 ≤ 11780249198151^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363343783 10000000000 11780249198151 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5336215961/10000000000 : ℝ), (-979695833/10000000000 : ℝ), (5363343783/10000000000 : ℝ)] ![(46833285178559/100000000000000 : ℝ), (302285900447/5000000000000 : ℝ), (11780249198151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5336215961/10000000000 : ℝ)|^93 ≤ (46833285178559/100000000000000 : ℝ)^77
        have hw : |(5336215961/10000000000 : ℝ)|=(5336215961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-979695833/10000000000 : ℝ)|^93 ≤ (302285900447/5000000000000 : ℝ)^77
        have hw : |(-979695833/10000000000 : ℝ)|=(979695833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5363343783/10000000000 : ℝ)|^93 ≤ (11780249198151/25000000000000 : ℝ)^77
        have hw : |(5363343783/10000000000 : ℝ)|=(5363343783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5354086727/10000000000 : ℝ)*x 0 + (5359476163/10000000000 : ℝ)*x 1 + (-239933611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354086727/10000000000 : ℝ)^93 ≤ (47022784459957/100000000000000 : ℝ)^77 := by
    have hnat : (5354086727 : ℕ)^93*100000000000000^77 ≤ 47022784459957^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354086727 10000000000 47022784459957 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5359476163/10000000000 : ℝ)^93 ≤ (47079959159097/100000000000000 : ℝ)^77 := by
    have hnat : (5359476163 : ℕ)^93*100000000000000^77 ≤ 47079959159097^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359476163 10000000000 47079959159097 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239933611/2500000000 : ℝ)^93 ≤ (5897256361607/100000000000000 : ℝ)^77 := by
    have hnat : (239933611 : ℕ)^93*100000000000000^77 ≤ 5897256361607^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239933611 2500000000 5897256361607 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354086727/10000000000 : ℝ), (5359476163/10000000000 : ℝ), (-239933611/2500000000 : ℝ)] ![(47022784459957/100000000000000 : ℝ), (47079959159097/100000000000000 : ℝ), (5897256361607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354086727/10000000000 : ℝ)|^93 ≤ (47022784459957/100000000000000 : ℝ)^77
        have hw : |(5354086727/10000000000 : ℝ)|=(5354086727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5359476163/10000000000 : ℝ)|^93 ≤ (47079959159097/100000000000000 : ℝ)^77
        have hw : |(5359476163/10000000000 : ℝ)|=(5359476163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239933611/2500000000 : ℝ)|^93 ≤ (5897256361607/100000000000000 : ℝ)^77
        have hw : |(-239933611/2500000000 : ℝ)|=(239933611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (809563573/2000000000 : ℝ)*x 0 + (1008292093/2500000000 : ℝ)*x 1 + (1999747533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (809563573/2000000000 : ℝ)^93 ≤ (3354320369563/10000000000000 : ℝ)^77 := by
    have hnat : (809563573 : ℕ)^93*10000000000000^77 ≤ 3354320369563^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809563573 2000000000 3354320369563 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008292093/2500000000 : ℝ)^93 ≤ (33396637131209/100000000000000 : ℝ)^77 := by
    have hnat : (1008292093 : ℕ)^93*100000000000000^77 ≤ 33396637131209^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008292093 2500000000 33396637131209 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999747533/5000000000 : ℝ)^93 ≤ (16530079577329/50000000000000 : ℝ)^77 := by
    have hnat : (1999747533 : ℕ)^93*50000000000000^77 ≤ 16530079577329^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999747533 5000000000 16530079577329 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(809563573/2000000000 : ℝ), (1008292093/2500000000 : ℝ), (1999747533/5000000000 : ℝ)] ![(3354320369563/10000000000000 : ℝ), (33396637131209/100000000000000 : ℝ), (16530079577329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(809563573/2000000000 : ℝ)|^93 ≤ (3354320369563/10000000000000 : ℝ)^77
        have hw : |(809563573/2000000000 : ℝ)|=(809563573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008292093/2500000000 : ℝ)|^93 ≤ (33396637131209/100000000000000 : ℝ)^77
        have hw : |(1008292093/2500000000 : ℝ)|=(1008292093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1999747533/5000000000 : ℝ)|^93 ≤ (16530079577329/50000000000000 : ℝ)^77
        have hw : |(1999747533/5000000000 : ℝ)|=(1999747533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-869643037/10000000000 : ℝ)*x 0 + (46350717/100000000 : ℝ)*x 1 + (3059758267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869643037/10000000000 : ℝ)^93 ≤ (5235333517767/100000000000000 : ℝ)^77 := by
    have hnat : (869643037 : ℕ)^93*100000000000000^77 ≤ 5235333517767^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869643037 10000000000 5235333517767 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46350717/100000000 : ℝ)^93 ≤ (39506230243587/100000000000000 : ℝ)^77 := by
    have hnat : (46350717 : ℕ)^93*100000000000000^77 ≤ 39506230243587^77*100000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46350717 100000000 39506230243587 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3059758267/5000000000 : ℝ)^93 ≤ (27629218107467/50000000000000 : ℝ)^77 := by
    have hnat : (3059758267 : ℕ)^93*50000000000000^77 ≤ 27629218107467^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059758267 5000000000 27629218107467 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-869643037/10000000000 : ℝ), (46350717/100000000 : ℝ), (3059758267/5000000000 : ℝ)] ![(5235333517767/100000000000000 : ℝ), (39506230243587/100000000000000 : ℝ), (27629218107467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-869643037/10000000000 : ℝ)|^93 ≤ (5235333517767/100000000000000 : ℝ)^77
        have hw : |(-869643037/10000000000 : ℝ)|=(869643037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46350717/100000000 : ℝ)|^93 ≤ (39506230243587/100000000000000 : ℝ)^77
        have hw : |(46350717/100000000 : ℝ)|=(46350717/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3059758267/5000000000 : ℝ)|^93 ≤ (27629218107467/50000000000000 : ℝ)^77
        have hw : |(3059758267/5000000000 : ℝ)|=(3059758267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50028193/100000000 : ℝ)*x 0 + (-36663287/1250000000 : ℝ)*x 1 + (3060227557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50028193/100000000 : ℝ)^93 ≤ (270765929803/625000000000 : ℝ)^77 := by
    have hnat : (50028193 : ℕ)^93*625000000000^77 ≤ 270765929803^77*100000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50028193 100000000 270765929803 625000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36663287/1250000000 : ℝ)^93 ≤ (1408778491191/100000000000000 : ℝ)^77 := by
    have hnat : (36663287 : ℕ)^93*100000000000000^77 ≤ 1408778491191^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36663287 1250000000 1408778491191 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3060227557/5000000000 : ℝ)^93 ≤ (11053734544997/20000000000000 : ℝ)^77 := by
    have hnat : (3060227557 : ℕ)^93*20000000000000^77 ≤ 11053734544997^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3060227557 5000000000 11053734544997 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50028193/100000000 : ℝ), (-36663287/1250000000 : ℝ), (3060227557/5000000000 : ℝ)] ![(270765929803/625000000000 : ℝ), (1408778491191/100000000000000 : ℝ), (11053734544997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50028193/100000000 : ℝ)|^93 ≤ (270765929803/625000000000 : ℝ)^77
        have hw : |(50028193/100000000 : ℝ)|=(50028193/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36663287/1250000000 : ℝ)|^93 ≤ (1408778491191/100000000000000 : ℝ)^77
        have hw : |(-36663287/1250000000 : ℝ)|=(36663287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3060227557/5000000000 : ℝ)|^93 ≤ (11053734544997/20000000000000 : ℝ)^77
        have hw : |(3060227557/5000000000 : ℝ)|=(3060227557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (190408281/400000000 : ℝ)*x 0 + (3183457639/5000000000 : ℝ)*x 1 + (-262867197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190408281/400000000 : ℝ)^93 ≤ (20399006061743/50000000000000 : ℝ)^77 := by
    have hnat : (190408281 : ℕ)^93*50000000000000^77 ≤ 20399006061743^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190408281 400000000 20399006061743 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3183457639/5000000000 : ℝ)^93 ≤ (57967832219381/100000000000000 : ℝ)^77 := by
    have hnat : (3183457639 : ℕ)^93*100000000000000^77 ≤ 57967832219381^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183457639 5000000000 57967832219381 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262867197/10000000000 : ℝ)^93 ≤ (1234155635491/100000000000000 : ℝ)^77 := by
    have hnat : (262867197 : ℕ)^93*100000000000000^77 ≤ 1234155635491^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262867197 10000000000 1234155635491 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(190408281/400000000 : ℝ), (3183457639/5000000000 : ℝ), (-262867197/10000000000 : ℝ)] ![(20399006061743/50000000000000 : ℝ), (57967832219381/100000000000000 : ℝ), (1234155635491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(190408281/400000000 : ℝ)|^93 ≤ (20399006061743/50000000000000 : ℝ)^77
        have hw : |(190408281/400000000 : ℝ)|=(190408281/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3183457639/5000000000 : ℝ)|^93 ≤ (57967832219381/100000000000000 : ℝ)^77
        have hw : |(3183457639/5000000000 : ℝ)|=(3183457639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262867197/10000000000 : ℝ)|^93 ≤ (1234155635491/100000000000000 : ℝ)^77
        have hw : |(-262867197/10000000000 : ℝ)|=(262867197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4515657849/10000000000 : ℝ)*x 0 + (5674372849/10000000000 : ℝ)*x 1 + (1641768947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4515657849/10000000000 : ℝ)^93 ≤ (9570062120119/25000000000000 : ℝ)^77 := by
    have hnat : (4515657849 : ℕ)^93*25000000000000^77 ≤ 9570062120119^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515657849 10000000000 9570062120119 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5674372849/10000000000 : ℝ)^93 ≤ (50441026892089/100000000000000 : ℝ)^77 := by
    have hnat : (5674372849 : ℕ)^93*100000000000000^77 ≤ 50441026892089^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674372849 10000000000 50441026892089 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1641768947/10000000000 : ℝ)^93 ≤ (2255744922161/20000000000000 : ℝ)^77 := by
    have hnat : (1641768947 : ℕ)^93*20000000000000^77 ≤ 2255744922161^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641768947 10000000000 2255744922161 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4515657849/10000000000 : ℝ), (5674372849/10000000000 : ℝ), (1641768947/10000000000 : ℝ)] ![(9570062120119/25000000000000 : ℝ), (50441026892089/100000000000000 : ℝ), (2255744922161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4515657849/10000000000 : ℝ)|^93 ≤ (9570062120119/25000000000000 : ℝ)^77
        have hw : |(4515657849/10000000000 : ℝ)|=(4515657849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5674372849/10000000000 : ℝ)|^93 ≤ (50441026892089/100000000000000 : ℝ)^77
        have hw : |(5674372849/10000000000 : ℝ)|=(5674372849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1641768947/10000000000 : ℝ)|^93 ≤ (2255744922161/20000000000000 : ℝ)^77
        have hw : |(1641768947/10000000000 : ℝ)|=(1641768947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-296245563/10000000000 : ℝ)*x 0 + (2506427149/5000000000 : ℝ)*x 1 + (305463137/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (296245563/10000000000 : ℝ)^93 ≤ (1425847304693/100000000000000 : ℝ)^77 := by
    have hnat : (296245563 : ℕ)^93*100000000000000^77 ≤ 1425847304693^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296245563 10000000000 1425847304693 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2506427149/5000000000 : ℝ)^93 ≤ (43427526974501/100000000000000 : ℝ)^77 := by
    have hnat : (2506427149 : ℕ)^93*100000000000000^77 ≤ 43427526974501^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506427149 5000000000 43427526974501 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305463137/500000000 : ℝ)^93 ≤ (55146625700843/100000000000000 : ℝ)^77 := by
    have hnat : (305463137 : ℕ)^93*100000000000000^77 ≤ 55146625700843^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305463137 500000000 55146625700843 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-296245563/10000000000 : ℝ), (2506427149/5000000000 : ℝ), (305463137/500000000 : ℝ)] ![(1425847304693/100000000000000 : ℝ), (43427526974501/100000000000000 : ℝ), (55146625700843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-296245563/10000000000 : ℝ)|^93 ≤ (1425847304693/100000000000000 : ℝ)^77
        have hw : |(-296245563/10000000000 : ℝ)|=(296245563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2506427149/5000000000 : ℝ)|^93 ≤ (43427526974501/100000000000000 : ℝ)^77
        have hw : |(2506427149/5000000000 : ℝ)|=(2506427149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(305463137/500000000 : ℝ)|^93 ≤ (55146625700843/100000000000000 : ℝ)^77
        have hw : |(305463137/500000000 : ℝ)|=(305463137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (930760929/2000000000 : ℝ)*x 0 + (-857060091/10000000000 : ℝ)*x 1 + (6110201773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930760929/2000000000 : ℝ)^93 ≤ (3969915570353/10000000000000 : ℝ)^77 := by
    have hnat : (930760929 : ℕ)^93*10000000000000^77 ≤ 3969915570353^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930760929 2000000000 3969915570353 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (857060091/10000000000 : ℝ)^93 ≤ (2571990343147/50000000000000 : ℝ)^77 := by
    have hnat : (857060091 : ℕ)^93*50000000000000^77 ≤ 2571990343147^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857060091 10000000000 2571990343147 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6110201773/10000000000 : ℝ)^93 ≤ (55156863583657/100000000000000 : ℝ)^77 := by
    have hnat : (6110201773 : ℕ)^93*100000000000000^77 ≤ 55156863583657^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6110201773 10000000000 55156863583657 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(930760929/2000000000 : ℝ), (-857060091/10000000000 : ℝ), (6110201773/10000000000 : ℝ)] ![(3969915570353/10000000000000 : ℝ), (2571990343147/50000000000000 : ℝ), (55156863583657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(930760929/2000000000 : ℝ)|^93 ≤ (3969915570353/10000000000000 : ℝ)^77
        have hw : |(930760929/2000000000 : ℝ)|=(930760929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-857060091/10000000000 : ℝ)|^93 ≤ (2571990343147/50000000000000 : ℝ)^77
        have hw : |(-857060091/10000000000 : ℝ)|=(857060091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6110201773/10000000000 : ℝ)|^93 ≤ (55156863583657/100000000000000 : ℝ)^77
        have hw : |(6110201773/10000000000 : ℝ)|=(6110201773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6099053891/10000000000 : ℝ)*x 0 + (5036219483/10000000000 : ℝ)*x 1 + (-8535021/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6099053891/10000000000 : ℝ)^93 ≤ (27517672006439/50000000000000 : ℝ)^77 := by
    have hnat : (6099053891 : ℕ)^93*50000000000000^77 ≤ 27517672006439^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6099053891 10000000000 27517672006439 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5036219483/10000000000 : ℝ)^93 ≤ (21836062083831/50000000000000 : ℝ)^77 := by
    have hnat : (5036219483 : ℕ)^93*50000000000000^77 ≤ 21836062083831^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036219483 10000000000 21836062083831 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8535021/312500000 : ℝ)^93 ≤ (1292531799769/100000000000000 : ℝ)^77 := by
    have hnat : (8535021 : ℕ)^93*100000000000000^77 ≤ 1292531799769^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8535021 312500000 1292531799769 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6099053891/10000000000 : ℝ), (5036219483/10000000000 : ℝ), (-8535021/312500000 : ℝ)] ![(27517672006439/50000000000000 : ℝ), (21836062083831/50000000000000 : ℝ), (1292531799769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6099053891/10000000000 : ℝ)|^93 ≤ (27517672006439/50000000000000 : ℝ)^77
        have hw : |(6099053891/10000000000 : ℝ)|=(6099053891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5036219483/10000000000 : ℝ)|^93 ≤ (21836062083831/50000000000000 : ℝ)^77
        have hw : |(5036219483/10000000000 : ℝ)|=(5036219483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8535021/312500000 : ℝ)|^93 ≤ (1292531799769/100000000000000 : ℝ)^77
        have hw : |(-8535021/312500000 : ℝ)|=(8535021/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3248258243/5000000000 : ℝ)*x 0 + (143698173/400000000 : ℝ)*x 1 + (104750733/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3248258243/5000000000 : ℝ)^93 ≤ (29697987907559/50000000000000 : ℝ)^77 := by
    have hnat : (3248258243 : ℕ)^93*50000000000000^77 ≤ 29697987907559^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3248258243 5000000000 29697987907559 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143698173/400000000 : ℝ)^93 ≤ (14520281193259/50000000000000 : ℝ)^77 := by
    have hnat : (143698173 : ℕ)^93*50000000000000^77 ≤ 14520281193259^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143698173 400000000 14520281193259 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104750733/625000000 : ℝ)^93 ≤ (5781730893969/50000000000000 : ℝ)^77 := by
    have hnat : (104750733 : ℕ)^93*50000000000000^77 ≤ 5781730893969^77*625000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104750733 625000000 5781730893969 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3248258243/5000000000 : ℝ), (143698173/400000000 : ℝ), (104750733/625000000 : ℝ)] ![(29697987907559/50000000000000 : ℝ), (14520281193259/50000000000000 : ℝ), (5781730893969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3248258243/5000000000 : ℝ)|^93 ≤ (29697987907559/50000000000000 : ℝ)^77
        have hw : |(3248258243/5000000000 : ℝ)|=(3248258243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(143698173/400000000 : ℝ)|^93 ≤ (14520281193259/50000000000000 : ℝ)^77
        have hw : |(143698173/400000000 : ℝ)|=(143698173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104750733/625000000 : ℝ)|^93 ≤ (5781730893969/50000000000000 : ℝ)^77
        have hw : |(104750733/625000000 : ℝ)|=(104750733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-121645041/5000000000 : ℝ)*x 0 + (2905938043/5000000000 : ℝ)*x 1 + (5347693137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121645041/5000000000 : ℝ)^93 ≤ (1124018946417/100000000000000 : ℝ)^77 := by
    have hnat : (121645041 : ℕ)^93*100000000000000^77 ≤ 1124018946417^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121645041 5000000000 1124018946417 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2905938043/5000000000 : ℝ)^93 ≤ (25960504246983/50000000000000 : ℝ)^77 := by
    have hnat : (2905938043 : ℕ)^93*50000000000000^77 ≤ 25960504246983^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2905938043 5000000000 25960504246983 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5347693137/10000000000 : ℝ)^93 ≤ (46954972539379/100000000000000 : ℝ)^77 := by
    have hnat : (5347693137 : ℕ)^93*100000000000000^77 ≤ 46954972539379^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347693137 10000000000 46954972539379 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121645041/5000000000 : ℝ), (2905938043/5000000000 : ℝ), (5347693137/10000000000 : ℝ)] ![(1124018946417/100000000000000 : ℝ), (25960504246983/50000000000000 : ℝ), (46954972539379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121645041/5000000000 : ℝ)|^93 ≤ (1124018946417/100000000000000 : ℝ)^77
        have hw : |(-121645041/5000000000 : ℝ)|=(121645041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2905938043/5000000000 : ℝ)|^93 ≤ (25960504246983/50000000000000 : ℝ)^77
        have hw : |(2905938043/5000000000 : ℝ)|=(2905938043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5347693137/10000000000 : ℝ)|^93 ≤ (46954972539379/100000000000000 : ℝ)^77
        have hw : |(5347693137/10000000000 : ℝ)|=(5347693137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3066984201/5000000000 : ℝ)*x 0 + (-235685031/10000000000 : ℝ)*x 1 + (5019988799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3066984201/5000000000 : ℝ)^93 ≤ (55416089914711/100000000000000 : ℝ)^77 := by
    have hnat : (3066984201 : ℕ)^93*100000000000000^77 ≤ 55416089914711^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3066984201 5000000000 55416089914711 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235685031/10000000000 : ℝ)^93 ≤ (1081721029803/100000000000000 : ℝ)^77 := by
    have hnat : (235685031 : ℕ)^93*100000000000000^77 ≤ 1081721029803^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235685031 10000000000 1081721029803 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5019988799/10000000000 : ℝ)^93 ≤ (4350218904569/10000000000000 : ℝ)^77 := by
    have hnat : (5019988799 : ℕ)^93*10000000000000^77 ≤ 4350218904569^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019988799 10000000000 4350218904569 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3066984201/5000000000 : ℝ), (-235685031/10000000000 : ℝ), (5019988799/10000000000 : ℝ)] ![(55416089914711/100000000000000 : ℝ), (1081721029803/100000000000000 : ℝ), (4350218904569/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3066984201/5000000000 : ℝ)|^93 ≤ (55416089914711/100000000000000 : ℝ)^77
        have hw : |(3066984201/5000000000 : ℝ)|=(3066984201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-235685031/10000000000 : ℝ)|^93 ≤ (1081721029803/100000000000000 : ℝ)^77
        have hw : |(-235685031/10000000000 : ℝ)|=(235685031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5019988799/10000000000 : ℝ)|^93 ≤ (4350218904569/10000000000000 : ℝ)^77
        have hw : |(5019988799/10000000000 : ℝ)|=(5019988799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (57610947/125000000 : ℝ)*x 0 + (1232776901/2000000000 : ℝ)*x 1 + (-21000097/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57610947/125000000 : ℝ)^93 ≤ (39236717146149/100000000000000 : ℝ)^77 := by
    have hnat : (57610947 : ℕ)^93*100000000000000^77 ≤ 39236717146149^77*125000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57610947 125000000 39236717146149 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232776901/2000000000 : ℝ)^93 ≤ (55742686254057/100000000000000 : ℝ)^77 := by
    have hnat : (1232776901 : ℕ)^93*100000000000000^77 ≤ 55742686254057^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232776901 2000000000 55742686254057 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21000097/250000000 : ℝ)^93 ≤ (1004119318061/20000000000000 : ℝ)^77 := by
    have hnat : (21000097 : ℕ)^93*20000000000000^77 ≤ 1004119318061^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21000097 250000000 1004119318061 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(57610947/125000000 : ℝ), (1232776901/2000000000 : ℝ), (-21000097/250000000 : ℝ)] ![(39236717146149/100000000000000 : ℝ), (55742686254057/100000000000000 : ℝ), (1004119318061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(57610947/125000000 : ℝ)|^93 ≤ (39236717146149/100000000000000 : ℝ)^77
        have hw : |(57610947/125000000 : ℝ)|=(57610947/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1232776901/2000000000 : ℝ)|^93 ≤ (55742686254057/100000000000000 : ℝ)^77
        have hw : |(1232776901/2000000000 : ℝ)|=(1232776901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21000097/250000000 : ℝ)|^93 ≤ (1004119318061/20000000000000 : ℝ)^77
        have hw : |(-21000097/250000000 : ℝ)|=(21000097/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328063_s1_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (209587629/312500000 : ℝ)*x 0 + (2614877059/10000000000 : ℝ)*x 1 + (1235806851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209587629/312500000 : ℝ)^93 ≤ (61725827560963/100000000000000 : ℝ)^77 := by
    have hnat : (209587629 : ℕ)^93*100000000000000^77 ≤ 61725827560963^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209587629 312500000 61725827560963 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614877059/10000000000 : ℝ)^93 ≤ (19788013098499/100000000000000 : ℝ)^77 := by
    have hnat : (2614877059 : ℕ)^93*100000000000000^77 ≤ 19788013098499^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614877059 10000000000 19788013098499 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1235806851/5000000000 : ℝ)^93 ≤ (3697231864367/20000000000000 : ℝ)^77 := by
    have hnat : (1235806851 : ℕ)^93*20000000000000^77 ≤ 3697231864367^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235806851 5000000000 3697231864367 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209587629/312500000 : ℝ), (2614877059/10000000000 : ℝ), (1235806851/5000000000 : ℝ)] ![(61725827560963/100000000000000 : ℝ), (19788013098499/100000000000000 : ℝ), (3697231864367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209587629/312500000 : ℝ)|^93 ≤ (61725827560963/100000000000000 : ℝ)^77
        have hw : |(209587629/312500000 : ℝ)|=(209587629/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614877059/10000000000 : ℝ)|^93 ≤ (19788013098499/100000000000000 : ℝ)^77
        have hw : |(2614877059/10000000000 : ℝ)|=(2614877059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1235806851/5000000000 : ℝ)|^93 ≤ (3697231864367/20000000000000 : ℝ)^77
        have hw : |(1235806851/5000000000 : ℝ)|=(1235806851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328063 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((34867/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34867/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1419/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1419/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16957/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16957/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (80697/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-38408089/2000000000 : ℝ)*X 0 0+(5444040647/10000000000 : ℝ)*X 0 1+(1435701761/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1483249797/10000000000 : ℝ)*X 0 0+(1188211747/10000000000 : ℝ)*X 0 1+(1703649263/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2355503631/10000000000 : ℝ)*X 1 0+(-25086217/5000000000 : ℝ)*X 1 1+(2129561617/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((47110029/200000000 : ℝ)*X 2 0+(8518248173/10000000000 : ℝ)*X 2 1+(-12543083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1566825153/5000000000 : ℝ)*X 0 0+(7171827243/10000000000 : ℝ)*X 0 1+(646067129/5000000000 : ℝ)*X 0 2+(1566825153/5000000000 : ℝ)*X 1 0+(7171827243/10000000000 : ℝ)*X 1 1+(646067129/5000000000 : ℝ)*X 1 2+(1566825153/5000000000 : ℝ)*X 2 0+(7171827243/10000000000 : ℝ)*X 2 1+(646067129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-5060157/2500000000 : ℝ)*X 0 0+(572745351/2500000000 : ℝ)*X 0 1+(4288489263/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((538305507/5000000000 : ℝ)*X 1 0+(-300842891/2000000000 : ℝ)*X 1 1+(857697707/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8212420461/10000000000 : ℝ)*X 2 0+(340924099/1250000000 : ℝ)*X 2 1+(-92093617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((748774533/1000000000 : ℝ)*X 0 0+(42859039/156250000 : ℝ)*X 0 1+(260471621/2000000000 : ℝ)*X 0 2+(748774533/1000000000 : ℝ)*X 1 0+(42859039/156250000 : ℝ)*X 1 1+(260471621/2000000000 : ℝ)*X 1 2+(748774533/1000000000 : ℝ)*X 2 0+(42859039/156250000 : ℝ)*X 2 1+(260471621/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-132639663/10000000000 : ℝ)*X 0 0+(7273185617/10000000000 : ℝ)*X 0 1+(478858149/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8161105099/10000000000 : ℝ)*X 1 0+(-7390343/5000000000 : ℝ)*X 1 1+(282508733/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((105016193/1250000000 : ℝ)*X 2 0+(4359305967/5000000000 : ℝ)*X 2 1+(-378935791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1898956749/2500000000 : ℝ)*X 0 0+(291909411/1250000000 : ℝ)*X 0 1+(160793623/1000000000 : ℝ)*X 0 2+(1898956749/2500000000 : ℝ)*X 1 0+(291909411/1250000000 : ℝ)*X 1 1+(160793623/1000000000 : ℝ)*X 1 2+(1898956749/2500000000 : ℝ)*X 2 0+(291909411/1250000000 : ℝ)*X 2 1+(160793623/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((62307/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62307/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23663338426129538633019/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (236508528091/200000000000 : ℝ)*(base7) + (79123/62500000000 : ℝ)*(base19) + (484357/500000000000 : ℝ)*(base50) + (23929/62500000000 : ℝ)*(base53) + (473051/500000000000 : ℝ)*(base60) + (271031331893/200000000000 : ℝ)*(major_s0_0) + (271031331893/200000000000 : ℝ)*(major_s0_1) + (1355156276601/1000000000000 : ℝ)*(major_s0_2) + (133367/40000000000 : ℝ)*(sp_s0_0) + (1449525708783/1000000000000 : ℝ)*(sp_s0_7) + (1449556113979/1000000000000 : ℝ)*(sp_s0_8) + (362389440703/250000000000 : ℝ)*(sp_s0_9) + (1807110751743/1000000000000 : ℝ)*(sp_s0_13) + (28336989/1000000000000 : ℝ)*(sp_s0_14) + (624568111287/1000000000000 : ℝ)*(f.failure) + (362389440703/250000000000 : ℝ)*(f.sum) + (4052699532552077/5000000000000000000000000000 : ℝ)*base62 + (29607372663083/200000000000000000000000000 : ℝ)*base64 + (14049455917281/40000000000000000000000000 : ℝ)*base67 + (8424325979932069/10000000000000000000000000000 : ℝ)*base68 + (184545816534753/2000000000000000000000000000 : ℝ)*base71 + (9853997465281/40000000000000000000000000 : ℝ)*base73 + (1359811122034417/2000000000000000000000000000 : ℝ)*base74 + (1795694375434417/2000000000000000000000000000 : ℝ)*base76 + (31560709281/20000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (127/4000000000000000 : ℝ)*base86 + (127/4000000000000000 : ℝ)*base88 + (127/4000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62187/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62187/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (44640816257254862504967/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23745504071/20000000000 : ℝ)*(base7) + (5122261/1000000000000 : ℝ)*(base27) + (300771/1000000000000 : ℝ)*(base49) + (70797/250000000000 : ℝ)*(base53) + (1325518172461/1000000000000 : ℝ)*(major_s0_0) + (1325518172461/1000000000000 : ℝ)*(major_s0_1) + (1325517889273/1000000000000 : ℝ)*(major_s0_2) + (355949/500000000000 : ℝ)*(sp_s0_0) + (5082409/100000000000 : ℝ)*(sp_s0_8) + (1401390835089/1000000000000 : ℝ)*(sp_s0_14) + (1401340722897/1000000000000 : ℝ)*(sp_s0_15) + (56055673207/40000000000 : ℝ)*(sp_s0_16) + (179810288691/100000000000 : ℝ)*(sp_s0_20) + (75443007/1000000000000 : ℝ)*(sp_s0_27) + (152727062157/250000000000 : ℝ)*(f.failure) + (56055673207/40000000000 : ℝ)*(f.sum) + (380221152387977/5000000000000000000000000000 : ℝ)*base63 + (42248129269259/200000000000000000000000000 : ℝ)*base64 + (147721547191463/200000000000000000000000000 : ℝ)*base66 + (903422411998363/10000000000000000000000000000 : ℝ)*base69 + (583141263685359/10000000000000000000000000000 : ℝ)*base70 + (58031098871463/200000000000000000000000000 : ℝ)*base72 + (1674806904222409/10000000000000000000000000000 : ℝ)*base74 + (1699445933222409/10000000000000000000000000000 : ℝ)*base76 + (54956959321463/100000000000000000000000000 : ℝ)*base78 + (397/1000000000000000 : ℝ)*base86 + (397/1000000000000000 : ℝ)*base88 + (397/1000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3/5 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3/5 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24350517289516718452083/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (296168312557/250000000000 : ℝ)*(base7) + (2384951/1000000000000 : ℝ)*(base27) + (68691478817/500000000000 : ℝ)*(base40) + (1050287/1000000000000 : ℝ)*(base43) + (20111/500000000000 : ℝ)*(base49) + (325393149517/250000000000 : ℝ)*(major_s0_0) + (1301571547781/1000000000000 : ℝ)*(major_s0_1) + (325393149517/250000000000 : ℝ)*(major_s0_2) + (804803/62500000000 : ℝ)*(sp_s0_9) + (545829/20000000000 : ℝ)*(sp_s0_20) + (1365939857039/1000000000000 : ℝ)*(sp_s0_21) + (682970453663/500000000000 : ℝ)*(sp_s0_22) + (1365926980191/1000000000000 : ℝ)*(sp_s0_23) + (1784515724107/1000000000000 : ℝ)*(sp_s0_27) + (599872150279/1000000000000 : ℝ)*(f.failure) + (682970453663/500000000000 : ℝ)*(f.sum) + (4532951345386981/10000000000000000000000000000 : ℝ)*base62 + (7261848786689/50000000000000000000000000 : ℝ)*base65 + (74795969447023/200000000000000000000000000 : ℝ)*base66 + (732118337388873/2500000000000000000000000000 : ℝ)*base68 + (996421613195577/2500000000000000000000000000 : ℝ)*base71 + (16500868018311/50000000000000000000000000 : ℝ)*base72 + (3452984702831489/10000000000000000000000000000 : ℝ)*base74 + (1484944470611127/2500000000000000000000000000 : ℝ)*base77 + (177857465760267/200000000000000000000000000 : ℝ)*base78 + (559/4000000000000000 : ℝ)*base86 + (559/4000000000000000 : ℝ)*base88 + (559/4000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (62307/100000 : ℝ) ^ (91/16 : ℝ) ≤ (6783100995972578101/100000000000000000000 : ℝ) := by
    have hpowers : (62307/100000 : ℝ)^91 ≤ (6783100995972578101/100000000000000000000 : ℝ)^16 := by
      have hnat : (62307 : ℕ)^91*100000000000000000000^16 ≤ 6783100995972578101^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62307 100000 6783100995972578101 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62307/100000 : ℝ)) (X := (6783100995972578101/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (106783100995972578101/100000000000000000000 : ℝ) ≤ (1011606086329177/1000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (106783100995972578101/100000000000000000000 : ℝ)^16 ≤ (1011606086329177/1000000000000000 : ℝ)^91 := by
      have hnat : (106783100995972578101 : ℕ)^16*1000000000000000^91 ≤ 1011606086329177^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106783100995972578101 100000000000000000000 1011606086329177 1000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011606086329177/1000000000000000 : ℝ)) (X := (106783100995972578101/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (56783100995972578101/50000000000000000000 : ℝ) ≤ (1022619636359169/1000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (56783100995972578101/50000000000000000000 : ℝ)^16 ≤ (1022619636359169/1000000000000000 : ℝ)^91 := by
      have hnat : (56783100995972578101 : ℕ)^16*1000000000000000^91 ≤ 1022619636359169^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56783100995972578101 50000000000000000000 1022619636359169 1000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1022619636359169/1000000000000000 : ℝ)) (X := (56783100995972578101/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3868695443059/207690000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(59856250163/3386250000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (62307/100000 : ℝ)) (alpha := (3868695443059/207690000000000 : ℝ)) (beta := (59856250163/3386250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (62307/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3868695443059/207690000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(59856250163/3386250000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (62187/100000 : ℝ) ^ (91/16 : ℝ) ≤ (3354567344355892303/50000000000000000000 : ℝ) := by
    have hpowers : (62187/100000 : ℝ)^91 ≤ (3354567344355892303/50000000000000000000 : ℝ)^16 := by
      have hnat : (62187 : ℕ)^91*50000000000000000000^16 ≤ 3354567344355892303^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62187 100000 3354567344355892303 50000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62187/100000 : ℝ)) (X := (3354567344355892303/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (53354567344355892303/50000000000000000000 : ℝ) ≤ (10114828481043537/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (53354567344355892303/50000000000000000000 : ℝ)^16 ≤ (10114828481043537/10000000000000000 : ℝ)^91 := by
      have hnat : (53354567344355892303 : ℕ)^16*10000000000000000^91 ≤ 10114828481043537^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53354567344355892303 50000000000000000000 10114828481043537 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10114828481043537/10000000000000000 : ℝ)) (X := (53354567344355892303/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (28354567344355892303/25000000000000000000 : ℝ) ≤ (5111926496982791/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (28354567344355892303/25000000000000000000 : ℝ)^16 ≤ (5111926496982791/5000000000000000 : ℝ)^91 := by
      have hnat : (28354567344355892303 : ℕ)^16*5000000000000000^91 ≤ 5111926496982791^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28354567344355892303 25000000000000000000 5111926496982791 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5111926496982791/5000000000000000 : ℝ)) (X := (28354567344355892303/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(114828481043537/6218700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1147626451811/65460000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (62187/100000 : ℝ)) (alpha := (114828481043537/6218700000000000 : ℝ)) (beta := (1147626451811/65460000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (62187/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(114828481043537/6218700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1147626451811/65460000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3/5 : ℝ) ^ (91/16 : ℝ) ≤ (5473123355461192981/100000000000000000000 : ℝ) := by
    have hpowers : (3/5 : ℝ)^91 ≤ (5473123355461192981/100000000000000000000 : ℝ)^16 := by
      have hnat : (3 : ℕ)^91*100000000000000000000^16 ≤ 5473123355461192981^16*5^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 5 5473123355461192981 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3/5 : ℝ)) (X := (5473123355461192981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (105473123355461192981/100000000000000000000 : ℝ) ≤ (10094129895605761/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (105473123355461192981/100000000000000000000 : ℝ)^16 ≤ (10094129895605761/10000000000000000 : ℝ)^91 := by
      have hnat : (105473123355461192981 : ℕ)^16*10000000000000000^91 ≤ 10094129895605761^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105473123355461192981 100000000000000000000 10094129895605761 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10094129895605761/10000000000000000 : ℝ)) (X := (105473123355461192981/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (55473123355461192981/50000000000000000000 : ℝ) ≤ (2546079129647409/2500000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (55473123355461192981/50000000000000000000 : ℝ)^16 ≤ (2546079129647409/2500000000000000 : ℝ)^91 := by
      have hnat : (55473123355461192981 : ℕ)^16*2500000000000000^91 ≤ 2546079129647409^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55473123355461192981 50000000000000000000 2546079129647409 2500000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2546079129647409/2500000000000000 : ℝ)) (X := (55473123355461192981/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(31376631868587/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(721492983871/48000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (3/5 : ℝ)) (alpha := (31376631868587/2000000000000000 : ℝ)) (beta := (721492983871/48000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3/5 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(31376631868587/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(721492983871/48000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-980855679/10000000000 : ℝ)*X 0 0+(533633159/1000000000 : ℝ)*X 0 1+(670301687/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5336215961/10000000000 : ℝ)*X 1 0+(-979695833/10000000000 : ℝ)*X 1 1+(5363343783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5354086727/10000000000 : ℝ)*X 2 0+(5359476163/10000000000 : ℝ)*X 2 1+(-239933611/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((809563573/2000000000 : ℝ)*X 0 0+(1008292093/2500000000 : ℝ)*X 0 1+(1999747533/5000000000 : ℝ)*X 0 2+(809563573/2000000000 : ℝ)*X 1 0+(1008292093/2500000000 : ℝ)*X 1 1+(1999747533/5000000000 : ℝ)*X 1 2+(809563573/2000000000 : ℝ)*X 2 0+(1008292093/2500000000 : ℝ)*X 2 1+(1999747533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-869643037/10000000000 : ℝ)*X 0 0+(46350717/100000000 : ℝ)*X 0 1+(3059758267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((50028193/100000000 : ℝ)*X 1 0+(-36663287/1250000000 : ℝ)*X 1 1+(3060227557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((190408281/400000000 : ℝ)*X 2 0+(3183457639/5000000000 : ℝ)*X 2 1+(-262867197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4515657849/10000000000 : ℝ)*X 0 0+(5674372849/10000000000 : ℝ)*X 0 1+(1641768947/10000000000 : ℝ)*X 0 2+(4515657849/10000000000 : ℝ)*X 1 0+(5674372849/10000000000 : ℝ)*X 1 1+(1641768947/10000000000 : ℝ)*X 1 2+(4515657849/10000000000 : ℝ)*X 2 0+(5674372849/10000000000 : ℝ)*X 2 1+(1641768947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-296245563/10000000000 : ℝ)*X 0 0+(2506427149/5000000000 : ℝ)*X 0 1+(305463137/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((930760929/2000000000 : ℝ)*X 1 0+(-857060091/10000000000 : ℝ)*X 1 1+(6110201773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6099053891/10000000000 : ℝ)*X 2 0+(5036219483/10000000000 : ℝ)*X 2 1+(-8535021/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3248258243/5000000000 : ℝ)*X 0 0+(143698173/400000000 : ℝ)*X 0 1+(104750733/625000000 : ℝ)*X 0 2+(3248258243/5000000000 : ℝ)*X 1 0+(143698173/400000000 : ℝ)*X 1 1+(104750733/625000000 : ℝ)*X 1 2+(3248258243/5000000000 : ℝ)*X 2 0+(143698173/400000000 : ℝ)*X 2 1+(104750733/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-121645041/5000000000 : ℝ)*X 0 0+(2905938043/5000000000 : ℝ)*X 0 1+(5347693137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3066984201/5000000000 : ℝ)*X 1 0+(-235685031/10000000000 : ℝ)*X 1 1+(5019988799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((57610947/125000000 : ℝ)*X 2 0+(1232776901/2000000000 : ℝ)*X 2 1+(-21000097/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((209587629/312500000 : ℝ)*X 0 0+(2614877059/10000000000 : ℝ)*X 0 1+(1235806851/5000000000 : ℝ)*X 0 2+(209587629/312500000 : ℝ)*X 1 0+(2614877059/10000000000 : ℝ)*X 1 1+(1235806851/5000000000 : ℝ)*X 1 2+(209587629/312500000 : ℝ)*X 2 0+(2614877059/10000000000 : ℝ)*X 2 1+(1235806851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328063_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((34867/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34867/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35381182532726413065857914071/1888248250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1874213/250000000000 : ℝ)*(base23) + (36006585071/200000000000 : ℝ)*(base60) + (2243798319471/500000000000 : ℝ)*(major_s1_0) + (2243798319471/500000000000 : ℝ)*(major_s1_1) + (2243798319471/500000000000 : ℝ)*(major_s1_2) + (272761/50000000000 : ℝ)*(sp_s1_0) + (9160617/500000000000 : ℝ)*(sp_s1_6) + (6906864716473/1000000000000 : ℝ)*(sp_s1_7) + (3453419853673/500000000000 : ℝ)*(sp_s1_8) + (107919499847/15625000000 : ℝ)*(sp_s1_9) + (517059210329/250000000000 : ℝ)*(sp_s1_13) + (61697779/1000000000000 : ℝ)*(sp_s1_14) + (737297/8000000000 : ℝ)*(sp_s1_15) + (19095603/250000000000 : ℝ)*(sp_s1_23) + (41365103251/20000000000 : ℝ)*(f.failure) + (6906931869471/1000000000000 : ℝ)*(f.sum) + (4015136285466920733/20729000000000000000000000000000 : ℝ)*base63 + (6857383948453/8000000000000000000000000 : ℝ)*base64 + (4339182481751/10910000000000000000000000 : ℝ)*base66 + (376174803457477/1000000000000000000000000000 : ℝ)*base69 + (33418625807632119/55384000000000000000000000000 : ℝ)*base70 + (1813620822661/9030000000000000000000000 : ℝ)*base73 + (305427013469721/1036450000000000000000000000 : ℝ)*base74 + (25227556366421/34615000000000000000000000 : ℝ)*base76 + (347685867700903/9851730000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (69/80000000000000 : ℝ)*base87 + (69/80000000000000 : ℝ)*base89 + (69/80000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1419/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1419/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (151788254366223209429315781919/11329489500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6598519/1000000000000 : ℝ)*(base21) + (289039/1000000000000 : ℝ)*(base60) + (4552417409173/1000000000000 : ℝ)*(major_s1_0) + (4552417409173/1000000000000 : ℝ)*(major_s1_1) + (4552417409173/1000000000000 : ℝ)*(major_s1_2) + (1051331/1000000000000 : ℝ)*(sp_s1_0) + (10994031/250000000000 : ℝ)*(sp_s1_2) + (1132581/20000000000 : ℝ)*(sp_s1_7) + (48049021/1000000000000 : ℝ)*(sp_s1_8) + (7006642745057/1000000000000 : ℝ)*(sp_s1_14) + (7006652376417/1000000000000 : ℝ)*(sp_s1_15) + (1401329970159/200000000000 : ℝ)*(sp_s1_16) + (2098095729309/1000000000000 : ℝ)*(sp_s1_20) + (34197721/1000000000000 : ℝ)*(sp_s1_27) + (209812992703/100000000000 : ℝ)*(f.failure) + (3503350212719/500000000000 : ℝ)*(f.sum) + (40902324794028561037/124374000000000000000000000000000 : ℝ)*base63 + (30955808703317/48000000000000000000000000 : ℝ)*base64 + (15512775625597/65460000000000000000000000 : ℝ)*base66 + (205647798948551/2000000000000000000000000000 : ℝ)*base69 + (45179156859395597/110768000000000000000000000000 : ℝ)*base70 + (7169309335169/27090000000000000000000000 : ℝ)*base72 + (3395809026450949/6218700000000000000000000000 : ℝ)*base74 + (1108067574301/103845000000000000000000000 : ℝ)*base76 + (2249427080196971/59110380000000000000000000000 : ℝ)*base78 + (137/400000000000000 : ℝ)*base87 + (137/400000000000000 : ℝ)*base89 + (137/400000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16957/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16957/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7553087880590008538765911/935914350000000000000000000000 : ℝ) := by norm_num
    linear_combination (2195027/500000000000 : ℝ)*(base15) + (212973182143/1000000000000 : ℝ)*(base40) + (1052607305549/250000000000 : ℝ)*(major_s1_0) + (1052607305549/250000000000 : ℝ)*(major_s1_1) + (1052607305549/250000000000 : ℝ)*(major_s1_2) + (20994489/500000000000 : ℝ)*(sp_s1_0) + (9460629/250000000000 : ℝ)*(sp_s1_1) + (20642659/1000000000000 : ℝ)*(sp_s1_2) + (17260643/500000000000 : ℝ)*(sp_s1_9) + (7334237/200000000000 : ℝ)*(sp_s1_20) + (1296060047941/200000000000 : ℝ)*(sp_s1_21) + (405018749757/62500000000 : ℝ)*(sp_s1_22) + (3240143532369/500000000000 : ℝ)*(sp_s1_23) + (1940476854427/1000000000000 : ℝ)*(sp_s1_27) + (485128381403/250000000000 : ℝ)*(f.failure) + (3240171114341/500000000000 : ℝ)*(f.sum) + (3240838894151041819/31093500000000000000000000000000 : ℝ)*base62 + (7148284161421/12000000000000000000000000 : ℝ)*base64 + (16368938115733/32730000000000000000000000 : ℝ)*base66 + (46908050589263/500000000000000000000000000 : ℝ)*base69 + (4626259730709339/27692000000000000000000000000 : ℝ)*base71 + (6127444958483/13545000000000000000000000 : ℝ)*base72 + (1913218718730589/3109350000000000000000000000 : ℝ)*base74 + (67438481175913/207690000000000000000000000 : ℝ)*base76 + (3512325627011143/14777595000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (637/1000000000000000 : ℝ)*base87 + (637/1000000000000000 : ℝ)*base89 + (637/1000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p028_positive63 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders 63) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  have ho : distinctOrders 63=![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] := by decide
  have hs : ![![true, true, true], ![true, true, true], ![true, true, true]]=(fun (_ _ : Fin 3) => true) := by decide
  have hh := collision_c328063 p hpa (by linarith only [hpb]) X (by simpa only [ho,hs] using hX)
  apply positive_chart_tailratio hX (by decide)
  intro j
  have hn := positive_chart_nonnegative hX j j
  fin_cases j
  · change 0 ≤ pair X 0 0 at hn
    change pair X 0 1 ≤ (2/5:ℝ)*pair X 0 0
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.1,hn]
  · change 0 ≤ pair X 1 1 at hn
    change pair X 1 0 ≤ (2/5:ℝ)*pair X 1 1
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.1,hn]
  · change 0 ≤ pair X 2 2 at hn
    change pair X 2 0 ≤ (2/5:ℝ)*pair X 2 2
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.2,hn]

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders 63) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_positive63 p hpa hpb X hX

#print axioms solution

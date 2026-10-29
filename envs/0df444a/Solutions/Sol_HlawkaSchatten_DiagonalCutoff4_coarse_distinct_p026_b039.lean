-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b039
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:10:08.491847+00:00
-- url     : https://prove2.me/submissions/b3946c5c-66f2-4327-9df7-f9515bbe1f0c

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
theorem collision_support_c326078_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-44874977/156250000 : ℝ)*x 0 + (44874977/156250000 : ℝ)*x 1 + (-6242728177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44874977/156250000 : ℝ)^89 ≤ (21848924697587/100000000000000 : ℝ)^73 := by
    have hnat : (44874977 : ℕ)^89*100000000000000^73 ≤ 21848924697587^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44874977 156250000 21848924697587 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44874977/156250000 : ℝ)^89 ≤ (21848924697587/100000000000000 : ℝ)^73 := by
    have hnat : (44874977 : ℕ)^89*100000000000000^73 ≤ 21848924697587^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44874977 156250000 21848924697587 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6242728177/10000000000 : ℝ)^89 ≤ (11260430118947/20000000000000 : ℝ)^73 := by
    have hnat : (6242728177 : ℕ)^89*20000000000000^73 ≤ 11260430118947^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6242728177 10000000000 11260430118947 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44874977/156250000 : ℝ), (44874977/156250000 : ℝ), (-6242728177/10000000000 : ℝ)] ![(21848924697587/100000000000000 : ℝ), (21848924697587/100000000000000 : ℝ), (11260430118947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44874977/156250000 : ℝ)|^89 ≤ (21848924697587/100000000000000 : ℝ)^73
        have hw : |(-44874977/156250000 : ℝ)|=(44874977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44874977/156250000 : ℝ)|^89 ≤ (21848924697587/100000000000000 : ℝ)^73
        have hw : |(44874977/156250000 : ℝ)|=(44874977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6242728177/10000000000 : ℝ)|^89 ≤ (11260430118947/20000000000000 : ℝ)^73
        have hw : |(-6242728177/10000000000 : ℝ)|=(6242728177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326078_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6242728177/10000000000 : ℝ)*x 0 + (-44874977/156250000 : ℝ)*x 1 + (-44874977/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6242728177/10000000000 : ℝ)^89 ≤ (11260430118947/20000000000000 : ℝ)^73 := by
    have hnat : (6242728177 : ℕ)^89*20000000000000^73 ≤ 11260430118947^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6242728177 10000000000 11260430118947 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44874977/156250000 : ℝ)^89 ≤ (21848924697587/100000000000000 : ℝ)^73 := by
    have hnat : (44874977 : ℕ)^89*100000000000000^73 ≤ 21848924697587^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44874977 156250000 21848924697587 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44874977/156250000 : ℝ)^89 ≤ (21848924697587/100000000000000 : ℝ)^73 := by
    have hnat : (44874977 : ℕ)^89*100000000000000^73 ≤ 21848924697587^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44874977 156250000 21848924697587 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6242728177/10000000000 : ℝ), (-44874977/156250000 : ℝ), (-44874977/156250000 : ℝ)] ![(11260430118947/20000000000000 : ℝ), (21848924697587/100000000000000 : ℝ), (21848924697587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6242728177/10000000000 : ℝ)|^89 ≤ (11260430118947/20000000000000 : ℝ)^73
        have hw : |(6242728177/10000000000 : ℝ)|=(6242728177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44874977/156250000 : ℝ)|^89 ≤ (21848924697587/100000000000000 : ℝ)^73
        have hw : |(-44874977/156250000 : ℝ)|=(44874977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44874977/156250000 : ℝ)|^89 ≤ (21848924697587/100000000000000 : ℝ)^73
        have hw : |(-44874977/156250000 : ℝ)|=(44874977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326078_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (44874977/156250000 : ℝ)*x 0 + (6242728177/10000000000 : ℝ)*x 1 + (44874977/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44874977/156250000 : ℝ)^89 ≤ (21848924697587/100000000000000 : ℝ)^73 := by
    have hnat : (44874977 : ℕ)^89*100000000000000^73 ≤ 21848924697587^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44874977 156250000 21848924697587 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6242728177/10000000000 : ℝ)^89 ≤ (11260430118947/20000000000000 : ℝ)^73 := by
    have hnat : (6242728177 : ℕ)^89*20000000000000^73 ≤ 11260430118947^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6242728177 10000000000 11260430118947 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44874977/156250000 : ℝ)^89 ≤ (21848924697587/100000000000000 : ℝ)^73 := by
    have hnat : (44874977 : ℕ)^89*100000000000000^73 ≤ 21848924697587^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44874977 156250000 21848924697587 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44874977/156250000 : ℝ), (6242728177/10000000000 : ℝ), (44874977/156250000 : ℝ)] ![(21848924697587/100000000000000 : ℝ), (11260430118947/20000000000000 : ℝ), (21848924697587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44874977/156250000 : ℝ)|^89 ≤ (21848924697587/100000000000000 : ℝ)^73
        have hw : |(44874977/156250000 : ℝ)|=(44874977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6242728177/10000000000 : ℝ)|^89 ≤ (11260430118947/20000000000000 : ℝ)^73
        have hw : |(6242728177/10000000000 : ℝ)|=(6242728177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44874977/156250000 : ℝ)|^89 ≤ (21848924697587/100000000000000 : ℝ)^73
        have hw : |(44874977/156250000 : ℝ)|=(44874977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326078_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2030595209/5000000000 : ℝ)*x 0 + (2030595209/5000000000 : ℝ)*x 1 + (-2030595209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030595209/5000000000 : ℝ)^89 ≤ (16666666665057/50000000000000 : ℝ)^73 := by
    have hnat : (2030595209 : ℕ)^89*50000000000000^73 ≤ 16666666665057^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030595209 5000000000 16666666665057 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2030595209/5000000000 : ℝ)^89 ≤ (16666666665057/50000000000000 : ℝ)^73 := by
    have hnat : (2030595209 : ℕ)^89*50000000000000^73 ≤ 16666666665057^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030595209 5000000000 16666666665057 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2030595209/5000000000 : ℝ)^89 ≤ (16666666665057/50000000000000 : ℝ)^73 := by
    have hnat : (2030595209 : ℕ)^89*50000000000000^73 ≤ 16666666665057^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030595209 5000000000 16666666665057 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2030595209/5000000000 : ℝ), (2030595209/5000000000 : ℝ), (-2030595209/5000000000 : ℝ)] ![(16666666665057/50000000000000 : ℝ), (16666666665057/50000000000000 : ℝ), (16666666665057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2030595209/5000000000 : ℝ)|^89 ≤ (16666666665057/50000000000000 : ℝ)^73
        have hw : |(2030595209/5000000000 : ℝ)|=(2030595209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2030595209/5000000000 : ℝ)|^89 ≤ (16666666665057/50000000000000 : ℝ)^73
        have hw : |(2030595209/5000000000 : ℝ)|=(2030595209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2030595209/5000000000 : ℝ)|^89 ≤ (16666666665057/50000000000000 : ℝ)^73
        have hw : |(-2030595209/5000000000 : ℝ)|=(2030595209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326078 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-44874977/156250000 : ℝ)*X 0 0+(44874977/156250000 : ℝ)*X 0 1+(-6242728177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326078_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6242728177/10000000000 : ℝ)*X 1 0+(-44874977/156250000 : ℝ)*X 1 1+(-44874977/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326078_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((44874977/156250000 : ℝ)*X 2 0+(6242728177/10000000000 : ℝ)*X 2 1+(44874977/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326078_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2030595209/5000000000 : ℝ)*X 0 0+(2030595209/5000000000 : ℝ)*X 0 1+(-2030595209/5000000000 : ℝ)*X 0 2+(2030595209/5000000000 : ℝ)*X 1 0+(2030595209/5000000000 : ℝ)*X 1 1+(-2030595209/5000000000 : ℝ)*X 1 2+(2030595209/5000000000 : ℝ)*X 2 0+(2030595209/5000000000 : ℝ)*X 2 1+(-2030595209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326078_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-46541247337357516133994849303/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83/1000000000000 : ℝ)*(base33) + (58402282369/100000000000 : ℝ)*(base39) + (36501426481/62500000000 : ℝ)*(base49) + (49/1000000000000 : ℝ)*(base50) + (292011411851/500000000000 : ℝ)*(base59) + (2062649999917/1000000000000 : ℝ)*(major_s0_0) + (41253/20000 : ℝ)*(major_s0_1) + (41253/20000 : ℝ)*(major_s0_2) + (3102749821919/1000000000000 : ℝ)*(sp_s0_0) + (3102749822099/1000000000000 : ℝ)*(sp_s0_1) + (3102749821823/1000000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (620549964381/200000000000 : ℝ)*(f.sum) + (69708219891/5000000000000000000000 : ℝ)*base63 + (1755066591/5000000000000000000000 : ℝ)*base64 + (192790837/10000000000000000000000 : ℝ)*base66 + (2443498281023/10000000000000000000000 : ℝ)*base68 + (129360366840831/200000000000000000000000000 : ℝ)*base70 + (327475885158741551/10000000000000000000000000000 : ℝ)*base73 + (3899137247/5000000000000000000000 : ℝ)*base74 + (66989946700831/200000000000000000000000000 : ℝ)*base76 + (3301435842741551/10000000000000000000000000000 : ℝ)*base79 + (7/500000000000 : ℝ)*base81 + (277/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c326079_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (387074263/500000000 : ℝ)*x 0 + (-1498029651/10000000000 : ℝ)*x 1 + (-3727349/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387074263/500000000 : ℝ)^89 ≤ (36595443683517/50000000000000 : ℝ)^73 := by
    have hnat : (387074263 : ℕ)^89*50000000000000^73 ≤ 36595443683517^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387074263 500000000 36595443683517 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1498029651/10000000000 : ℝ)^89 ≤ (617579073313/6250000000000 : ℝ)^73 := by
    have hnat : (1498029651 : ℕ)^89*6250000000000^73 ≤ 617579073313^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498029651 10000000000 617579073313 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3727349/16000000 : ℝ)^89 ≤ (16927847443777/100000000000000 : ℝ)^73 := by
    have hnat : (3727349 : ℕ)^89*100000000000000^73 ≤ 16927847443777^73*16000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3727349 16000000 16927847443777 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(387074263/500000000 : ℝ), (-1498029651/10000000000 : ℝ), (-3727349/16000000 : ℝ)] ![(36595443683517/50000000000000 : ℝ), (617579073313/6250000000000 : ℝ), (16927847443777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(387074263/500000000 : ℝ)|^89 ≤ (36595443683517/50000000000000 : ℝ)^73
        have hw : |(387074263/500000000 : ℝ)|=(387074263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1498029651/10000000000 : ℝ)|^89 ≤ (617579073313/6250000000000 : ℝ)^73
        have hw : |(-1498029651/10000000000 : ℝ)|=(1498029651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3727349/16000000 : ℝ)|^89 ≤ (16927847443777/100000000000000 : ℝ)^73
        have hw : |(-3727349/16000000 : ℝ)|=(3727349/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (738315997/2500000000 : ℝ)*x 0 + (722003707/1250000000 : ℝ)*x 1 + (1665697123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (738315997/2500000000 : ℝ)^89 ≤ (2260498051293/10000000000000 : ℝ)^73 := by
    have hnat : (738315997 : ℕ)^89*10000000000000^73 ≤ 2260498051293^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738315997 2500000000 2260498051293 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722003707/1250000000 : ℝ)^89 ≤ (51213423284377/100000000000000 : ℝ)^73 := by
    have hnat : (722003707 : ℕ)^89*100000000000000^73 ≤ 51213423284377^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722003707 1250000000 51213423284377 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1665697123/5000000000 : ℝ)^89 ≤ (1309079809721/5000000000000 : ℝ)^73 := by
    have hnat : (1665697123 : ℕ)^89*5000000000000^73 ≤ 1309079809721^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665697123 5000000000 1309079809721 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(738315997/2500000000 : ℝ), (722003707/1250000000 : ℝ), (1665697123/5000000000 : ℝ)] ![(2260498051293/10000000000000 : ℝ), (51213423284377/100000000000000 : ℝ), (1309079809721/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(738315997/2500000000 : ℝ)|^89 ≤ (2260498051293/10000000000000 : ℝ)^73
        have hw : |(738315997/2500000000 : ℝ)|=(738315997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(722003707/1250000000 : ℝ)|^89 ≤ (51213423284377/100000000000000 : ℝ)^73
        have hw : |(722003707/1250000000 : ℝ)|=(722003707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1665697123/5000000000 : ℝ)|^89 ≤ (1309079809721/5000000000000 : ℝ)^73
        have hw : |(1665697123/5000000000 : ℝ)|=(1665697123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (786679041/2500000000 : ℝ)*x 0 + (655801641/1250000000 : ℝ)*x 1 + (-745597827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (786679041/2500000000 : ℝ)^89 ≤ (6105749254577/25000000000000 : ℝ)^73 := by
    have hnat : (786679041 : ℕ)^89*25000000000000^73 ≤ 6105749254577^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786679041 2500000000 6105749254577 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655801641/1250000000 : ℝ)^89 ≤ (182189135179/400000000000 : ℝ)^73 := by
    have hnat : (655801641 : ℕ)^89*400000000000^73 ≤ 182189135179^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655801641 1250000000 182189135179 400000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745597827/2000000000 : ℝ)^89 ≤ (938428724333/3125000000000 : ℝ)^73 := by
    have hnat : (745597827 : ℕ)^89*3125000000000^73 ≤ 938428724333^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745597827 2000000000 938428724333 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(786679041/2500000000 : ℝ), (655801641/1250000000 : ℝ), (-745597827/2000000000 : ℝ)] ![(6105749254577/25000000000000 : ℝ), (182189135179/400000000000 : ℝ), (938428724333/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(786679041/2500000000 : ℝ)|^89 ≤ (6105749254577/25000000000000 : ℝ)^73
        have hw : |(786679041/2500000000 : ℝ)|=(786679041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655801641/1250000000 : ℝ)|^89 ≤ (182189135179/400000000000 : ℝ)^73
        have hw : |(655801641/1250000000 : ℝ)|=(655801641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-745597827/2000000000 : ℝ)|^89 ≤ (938428724333/3125000000000 : ℝ)^73
        have hw : |(-745597827/2000000000 : ℝ)|=(745597827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-882229113/5000000000 : ℝ)*x 0 + (3305266969/10000000000 : ℝ)*x 1 + (-1351361493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882229113/5000000000 : ℝ)^89 ≤ (12063827207293/100000000000000 : ℝ)^73 := by
    have hnat : (882229113 : ℕ)^89*100000000000000^73 ≤ 12063827207293^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882229113 5000000000 12063827207293 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3305266969/10000000000 : ℝ)^89 ≤ (2593147114209/10000000000000 : ℝ)^73 := by
    have hnat : (3305266969 : ℕ)^89*10000000000000^73 ≤ 2593147114209^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3305266969 10000000000 2593147114209 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351361493/2000000000 : ℝ)^89 ≤ (2480188065301/4000000000000 : ℝ)^73 := by
    have hnat : (1351361493 : ℕ)^89*4000000000000^73 ≤ 2480188065301^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351361493 2000000000 2480188065301 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882229113/5000000000 : ℝ), (3305266969/10000000000 : ℝ), (-1351361493/2000000000 : ℝ)] ![(12063827207293/100000000000000 : ℝ), (2593147114209/10000000000000 : ℝ), (2480188065301/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882229113/5000000000 : ℝ)|^89 ≤ (12063827207293/100000000000000 : ℝ)^73
        have hw : |(-882229113/5000000000 : ℝ)|=(882229113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3305266969/10000000000 : ℝ)|^89 ≤ (2593147114209/10000000000000 : ℝ)^73
        have hw : |(3305266969/10000000000 : ℝ)|=(3305266969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1351361493/2000000000 : ℝ)|^89 ≤ (2480188065301/4000000000000 : ℝ)^73
        have hw : |(-1351361493/2000000000 : ℝ)|=(1351361493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (63216531/80000000 : ℝ)*x 0 + (-595494329/10000000000 : ℝ)*x 1 + (-2860796239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63216531/80000000 : ℝ)^89 ≤ (9380752617317/12500000000000 : ℝ)^73 := by
    have hnat : (63216531 : ℕ)^89*12500000000000^73 ≤ 9380752617317^73*80000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63216531 80000000 9380752617317 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595494329/10000000000 : ℝ)^89 ≤ (1604455450021/50000000000000 : ℝ)^73 := by
    have hnat : (595494329 : ℕ)^89*50000000000000^73 ≤ 1604455450021^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595494329 10000000000 1604455450021 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2860796239/10000000000 : ℝ)^89 ≤ (5436267036141/25000000000000 : ℝ)^73 := by
    have hnat : (2860796239 : ℕ)^89*25000000000000^73 ≤ 5436267036141^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860796239 10000000000 5436267036141 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63216531/80000000 : ℝ), (-595494329/10000000000 : ℝ), (-2860796239/10000000000 : ℝ)] ![(9380752617317/12500000000000 : ℝ), (1604455450021/50000000000000 : ℝ), (5436267036141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63216531/80000000 : ℝ)|^89 ≤ (9380752617317/12500000000000 : ℝ)^73
        have hw : |(63216531/80000000 : ℝ)|=(63216531/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-595494329/10000000000 : ℝ)|^89 ≤ (1604455450021/50000000000000 : ℝ)^73
        have hw : |(-595494329/10000000000 : ℝ)|=(595494329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2860796239/10000000000 : ℝ)|^89 ≤ (5436267036141/25000000000000 : ℝ)^73
        have hw : |(-2860796239/10000000000 : ℝ)|=(2860796239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (933025769/5000000000 : ℝ)*x 0 + (56552243/80000000 : ℝ)*x 1 + (71043883/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933025769/5000000000 : ℝ)^89 ≤ (12915941658253/100000000000000 : ℝ)^73 := by
    have hnat : (933025769 : ℕ)^89*100000000000000^73 ≤ 12915941658253^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933025769 5000000000 12915941658253 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56552243/80000000 : ℝ)^89 ≤ (65515314194817/100000000000000 : ℝ)^73 := by
    have hnat : (56552243 : ℕ)^89*100000000000000^73 ≤ 65515314194817^73*80000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56552243 80000000 65515314194817 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71043883/250000000 : ℝ)^89 ≤ (10784372066813/50000000000000 : ℝ)^73 := by
    have hnat : (71043883 : ℕ)^89*50000000000000^73 ≤ 10784372066813^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71043883 250000000 10784372066813 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(933025769/5000000000 : ℝ), (56552243/80000000 : ℝ), (71043883/250000000 : ℝ)] ![(12915941658253/100000000000000 : ℝ), (65515314194817/100000000000000 : ℝ), (10784372066813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(933025769/5000000000 : ℝ)|^89 ≤ (12915941658253/100000000000000 : ℝ)^73
        have hw : |(933025769/5000000000 : ℝ)|=(933025769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56552243/80000000 : ℝ)|^89 ≤ (65515314194817/100000000000000 : ℝ)^73
        have hw : |(56552243/80000000 : ℝ)|=(56552243/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71043883/250000000 : ℝ)|^89 ≤ (10784372066813/50000000000000 : ℝ)^73
        have hw : |(71043883/250000000 : ℝ)|=(71043883/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2541588107/10000000000 : ℝ)*x 0 + (1742278151/2500000000 : ℝ)*x 1 + (-2313761221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2541588107/10000000000 : ℝ)^89 ≤ (94121158893/500000000000 : ℝ)^73 := by
    have hnat : (2541588107 : ℕ)^89*500000000000^73 ≤ 94121158893^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541588107 10000000000 94121158893 500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1742278151/2500000000 : ℝ)^89 ≤ (64388072282607/100000000000000 : ℝ)^73 := by
    have hnat : (1742278151 : ℕ)^89*100000000000000^73 ≤ 64388072282607^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742278151 2500000000 64388072282607 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2313761221/10000000000 : ℝ)^89 ≤ (8393847961931/50000000000000 : ℝ)^73 := by
    have hnat : (2313761221 : ℕ)^89*50000000000000^73 ≤ 8393847961931^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313761221 10000000000 8393847961931 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2541588107/10000000000 : ℝ), (1742278151/2500000000 : ℝ), (-2313761221/10000000000 : ℝ)] ![(94121158893/500000000000 : ℝ), (64388072282607/100000000000000 : ℝ), (8393847961931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2541588107/10000000000 : ℝ)|^89 ≤ (94121158893/500000000000 : ℝ)^73
        have hw : |(2541588107/10000000000 : ℝ)|=(2541588107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1742278151/2500000000 : ℝ)|^89 ≤ (64388072282607/100000000000000 : ℝ)^73
        have hw : |(1742278151/2500000000 : ℝ)|=(1742278151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2313761221/10000000000 : ℝ)|^89 ≤ (8393847961931/50000000000000 : ℝ)^73
        have hw : |(-2313761221/10000000000 : ℝ)|=(2313761221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-543901653/10000000000 : ℝ)*x 0 + (3660872783/10000000000 : ℝ)*x 1 + (-7266631413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543901653/10000000000 : ℝ)^89 ≤ (287325492861/10000000000000 : ℝ)^73 := by
    have hnat : (543901653 : ℕ)^89*10000000000000^73 ≤ 287325492861^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543901653 10000000000 287325492861 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3660872783/10000000000 : ℝ)^89 ≤ (29371894185367/100000000000000 : ℝ)^73 := by
    have hnat : (3660872783 : ℕ)^89*100000000000000^73 ≤ 29371894185367^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660872783 10000000000 29371894185367 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7266631413/10000000000 : ℝ)^89 ≤ (13550970174059/20000000000000 : ℝ)^73 := by
    have hnat : (7266631413 : ℕ)^89*20000000000000^73 ≤ 13550970174059^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7266631413 10000000000 13550970174059 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543901653/10000000000 : ℝ), (3660872783/10000000000 : ℝ), (-7266631413/10000000000 : ℝ)] ![(287325492861/10000000000000 : ℝ), (29371894185367/100000000000000 : ℝ), (13550970174059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543901653/10000000000 : ℝ)|^89 ≤ (287325492861/10000000000000 : ℝ)^73
        have hw : |(-543901653/10000000000 : ℝ)|=(543901653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3660872783/10000000000 : ℝ)|^89 ≤ (29371894185367/100000000000000 : ℝ)^73
        have hw : |(3660872783/10000000000 : ℝ)|=(3660872783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7266631413/10000000000 : ℝ)|^89 ≤ (13550970174059/20000000000000 : ℝ)^73
        have hw : |(-7266631413/10000000000 : ℝ)|=(7266631413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4246310307/5000000000 : ℝ)*x 0 + (-1569743687/10000000000 : ℝ)*x 1 + (-75493519/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246310307/5000000000 : ℝ)^89 ≤ (81938729283813/100000000000000 : ℝ)^73 := by
    have hnat : (4246310307 : ℕ)^89*100000000000000^73 ≤ 81938729283813^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246310307 5000000000 81938729283813 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1569743687/10000000000 : ℝ)^89 ≤ (2092194361899/20000000000000 : ℝ)^73 := by
    have hnat : (1569743687 : ℕ)^89*20000000000000^73 ≤ 2092194361899^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569743687 10000000000 2092194361899 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75493519/625000000 : ℝ)^89 ≤ (3800149448231/50000000000000 : ℝ)^73 := by
    have hnat : (75493519 : ℕ)^89*50000000000000^73 ≤ 3800149448231^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75493519 625000000 3800149448231 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246310307/5000000000 : ℝ), (-1569743687/10000000000 : ℝ), (-75493519/625000000 : ℝ)] ![(81938729283813/100000000000000 : ℝ), (2092194361899/20000000000000 : ℝ), (3800149448231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246310307/5000000000 : ℝ)|^89 ≤ (81938729283813/100000000000000 : ℝ)^73
        have hw : |(4246310307/5000000000 : ℝ)|=(4246310307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1569743687/10000000000 : ℝ)|^89 ≤ (2092194361899/20000000000000 : ℝ)^73
        have hw : |(-1569743687/10000000000 : ℝ)|=(1569743687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75493519/625000000 : ℝ)|^89 ≤ (3800149448231/50000000000000 : ℝ)^73
        have hw : |(-75493519/625000000 : ℝ)|=(75493519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (83251929/250000000 : ℝ)*x 0 + (5806318961/10000000000 : ℝ)*x 1 + (583893393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83251929/250000000 : ℝ)^89 ≤ (13084488486653/50000000000000 : ℝ)^73 := by
    have hnat : (83251929 : ℕ)^89*50000000000000^73 ≤ 13084488486653^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83251929 250000000 13084488486653 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5806318961/10000000000 : ℝ)^89 ≤ (51541035447041/100000000000000 : ℝ)^73 := by
    have hnat : (5806318961 : ℕ)^89*100000000000000^73 ≤ 51541035447041^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5806318961 10000000000 51541035447041 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583893393/2000000000 : ℝ)^89 ≤ (11144993785027/50000000000000 : ℝ)^73 := by
    have hnat : (583893393 : ℕ)^89*50000000000000^73 ≤ 11144993785027^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583893393 2000000000 11144993785027 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83251929/250000000 : ℝ), (5806318961/10000000000 : ℝ), (583893393/2000000000 : ℝ)] ![(13084488486653/50000000000000 : ℝ), (51541035447041/100000000000000 : ℝ), (11144993785027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83251929/250000000 : ℝ)|^89 ≤ (13084488486653/50000000000000 : ℝ)^73
        have hw : |(83251929/250000000 : ℝ)|=(83251929/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5806318961/10000000000 : ℝ)|^89 ≤ (51541035447041/100000000000000 : ℝ)^73
        have hw : |(5806318961/10000000000 : ℝ)|=(5806318961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(583893393/2000000000 : ℝ)|^89 ≤ (11144993785027/50000000000000 : ℝ)^73
        have hw : |(583893393/2000000000 : ℝ)|=(583893393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2603666341/10000000000 : ℝ)*x 0 + (3809381519/10000000000 : ℝ)*x 1 + (-5643346831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2603666341/10000000000 : ℝ)^89 ≤ (19386278253197/100000000000000 : ℝ)^73 := by
    have hnat : (2603666341 : ℕ)^89*100000000000000^73 ≤ 19386278253197^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603666341 10000000000 19386278253197 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3809381519/10000000000 : ℝ)^89 ≤ (30830953568169/100000000000000 : ℝ)^73 := by
    have hnat : (3809381519 : ℕ)^89*100000000000000^73 ≤ 30830953568169^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3809381519 10000000000 30830953568169 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5643346831/10000000000 : ℝ)^89 ≤ (49782768157663/100000000000000 : ℝ)^73 := by
    have hnat : (5643346831 : ℕ)^89*100000000000000^73 ≤ 49782768157663^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643346831 10000000000 49782768157663 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2603666341/10000000000 : ℝ), (3809381519/10000000000 : ℝ), (-5643346831/10000000000 : ℝ)] ![(19386278253197/100000000000000 : ℝ), (30830953568169/100000000000000 : ℝ), (49782768157663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2603666341/10000000000 : ℝ)|^89 ≤ (19386278253197/100000000000000 : ℝ)^73
        have hw : |(2603666341/10000000000 : ℝ)|=(2603666341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3809381519/10000000000 : ℝ)|^89 ≤ (30830953568169/100000000000000 : ℝ)^73
        have hw : |(3809381519/10000000000 : ℝ)|=(3809381519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5643346831/10000000000 : ℝ)|^89 ≤ (49782768157663/100000000000000 : ℝ)^73
        have hw : |(-5643346831/10000000000 : ℝ)|=(5643346831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-605065823/10000000000 : ℝ)*x 0 + (508746479/1000000000 : ℝ)*x 1 + (-5927691591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (605065823/10000000000 : ℝ)^89 ≤ (204493955277/6250000000000 : ℝ)^73 := by
    have hnat : (605065823 : ℕ)^89*6250000000000^73 ≤ 204493955277^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605065823 10000000000 204493955277 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508746479/1000000000 : ℝ)^89 ≤ (21935268975897/50000000000000 : ℝ)^73 := by
    have hnat : (508746479 : ℕ)^89*50000000000000^73 ≤ 21935268975897^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508746479 1000000000 21935268975897 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5927691591/10000000000 : ℝ)^89 ≤ (26428779376643/50000000000000 : ℝ)^73 := by
    have hnat : (5927691591 : ℕ)^89*50000000000000^73 ≤ 26428779376643^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5927691591 10000000000 26428779376643 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-605065823/10000000000 : ℝ), (508746479/1000000000 : ℝ), (-5927691591/10000000000 : ℝ)] ![(204493955277/6250000000000 : ℝ), (21935268975897/50000000000000 : ℝ), (26428779376643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-605065823/10000000000 : ℝ)|^89 ≤ (204493955277/6250000000000 : ℝ)^73
        have hw : |(-605065823/10000000000 : ℝ)|=(605065823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508746479/1000000000 : ℝ)|^89 ≤ (21935268975897/50000000000000 : ℝ)^73
        have hw : |(508746479/1000000000 : ℝ)|=(508746479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5927691591/10000000000 : ℝ)|^89 ≤ (26428779376643/50000000000000 : ℝ)^73
        have hw : |(-5927691591/10000000000 : ℝ)|=(5927691591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2253866137/2500000000 : ℝ)*x 0 + (-38442967/625000000 : ℝ)*x 1 + (-1328092901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2253866137/2500000000 : ℝ)^89 ≤ (22032435066253/25000000000000 : ℝ)^73 := by
    have hnat : (2253866137 : ℕ)^89*25000000000000^73 ≤ 22032435066253^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253866137 2500000000 22032435066253 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38442967/625000000 : ℝ)^89 ≤ (3338092674821/100000000000000 : ℝ)^73 := by
    have hnat : (38442967 : ℕ)^89*100000000000000^73 ≤ 3338092674821^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38442967 625000000 3338092674821 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328092901/10000000000 : ℝ)^89 ≤ (1066520880641/12500000000000 : ℝ)^73 := by
    have hnat : (1328092901 : ℕ)^89*12500000000000^73 ≤ 1066520880641^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328092901 10000000000 1066520880641 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2253866137/2500000000 : ℝ), (-38442967/625000000 : ℝ), (-1328092901/10000000000 : ℝ)] ![(22032435066253/25000000000000 : ℝ), (3338092674821/100000000000000 : ℝ), (1066520880641/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2253866137/2500000000 : ℝ)|^89 ≤ (22032435066253/25000000000000 : ℝ)^73
        have hw : |(2253866137/2500000000 : ℝ)|=(2253866137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38442967/625000000 : ℝ)|^89 ≤ (3338092674821/100000000000000 : ℝ)^73
        have hw : |(-38442967/625000000 : ℝ)|=(38442967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1328092901/10000000000 : ℝ)|^89 ≤ (1066520880641/12500000000000 : ℝ)^73
        have hw : |(-1328092901/10000000000 : ℝ)|=(1328092901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2509000739/10000000000 : ℝ)*x 0 + (1428378411/2500000000 : ℝ)*x 1 + (1909767777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2509000739/10000000000 : ℝ)^89 ≤ (4632597116633/25000000000000 : ℝ)^73 := by
    have hnat : (2509000739 : ℕ)^89*25000000000000^73 ≤ 4632597116633^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509000739 10000000000 4632597116633 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428378411/2500000000 : ℝ)^89 ≤ (12634608875031/25000000000000 : ℝ)^73 := by
    have hnat : (1428378411 : ℕ)^89*25000000000000^73 ≤ 12634608875031^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428378411 2500000000 12634608875031 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1909767777/5000000000 : ℝ)^89 ≤ (30931176025299/100000000000000 : ℝ)^73 := by
    have hnat : (1909767777 : ℕ)^89*100000000000000^73 ≤ 30931176025299^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909767777 5000000000 30931176025299 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2509000739/10000000000 : ℝ), (1428378411/2500000000 : ℝ), (1909767777/5000000000 : ℝ)] ![(4632597116633/25000000000000 : ℝ), (12634608875031/25000000000000 : ℝ), (30931176025299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2509000739/10000000000 : ℝ)|^89 ≤ (4632597116633/25000000000000 : ℝ)^73
        have hw : |(2509000739/10000000000 : ℝ)|=(2509000739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1428378411/2500000000 : ℝ)|^89 ≤ (12634608875031/25000000000000 : ℝ)^73
        have hw : |(1428378411/2500000000 : ℝ)|=(1428378411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1909767777/5000000000 : ℝ)|^89 ≤ (30931176025299/100000000000000 : ℝ)^73
        have hw : |(1909767777/5000000000 : ℝ)|=(1909767777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s0_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3344577597/10000000000 : ℝ)*x 0 + (1114873971/2000000000 : ℝ)*x 1 + (-1585348827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3344577597/10000000000 : ℝ)^89 ≤ (26307968282069/100000000000000 : ℝ)^73 := by
    have hnat : (3344577597 : ℕ)^89*100000000000000^73 ≤ 26307968282069^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3344577597 10000000000 26307968282069 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114873971/2000000000 : ℝ)^89 ≤ (24520959648667/50000000000000 : ℝ)^73 := by
    have hnat : (1114873971 : ℕ)^89*50000000000000^73 ≤ 24520959648667^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114873971 2000000000 24520959648667 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585348827/5000000000 : ℝ)^89 ≤ (12325056199309/50000000000000 : ℝ)^73 := by
    have hnat : (1585348827 : ℕ)^89*50000000000000^73 ≤ 12325056199309^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585348827 5000000000 12325056199309 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3344577597/10000000000 : ℝ), (1114873971/2000000000 : ℝ), (-1585348827/5000000000 : ℝ)] ![(26307968282069/100000000000000 : ℝ), (24520959648667/50000000000000 : ℝ), (12325056199309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3344577597/10000000000 : ℝ)|^89 ≤ (26307968282069/100000000000000 : ℝ)^73
        have hw : |(3344577597/10000000000 : ℝ)|=(3344577597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1114873971/2000000000 : ℝ)|^89 ≤ (24520959648667/50000000000000 : ℝ)^73
        have hw : |(1114873971/2000000000 : ℝ)|=(1114873971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1585348827/5000000000 : ℝ)|^89 ≤ (12325056199309/50000000000000 : ℝ)^73
        have hw : |(-1585348827/5000000000 : ℝ)|=(1585348827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-146887921/625000000 : ℝ)*x 0 + (2118788279/5000000000 : ℝ)*x 1 + (-2728347267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (146887921/625000000 : ℝ)^89 ≤ (17110641829549/100000000000000 : ℝ)^73 := by
    have hnat : (146887921 : ℕ)^89*100000000000000^73 ≤ 17110641829549^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146887921 625000000 17110641829549 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118788279/5000000000 : ℝ)^89 ≤ (17553345583587/50000000000000 : ℝ)^73 := by
    have hnat : (2118788279 : ℕ)^89*50000000000000^73 ≤ 17553345583587^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118788279 5000000000 17553345583587 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728347267/5000000000 : ℝ)^89 ≤ (2389133349449/5000000000000 : ℝ)^73 := by
    have hnat : (2728347267 : ℕ)^89*5000000000000^73 ≤ 2389133349449^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728347267 5000000000 2389133349449 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-146887921/625000000 : ℝ), (2118788279/5000000000 : ℝ), (-2728347267/5000000000 : ℝ)] ![(17110641829549/100000000000000 : ℝ), (17553345583587/50000000000000 : ℝ), (2389133349449/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-146887921/625000000 : ℝ)|^89 ≤ (17110641829549/100000000000000 : ℝ)^73
        have hw : |(-146887921/625000000 : ℝ)|=(146887921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118788279/5000000000 : ℝ)|^89 ≤ (17553345583587/50000000000000 : ℝ)^73
        have hw : |(2118788279/5000000000 : ℝ)|=(2118788279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2728347267/5000000000 : ℝ)|^89 ≤ (2389133349449/5000000000000 : ℝ)^73
        have hw : |(-2728347267/5000000000 : ℝ)|=(2728347267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6413121173/10000000000 : ℝ)*x 0 + (-2437719413/10000000000 : ℝ)*x 1 + (-773581343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6413121173/10000000000 : ℝ)^89 ≤ (11636256678949/20000000000000 : ℝ)^73 := by
    have hnat : (6413121173 : ℕ)^89*20000000000000^73 ≤ 11636256678949^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6413121173 10000000000 11636256678949 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2437719413/10000000000 : ℝ)^89 ≤ (8945280979703/50000000000000 : ℝ)^73 := by
    have hnat : (2437719413 : ℕ)^89*50000000000000^73 ≤ 8945280979703^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437719413 10000000000 8945280979703 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773581343/2500000000 : ℝ)^89 ≤ (23928154625623/100000000000000 : ℝ)^73 := by
    have hnat : (773581343 : ℕ)^89*100000000000000^73 ≤ 23928154625623^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773581343 2500000000 23928154625623 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6413121173/10000000000 : ℝ), (-2437719413/10000000000 : ℝ), (-773581343/2500000000 : ℝ)] ![(11636256678949/20000000000000 : ℝ), (8945280979703/50000000000000 : ℝ), (23928154625623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6413121173/10000000000 : ℝ)|^89 ≤ (11636256678949/20000000000000 : ℝ)^73
        have hw : |(6413121173/10000000000 : ℝ)|=(6413121173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2437719413/10000000000 : ℝ)|^89 ≤ (8945280979703/50000000000000 : ℝ)^73
        have hw : |(-2437719413/10000000000 : ℝ)|=(2437719413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-773581343/2500000000 : ℝ)|^89 ≤ (23928154625623/100000000000000 : ℝ)^73
        have hw : |(-773581343/2500000000 : ℝ)|=(773581343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3459215421/10000000000 : ℝ)*x 0 + (5102924443/10000000000 : ℝ)*x 1 + (3577195623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3459215421/10000000000 : ℝ)^89 ≤ (27411424463021/100000000000000 : ℝ)^73 := by
    have hnat : (3459215421 : ℕ)^89*100000000000000^73 ≤ 27411424463021^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3459215421 10000000000 27411424463021 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5102924443/10000000000 : ℝ)^89 ≤ (22016561933581/50000000000000 : ℝ)^73 := by
    have hnat : (5102924443 : ℕ)^89*50000000000000^73 ≤ 22016561933581^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5102924443 10000000000 22016561933581 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3577195623/10000000000 : ℝ)^89 ≤ (7138862916341/25000000000000 : ℝ)^73 := by
    have hnat : (3577195623 : ℕ)^89*25000000000000^73 ≤ 7138862916341^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3577195623 10000000000 7138862916341 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3459215421/10000000000 : ℝ), (5102924443/10000000000 : ℝ), (3577195623/10000000000 : ℝ)] ![(27411424463021/100000000000000 : ℝ), (22016561933581/50000000000000 : ℝ), (7138862916341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3459215421/10000000000 : ℝ)|^89 ≤ (27411424463021/100000000000000 : ℝ)^73
        have hw : |(3459215421/10000000000 : ℝ)|=(3459215421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5102924443/10000000000 : ℝ)|^89 ≤ (22016561933581/50000000000000 : ℝ)^73
        have hw : |(5102924443/10000000000 : ℝ)|=(5102924443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3577195623/10000000000 : ℝ)|^89 ≤ (7138862916341/25000000000000 : ℝ)^73
        have hw : |(3577195623/10000000000 : ℝ)|=(3577195623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326079_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1748652237/5000000000 : ℝ)*x 0 + (60872843/125000000 : ℝ)*x 1 + (-3788684749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748652237/5000000000 : ℝ)^89 ≤ (6944961192647/25000000000000 : ℝ)^73 := by
    have hnat : (1748652237 : ℕ)^89*25000000000000^73 ≤ 6944961192647^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748652237 5000000000 6944961192647 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60872843/125000000 : ℝ)^89 ≤ (41593301728431/100000000000000 : ℝ)^73 := by
    have hnat : (60872843 : ℕ)^89*100000000000000^73 ≤ 41593301728431^73*125000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60872843 125000000 41593301728431 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3788684749/10000000000 : ℝ)^89 ≤ (3062685348573/10000000000000 : ℝ)^73 := by
    have hnat : (3788684749 : ℕ)^89*10000000000000^73 ≤ 3062685348573^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3788684749 10000000000 3062685348573 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1748652237/5000000000 : ℝ), (60872843/125000000 : ℝ), (-3788684749/10000000000 : ℝ)] ![(6944961192647/25000000000000 : ℝ), (41593301728431/100000000000000 : ℝ), (3062685348573/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1748652237/5000000000 : ℝ)|^89 ≤ (6944961192647/25000000000000 : ℝ)^73
        have hw : |(1748652237/5000000000 : ℝ)|=(1748652237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60872843/125000000 : ℝ)|^89 ≤ (41593301728431/100000000000000 : ℝ)^73
        have hw : |(60872843/125000000 : ℝ)|=(60872843/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3788684749/10000000000 : ℝ)|^89 ≤ (3062685348573/10000000000000 : ℝ)^73
        have hw : |(-3788684749/10000000000 : ℝ)|=(3788684749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326079 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((387074263/500000000 : ℝ)*X 1 0+(-1498029651/10000000000 : ℝ)*X 1 1+(-3727349/16000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((738315997/2500000000 : ℝ)*X 2 0+(722003707/1250000000 : ℝ)*X 2 1+(1665697123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((786679041/2500000000 : ℝ)*X 0 0+(655801641/1250000000 : ℝ)*X 0 1+(-745597827/2000000000 : ℝ)*X 0 2+(786679041/2500000000 : ℝ)*X 1 0+(655801641/1250000000 : ℝ)*X 1 1+(-745597827/2000000000 : ℝ)*X 1 2+(786679041/2500000000 : ℝ)*X 2 0+(655801641/1250000000 : ℝ)*X 2 1+(-745597827/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-882229113/5000000000 : ℝ)*X 0 0+(3305266969/10000000000 : ℝ)*X 0 1+(-1351361493/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((63216531/80000000 : ℝ)*X 1 0+(-595494329/10000000000 : ℝ)*X 1 1+(-2860796239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((933025769/5000000000 : ℝ)*X 2 0+(56552243/80000000 : ℝ)*X 2 1+(71043883/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2541588107/10000000000 : ℝ)*X 0 0+(1742278151/2500000000 : ℝ)*X 0 1+(-2313761221/10000000000 : ℝ)*X 0 2+(2541588107/10000000000 : ℝ)*X 1 0+(1742278151/2500000000 : ℝ)*X 1 1+(-2313761221/10000000000 : ℝ)*X 1 2+(2541588107/10000000000 : ℝ)*X 2 0+(1742278151/2500000000 : ℝ)*X 2 1+(-2313761221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-543901653/10000000000 : ℝ)*X 0 0+(3660872783/10000000000 : ℝ)*X 0 1+(-7266631413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4246310307/5000000000 : ℝ)*X 1 0+(-1569743687/10000000000 : ℝ)*X 1 1+(-75493519/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((83251929/250000000 : ℝ)*X 2 0+(5806318961/10000000000 : ℝ)*X 2 1+(583893393/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2603666341/10000000000 : ℝ)*X 0 0+(3809381519/10000000000 : ℝ)*X 0 1+(-5643346831/10000000000 : ℝ)*X 0 2+(2603666341/10000000000 : ℝ)*X 1 0+(3809381519/10000000000 : ℝ)*X 1 1+(-5643346831/10000000000 : ℝ)*X 1 2+(2603666341/10000000000 : ℝ)*X 2 0+(3809381519/10000000000 : ℝ)*X 2 1+(-5643346831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-605065823/10000000000 : ℝ)*X 0 0+(508746479/1000000000 : ℝ)*X 0 1+(-5927691591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2253866137/2500000000 : ℝ)*X 1 0+(-38442967/625000000 : ℝ)*X 1 1+(-1328092901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2509000739/10000000000 : ℝ)*X 2 0+(1428378411/2500000000 : ℝ)*X 2 1+(1909767777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((3344577597/10000000000 : ℝ)*X 0 0+(1114873971/2000000000 : ℝ)*X 0 1+(-1585348827/5000000000 : ℝ)*X 0 2+(3344577597/10000000000 : ℝ)*X 1 0+(1114873971/2000000000 : ℝ)*X 1 1+(-1585348827/5000000000 : ℝ)*X 1 2+(3344577597/10000000000 : ℝ)*X 2 0+(1114873971/2000000000 : ℝ)*X 2 1+(-1585348827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1481/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1481/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1361093112143423036691/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3672847/1000000000000 : ℝ)*(base18) + (268432818403/200000000000 : ℝ)*(base39) + (1616834882639/1000000000000 : ℝ)*(base49) + (913036946773/1000000000000 : ℝ)*(base60) + (146517748451/40000000000 : ℝ)*(major_s0_0) + (146517748451/40000000000 : ℝ)*(major_s0_1) + (146517748451/40000000000 : ℝ)*(major_s0_2) + (2517859/125000000000 : ℝ)*(sp_s0_1) + (3488653/1000000000000 : ℝ)*(sp_s0_6) + (5550012273643/1000000000000 : ℝ)*(sp_s0_7) + (5550017782099/1000000000000 : ℝ)*(sp_s0_8) + (2775020798909/500000000000 : ℝ)*(sp_s0_9) + (355168013517/200000000000 : ℝ)*(sp_s0_13) + (1172967/40000000000 : ℝ)*(sp_s0_14) + (887921778119/500000000000 : ℝ)*(f.failure) + (2775020798909/500000000000 : ℝ)*(f.sum) + (128181613040403/400000000000000000000000000 : ℝ)*base62 + (87037714810753/400000000000000000000000000 : ℝ)*base65 + (319557555407/8000000000000000000000000 : ℝ)*base66 + (986383102193/8000000000000000000000000 : ℝ)*base68 + (106835674381103/400000000000000000000000000 : ℝ)*base71 + (96410600509247/400000000000000000000000000 : ℝ)*base72 + (160095626290753/400000000000000000000000000 : ℝ)*base74 + (1778006384207/8000000000000000000000000 : ℝ)*base77 + (80545803519597/400000000000000000000000000 : ℝ)*base78 + (6893/10000000000000000 : ℝ)*base86 + (6893/10000000000000000 : ℝ)*base88 + (6893/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((29961/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(29961/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1681933968275338805589/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1908239587051/1000000000000 : ℝ)*(base39) + (33301/20000000000 : ℝ)*(base40) + (1178437411071/1000000000000 : ℝ)*(base49) + (290215253703/250000000000 : ℝ)*(base60) + (2094943902859/500000000000 : ℝ)*(major_s0_0) + (2094943902859/500000000000 : ℝ)*(major_s0_1) + (2094943902859/500000000000 : ℝ)*(major_s0_2) + (3362361/125000000000 : ℝ)*(sp_s0_1) + (20833323/1000000000000 : ℝ)*(sp_s0_7) + (1587109990403/250000000000 : ℝ)*(sp_s0_14) + (6348399627117/1000000000000 : ℝ)*(sp_s0_15) + (1269692158987/200000000000 : ℝ)*(sp_s0_16) + (2031313022431/1000000000000 : ℝ)*(sp_s0_20) + (3426893/100000000000 : ℝ)*(sp_s0_22) + (2031313022431/1000000000000 : ℝ)*(f.failure) + (1269692158987/200000000000 : ℝ)*(f.sum) + (2250593972135973/5000000000000000000000000000 : ℝ)*base63 + (674867967722823/5000000000000000000000000000 : ℝ)*base64 + (18881641058263/100000000000000000000000000 : ℝ)*base66 + (27488348888263/100000000000000000000000000 : ℝ)*base69 + (1443107946190327/5000000000000000000000000000 : ℝ)*base71 + (3766408202222823/5000000000000000000000000000 : ℝ)*base72 + (1151994746222823/5000000000000000000000000000 : ℝ)*base75 + (46372889938263/100000000000000000000000000 : ℝ)*base77 + (4132164697635973/5000000000000000000000000000 : ℝ)*base78 + (13957/20000000000000000 : ℝ)*base86 + (13957/20000000000000000 : ℝ)*base88 + (13957/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-24347/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-24347/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4244495005521373266537/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5043693/1000000000000 : ℝ)*(base11) + (1369659114011/1000000000000 : ℝ)*(base39) + (107061484553/100000000000 : ℝ)*(base49) + (1484043/1000000000000 : ℝ)*(base50) + (67821346359/500000000000 : ℝ)*(base60) + (361944256257/125000000000 : ℝ)*(major_s0_0) + (361944256257/125000000000 : ℝ)*(major_s0_1) + (361944256257/125000000000 : ℝ)*(major_s0_2) + (5938523/40000000000 : ℝ)*(sp_s0_2) + (12003213/1000000000000 : ℝ)*(sp_s0_13) + (2193647814871/500000000000 : ℝ)*(sp_s0_21) + (2193650336717/500000000000 : ℝ)*(sp_s0_22) + (4387152210359/1000000000000 : ℝ)*(sp_s0_23) + (1403790895997/1000000000000 : ℝ)*(sp_s0_27) + (140380289921/100000000000 : ℝ)*(f.failure) + (2193650336717/500000000000 : ℝ)*(f.sum) + (776780853869121/1250000000000000000000000000 : ℝ)*base62 + (25226649171571/1250000000000000000000000000 : ℝ)*base65 + (7298041673951/25000000000000000000000000 : ℝ)*base67 + (11285480328549/25000000000000000000000000 : ℝ)*base69 + (339574148099021/1250000000000000000000000000 : ℝ)*base71 + (143156174328429/1250000000000000000000000000 : ℝ)*base72 + (289603732671571/1250000000000000000000000000 : ℝ)*base74 + (14367548701049/25000000000000000000000000 : ℝ)*base77 + (769701408994121/1250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (987/2000000000000000 : ℝ)*base86 + (987/2000000000000000 : ℝ)*base88 + (987/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (1481/6250 : ℝ) ^ (87/16 : ℝ) ≤ (39791978786632957/100000000000000000000 : ℝ) := by
    have hpowers : (1481/6250 : ℝ)^87 ≤ (39791978786632957/100000000000000000000 : ℝ)^16 := by
      have hnat : (1481 : ℕ)^87*100000000000000000000^16 ≤ 39791978786632957^16*6250^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1481 6250 39791978786632957 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1481/6250 : ℝ)) (X := (39791978786632957/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100039791978786632957/100000000000000000000 : ℝ) ≤ (10000731687711929/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (100039791978786632957/100000000000000000000 : ℝ)^16 ≤ (10000731687711929/10000000000000000 : ℝ)^87 := by
      have hnat : (100039791978786632957 : ℕ)^16*10000000000000000^87 ≤ 10000731687711929^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039791978786632957 100000000000000000000 10000731687711929 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000731687711929/10000000000000000 : ℝ)) (X := (100039791978786632957/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50039791978786632957/50000000000000000000 : ℝ) ≤ (1000146313794927/1000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50039791978786632957/50000000000000000000 : ℝ)^16 ≤ (1000146313794927/1000000000000000 : ℝ)^87 := by
      have hnat : (50039791978786632957 : ℕ)^16*1000000000000000^87 ≤ 1000146313794927^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039791978786632957 50000000000000000000 1000146313794927 1000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000146313794927/1000000000000000 : ℝ)) (X := (50039791978786632957/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(731687711929/2369600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(731450237341/2369600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1481/6250 : ℝ)) (alpha := (731687711929/2369600000000000 : ℝ)) (beta := (731450237341/2369600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1481/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(731687711929/2369600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(731450237341/2369600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (29961/100000 : ℝ) ^ (87/16 : ℝ) ≤ (142486889615008513/100000000000000000000 : ℝ) := by
    have hpowers : (29961/100000 : ℝ)^87 ≤ (142486889615008513/100000000000000000000 : ℝ)^16 := by
      have hnat : (29961 : ℕ)^87*100000000000000000000^16 ≤ 142486889615008513^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29961 100000 142486889615008513 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29961/100000 : ℝ)) (X := (142486889615008513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100142486889615008513/100000000000000000000 : ℝ) ≤ (2500654731574303/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (100142486889615008513/100000000000000000000 : ℝ)^16 ≤ (2500654731574303/2500000000000000 : ℝ)^87 := by
      have hnat : (100142486889615008513 : ℕ)^16*2500000000000000^87 ≤ 2500654731574303^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100142486889615008513 100000000000000000000 2500654731574303 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500654731574303/2500000000000000 : ℝ)) (X := (100142486889615008513/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50142486889615008513/50000000000000000000 : ℝ) ≤ (1250654351667557/1250000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50142486889615008513/50000000000000000000 : ℝ)^16 ≤ (1250654351667557/1250000000000000 : ℝ)^87 := by
      have hnat : (50142486889615008513 : ℕ)^16*1250000000000000^87 ≤ 1250654351667557^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50142486889615008513 50000000000000000000 1250654351667557 1250000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250654351667557/1250000000000000 : ℝ)) (X := (50142486889615008513/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(218243858101/249675000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(72663528979/83225000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (29961/100000 : ℝ)) (alpha := (218243858101/249675000000000 : ℝ)) (beta := (72663528979/83225000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (29961/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(218243858101/249675000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(72663528979/83225000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (24347/100000 : ℝ) ^ (87/16 : ℝ) ≤ (23055108476732617/50000000000000000000 : ℝ) := by
    have hpowers : (24347/100000 : ℝ)^87 ≤ (23055108476732617/50000000000000000000 : ℝ)^16 := by
      have hnat : (24347 : ℕ)^87*50000000000000000000^16 ≤ 23055108476732617^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24347 100000 23055108476732617 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24347/100000 : ℝ)) (X := (23055108476732617/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50023055108476732617/50000000000000000000 : ℝ) ≤ (1000084784448177/1000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50023055108476732617/50000000000000000000 : ℝ)^16 ≤ (1000084784448177/1000000000000000 : ℝ)^87 := by
      have hnat : (50023055108476732617 : ℕ)^16*1000000000000000^87 ≤ 1000084784448177^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023055108476732617 50000000000000000000 1000084784448177 1000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000084784448177/1000000000000000 : ℝ)) (X := (50023055108476732617/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25023055108476732617/25000000000000000000 : ℝ) ≤ (2000339074025031/2000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25023055108476732617/25000000000000000000 : ℝ)^16 ≤ (2000339074025031/2000000000000000 : ℝ)^87 := by
      have hnat : (25023055108476732617 : ℕ)^16*2000000000000000^87 ≤ 2000339074025031^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023055108476732617 25000000000000000000 2000339074025031 2000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000339074025031/2000000000000000 : ℝ)) (X := (25023055108476732617/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(84784448177/243470000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(169505128677/486940000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (24347/100000 : ℝ)) (alpha := (84784448177/243470000000000 : ℝ)) (beta := (169505128677/486940000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (24347/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(84784448177/243470000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(169505128677/486940000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-146887921/625000000 : ℝ)*X 0 0+(2118788279/5000000000 : ℝ)*X 0 1+(-2728347267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6413121173/10000000000 : ℝ)*X 1 0+(-2437719413/10000000000 : ℝ)*X 1 1+(-773581343/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3459215421/10000000000 : ℝ)*X 2 0+(5102924443/10000000000 : ℝ)*X 2 1+(3577195623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1748652237/5000000000 : ℝ)*X 0 0+(60872843/125000000 : ℝ)*X 0 1+(-3788684749/10000000000 : ℝ)*X 0 2+(1748652237/5000000000 : ℝ)*X 1 0+(60872843/125000000 : ℝ)*X 1 1+(-3788684749/10000000000 : ℝ)*X 1 2+(1748652237/5000000000 : ℝ)*X 2 0+(60872843/125000000 : ℝ)*X 2 1+(-3788684749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-1390485511350501725448662616365073/150045965503750000000000000000000 : ℝ) := by norm_num
    linear_combination (2773/200000000000 : ℝ)*(base1) + (2687/1000000000000 : ℝ)*(base3) + (13863/500000000000 : ℝ)*(base25) + (363650579163/500000000000 : ℝ)*(base39) + (321279849293/500000000000 : ℝ)*(base49) + (3339/500000000000 : ℝ)*(base50) + (2497/250000000000 : ℝ)*(base59) + (53477778807/200000000000 : ℝ)*(base60) + (41253/20000 : ℝ)*(major_s1_0) + (41253/20000 : ℝ)*(major_s1_1) + (41253/20000 : ℝ)*(major_s1_2) + (3089021227421/1000000000000 : ℝ)*(sp_s1_0) + (3089021216243/1000000000000 : ℝ)*(sp_s1_1) + (308902118583/100000000000 : ℝ)*(sp_s1_2) + (124999997931/125000000000 : ℝ)*(sp_s1_6) + (772255303389/250000000000 : ℝ)*(f.sum) + (3044286379067839/25328488437500000000000000000 : ℝ)*base62 + (112806165797593/121735000000000000000000000 : ℝ)*base64 + (7977273698707/16645000000000000000000000 : ℝ)*base67 + (109427752307323/243470000000000000000000000 : ℝ)*base69 + (392213763056988727/360579070000000000000000000000 : ℝ)*base70 + (6525102251/28925781250000000000000 : ℝ)*base72 + (5280426736639/16645000000000000000000000 : ℝ)*base74 + (152198399211/1481000000000000000000000 : ℝ)*base76 + (5783416915837769/24651245000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_b039 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 80)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=78 ∨ c=79 := by omega
  rcases hc with rfl|rfl
  · exact collision_c326078 p hpa (by linarith only [hpb]) X hX
  · exact collision_c326079 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 78 ≤ c.val) (hhi : c.val < 80)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b039 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

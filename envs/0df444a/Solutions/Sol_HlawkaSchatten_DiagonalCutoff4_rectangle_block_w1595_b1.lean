-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1595_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:45.797586+00:00
-- url     : https://prove2.me/submissions/ea0da522-50c7-495d-9367-b5eb9324ef04

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1595_s3_0 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-435650077/2500000000 : ℝ)*x 0 + (5464970607/10000000000 : ℝ)*x 1 + (2589237917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435650077/2500000000 : ℝ)^4699 ≤ (10709410127671/100000000000000 : ℝ)^3675 := by
    have hnat : (435650077 : ℕ)^4699*100000000000000^3675 ≤ 10709410127671^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435650077 2500000000 10709410127671 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464970607/10000000000 : ℝ)^4699 ≤ (5772706260879/12500000000000 : ℝ)^3675 := by
    have hnat : (5464970607 : ℕ)^4699*12500000000000^3675 ≤ 5772706260879^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464970607 10000000000 5772706260879 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589237917/5000000000 : ℝ)^4699 ≤ (8621787954203/20000000000000 : ℝ)^3675 := by
    have hnat : (2589237917 : ℕ)^4699*20000000000000^3675 ≤ 8621787954203^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589237917 5000000000 8621787954203 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435650077/2500000000 : ℝ), (5464970607/10000000000 : ℝ), (2589237917/5000000000 : ℝ)] ![(10709410127671/100000000000000 : ℝ), (5772706260879/12500000000000 : ℝ), (8621787954203/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435650077/2500000000 : ℝ)|^4699 ≤ (10709410127671/100000000000000 : ℝ)^3675
        have hw : |(-435650077/2500000000 : ℝ)|=(435650077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464970607/10000000000 : ℝ)|^4699 ≤ (5772706260879/12500000000000 : ℝ)^3675
        have hw : |(5464970607/10000000000 : ℝ)|=(5464970607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589237917/5000000000 : ℝ)|^4699 ≤ (8621787954203/20000000000000 : ℝ)^3675
        have hw : |(2589237917/5000000000 : ℝ)|=(2589237917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s3_1 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071177869/2000000000 : ℝ)*x 0 + (-945229169/5000000000 : ℝ)*x 1 + (1035695167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071177869/2000000000 : ℝ)^4699 ≤ (22503153543087/50000000000000 : ℝ)^3675 := by
    have hnat : (1071177869 : ℕ)^4699*50000000000000^3675 ≤ 22503153543087^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071177869 2000000000 22503153543087 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945229169/5000000000 : ℝ)^4699 ≤ (5942376554973/50000000000000 : ℝ)^3675 := by
    have hnat : (945229169 : ℕ)^4699*50000000000000^3675 ≤ 5942376554973^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945229169 5000000000 5942376554973 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035695167/2000000000 : ℝ)^4699 ≤ (43108939781659/100000000000000 : ℝ)^3675 := by
    have hnat : (1035695167 : ℕ)^4699*100000000000000^3675 ≤ 43108939781659^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035695167 2000000000 43108939781659 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071177869/2000000000 : ℝ), (-945229169/5000000000 : ℝ), (1035695167/2000000000 : ℝ)] ![(22503153543087/50000000000000 : ℝ), (5942376554973/50000000000000 : ℝ), (43108939781659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071177869/2000000000 : ℝ)|^4699 ≤ (22503153543087/50000000000000 : ℝ)^3675
        have hw : |(1071177869/2000000000 : ℝ)|=(1071177869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945229169/5000000000 : ℝ)|^4699 ≤ (5942376554973/50000000000000 : ℝ)^3675
        have hw : |(-945229169/5000000000 : ℝ)|=(945229169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035695167/2000000000 : ℝ)|^4699 ≤ (43108939781659/100000000000000 : ℝ)^3675
        have hw : |(1035695167/2000000000 : ℝ)|=(1035695167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s3_2 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071177869/2000000000 : ℝ)*x 0 + (1035695167/2000000000 : ℝ)*x 1 + (-1890458339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071177869/2000000000 : ℝ)^4699 ≤ (22503153543087/50000000000000 : ℝ)^3675 := by
    have hnat : (1071177869 : ℕ)^4699*50000000000000^3675 ≤ 22503153543087^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071177869 2000000000 22503153543087 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035695167/2000000000 : ℝ)^4699 ≤ (43108939781659/100000000000000 : ℝ)^3675 := by
    have hnat : (1035695167 : ℕ)^4699*100000000000000^3675 ≤ 43108939781659^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035695167 2000000000 43108939781659 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890458339/10000000000 : ℝ)^4699 ≤ (2376950623597/20000000000000 : ℝ)^3675 := by
    have hnat : (1890458339 : ℕ)^4699*20000000000000^3675 ≤ 2376950623597^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890458339 10000000000 2376950623597 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071177869/2000000000 : ℝ), (1035695167/2000000000 : ℝ), (-1890458339/10000000000 : ℝ)] ![(22503153543087/50000000000000 : ℝ), (43108939781659/100000000000000 : ℝ), (2376950623597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071177869/2000000000 : ℝ)|^4699 ≤ (22503153543087/50000000000000 : ℝ)^3675
        have hw : |(1071177869/2000000000 : ℝ)|=(1071177869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035695167/2000000000 : ℝ)|^4699 ≤ (43108939781659/100000000000000 : ℝ)^3675
        have hw : |(1035695167/2000000000 : ℝ)|=(1035695167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1890458339/10000000000 : ℝ)|^4699 ≤ (2376950623597/20000000000000 : ℝ)^3675
        have hw : |(-1890458339/10000000000 : ℝ)|=(1890458339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s3_3 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224971883/10000000000 : ℝ)*x 0 + (778202613/2000000000 : ℝ)*x 1 + (4581143641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224971883/10000000000 : ℝ)^4699 ≤ (33232543108647/100000000000000 : ℝ)^3675 := by
    have hnat : (4224971883 : ℕ)^4699*100000000000000^3675 ≤ 33232543108647^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224971883 10000000000 33232543108647 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (778202613/2000000000 : ℝ)^4699 ≤ (14955742674463/50000000000000 : ℝ)^3675 := by
    have hnat : (778202613 : ℕ)^4699*50000000000000^3675 ≤ 14955742674463^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778202613 2000000000 14955742674463 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4581143641/10000000000 : ℝ)^4699 ≤ (7371194306401/20000000000000 : ℝ)^3675 := by
    have hnat : (4581143641 : ℕ)^4699*20000000000000^3675 ≤ 7371194306401^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581143641 10000000000 7371194306401 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224971883/10000000000 : ℝ), (778202613/2000000000 : ℝ), (4581143641/10000000000 : ℝ)] ![(33232543108647/100000000000000 : ℝ), (14955742674463/50000000000000 : ℝ), (7371194306401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224971883/10000000000 : ℝ)|^4699 ≤ (33232543108647/100000000000000 : ℝ)^3675
        have hw : |(4224971883/10000000000 : ℝ)|=(4224971883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(778202613/2000000000 : ℝ)|^4699 ≤ (14955742674463/50000000000000 : ℝ)^3675
        have hw : |(778202613/2000000000 : ℝ)|=(778202613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4581143641/10000000000 : ℝ)|^4699 ≤ (7371194306401/20000000000000 : ℝ)^3675
        have hw : |(4581143641/10000000000 : ℝ)|=(4581143641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s3_4 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1742674351/10000000000 : ℝ)*x 0 + (1295150709/2500000000 : ℝ)*x 1 + (1092564239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742674351/10000000000 : ℝ)^4699 ≤ (2141998393231/20000000000000 : ℝ)^3675 := by
    have hnat : (1742674351 : ℕ)^4699*20000000000000^3675 ≤ 2141998393231^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742674351 10000000000 2141998393231 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295150709/2500000000 : ℝ)^4699 ≤ (43131581325301/100000000000000 : ℝ)^3675 := by
    have hnat : (1295150709 : ℕ)^4699*100000000000000^3675 ≤ 43131581325301^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295150709 2500000000 43131581325301 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092564239/2000000000 : ℝ)^4699 ≤ (46158426698589/100000000000000 : ℝ)^3675 := by
    have hnat : (1092564239 : ℕ)^4699*100000000000000^3675 ≤ 46158426698589^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092564239 2000000000 46158426698589 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1742674351/10000000000 : ℝ), (1295150709/2500000000 : ℝ), (1092564239/2000000000 : ℝ)] ![(2141998393231/20000000000000 : ℝ), (43131581325301/100000000000000 : ℝ), (46158426698589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1742674351/10000000000 : ℝ)|^4699 ≤ (2141998393231/20000000000000 : ℝ)^3675
        have hw : |(-1742674351/10000000000 : ℝ)|=(1742674351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295150709/2500000000 : ℝ)|^4699 ≤ (43131581325301/100000000000000 : ℝ)^3675
        have hw : |(1295150709/2500000000 : ℝ)|=(1295150709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092564239/2000000000 : ℝ)|^4699 ≤ (46158426698589/100000000000000 : ℝ)^3675
        have hw : |(1092564239/2000000000 : ℝ)|=(1092564239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s3_5 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640010849/5000000000 : ℝ)*x 0 + (-401528313/2500000000 : ℝ)*x 1 + (2731410681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640010849/5000000000 : ℝ)^4699 ≤ (2762047156389/6250000000000 : ℝ)^3675 := by
    have hnat : (2640010849 : ℕ)^4699*6250000000000^3675 ≤ 2762047156389^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640010849 5000000000 2762047156389 6250000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401528313/2500000000 : ℝ)^4699 ≤ (385952678947/4000000000000 : ℝ)^3675 := by
    have hnat : (401528313 : ℕ)^4699*4000000000000^3675 ≤ 385952678947^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401528313 2500000000 385952678947 4000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731410681/5000000000 : ℝ)^4699 ≤ (46158428502847/100000000000000 : ℝ)^3675 := by
    have hnat : (2731410681 : ℕ)^4699*100000000000000^3675 ≤ 46158428502847^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731410681 5000000000 46158428502847 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640010849/5000000000 : ℝ), (-401528313/2500000000 : ℝ), (2731410681/5000000000 : ℝ)] ![(2762047156389/6250000000000 : ℝ), (385952678947/4000000000000 : ℝ), (46158428502847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640010849/5000000000 : ℝ)|^4699 ≤ (2762047156389/6250000000000 : ℝ)^3675
        have hw : |(2640010849/5000000000 : ℝ)|=(2640010849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-401528313/2500000000 : ℝ)|^4699 ≤ (385952678947/4000000000000 : ℝ)^3675
        have hw : |(-401528313/2500000000 : ℝ)|=(401528313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731410681/5000000000 : ℝ)|^4699 ≤ (46158428502847/100000000000000 : ℝ)^3675
        have hw : |(2731410681/5000000000 : ℝ)|=(2731410681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s3_6 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528002219/1000000000 : ℝ)*x 0 + (2731410527/5000000000 : ℝ)*x 1 + (-1606113/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528002219/1000000000 : ℝ)^4699 ≤ (4419275976759/10000000000000 : ℝ)^3675 := by
    have hnat : (528002219 : ℕ)^4699*10000000000000^3675 ≤ 4419275976759^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528002219 1000000000 4419275976759 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731410527/5000000000 : ℝ)^4699 ≤ (23079212587617/50000000000000 : ℝ)^3675 := by
    have hnat : (2731410527 : ℕ)^4699*50000000000000^3675 ≤ 23079212587617^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731410527 5000000000 23079212587617 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1606113/10000000 : ℝ)^4699 ≤ (9648815037937/100000000000000 : ℝ)^3675 := by
    have hnat : (1606113 : ℕ)^4699*100000000000000^3675 ≤ 9648815037937^3675*10000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606113 10000000 9648815037937 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528002219/1000000000 : ℝ), (2731410527/5000000000 : ℝ), (-1606113/10000000 : ℝ)] ![(4419275976759/10000000000000 : ℝ), (23079212587617/50000000000000 : ℝ), (9648815037937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528002219/1000000000 : ℝ)|^4699 ≤ (4419275976759/10000000000000 : ℝ)^3675
        have hw : |(528002219/1000000000 : ℝ)|=(528002219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731410527/5000000000 : ℝ)|^4699 ≤ (23079212587617/50000000000000 : ℝ)^3675
        have hw : |(2731410527/5000000000 : ℝ)|=(2731410527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1606113/10000000 : ℝ)|^4699 ≤ (9648815037937/100000000000000 : ℝ)^3675
        have hw : |(-1606113/10000000 : ℝ)|=(1606113/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s3_7 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211257519/500000000 : ℝ)*x 0 + (4576019367/10000000000 : ℝ)*x 1 + (3896191421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211257519/500000000 : ℝ)^4699 ≤ (6646867668751/20000000000000 : ℝ)^3675 := by
    have hnat : (211257519 : ℕ)^4699*20000000000000^3675 ≤ 6646867668751^3675*500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211257519 500000000 6646867668751 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4576019367/10000000000 : ℝ)^4699 ≤ (36803267153397/100000000000000 : ℝ)^3675 := by
    have hnat : (4576019367 : ℕ)^4699*100000000000000^3675 ≤ 36803267153397^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576019367 10000000000 36803267153397 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3896191421/10000000000 : ℝ)^4699 ≤ (14981197246019/50000000000000 : ℝ)^3675 := by
    have hnat : (3896191421 : ℕ)^4699*50000000000000^3675 ≤ 14981197246019^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3896191421 10000000000 14981197246019 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211257519/500000000 : ℝ), (4576019367/10000000000 : ℝ), (3896191421/10000000000 : ℝ)] ![(6646867668751/20000000000000 : ℝ), (36803267153397/100000000000000 : ℝ), (14981197246019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211257519/500000000 : ℝ)|^4699 ≤ (6646867668751/20000000000000 : ℝ)^3675
        have hw : |(211257519/500000000 : ℝ)|=(211257519/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4576019367/10000000000 : ℝ)|^4699 ≤ (36803267153397/100000000000000 : ℝ)^3675
        have hw : |(4576019367/10000000000 : ℝ)|=(4576019367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3896191421/10000000000 : ℝ)|^4699 ≤ (14981197246019/50000000000000 : ℝ)^3675
        have hw : |(3896191421/10000000000 : ℝ)|=(3896191421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1595_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8281/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10157/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2579/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (512/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8281/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10157/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8281/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10157/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8281/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10157/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8281/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10157/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8281/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10157/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8281/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10157/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (10157/100000 : ℝ) ^ (4695/1024 : ℝ) ≤ (2792919367881519/100000000000000000000 : ℝ) := by
    have hpowers : (10157/100000 : ℝ)^4695 ≤ (2792919367881519/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10157 : ℕ)^4695*100000000000000000000^1024 ≤ 2792919367881519^1024*100000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10157 100000 2792919367881519 100000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10157/100000 : ℝ)) (X := (2792919367881519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8281/50000 : ℝ) ^ (4695/1024 : ℝ) ≤ (13141126787311333/50000000000000000000 : ℝ) := by
    have hpowers : (8281/50000 : ℝ)^4695 ≤ (13141126787311333/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8281 : ℕ)^4695*50000000000000000000^1024 ≤ 13141126787311333^1024*50000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8281 50000 13141126787311333 50000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8281/50000 : ℝ)) (X := (13141126787311333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002792919367881519/50000000000000000000 : ℝ) ≤ (10000121826921407/10000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (50002792919367881519/50000000000000000000 : ℝ)^1024 ≤ (10000121826921407/10000000000000000 : ℝ)^4695 := by
      have hnat : (50002792919367881519 : ℕ)^1024*10000000000000000^4695 ≤ 10000121826921407^4695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002792919367881519 50000000000000000000 10000121826921407 10000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000121826921407/10000000000000000 : ℝ)) (X := (50002792919367881519/50000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005815034588500837/20000000000000000000 : ℝ) ≤ (10000634070147397/10000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (20005815034588500837/20000000000000000000 : ℝ)^1024 ≤ (10000634070147397/10000000000000000 : ℝ)^4695 := by
      have hnat : (20005815034588500837 : ℕ)^1024*10000000000000000^4695 ≤ 10000634070147397^4695*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005815034588500837 20000000000000000000 10000634070147397 10000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000634070147397/10000000000000000 : ℝ)) (X := (20005815034588500837/20000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013141126787311333/25000000000000000000 : ℝ) ≤ (10001146313373387/10000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (25013141126787311333/25000000000000000000 : ℝ)^1024 ≤ (10001146313373387/10000000000000000 : ℝ)^4695 := by
      have hnat : (25013141126787311333 : ℕ)^1024*10000000000000000^4695 ≤ 10001146313373387^4695*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013141126787311333 25000000000000000000 10001146313373387 10000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001146313373387/10000000000000000 : ℝ)) (X := (25013141126787311333/25000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2792919367881519/100000000000000000000 : ℝ) ≤ ((365944997671650577/366000000000000000 : ℝ)+2*(51224322599/64050000000000 : ℝ)*(10157/100000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (365944997671650577/366000000000000000 : ℝ)+2*(51224322599/64050000000000 : ℝ)*(10157/100000 : ℝ)=(10000121826921407/10000000000000000 : ℝ) by norm_num, show 1+2*(2792919367881519/100000000000000000000 : ℝ)=(50002792919367881519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13141126787311333/50000000000000000000 : ℝ)+(2792919367881519/100000000000000000000 : ℝ) ≤ ((365944997671650577/366000000000000000 : ℝ)+(51224322599/64050000000000 : ℝ)*((8281/50000 : ℝ)+(10157/100000 : ℝ)))^(4695/1024 : ℝ) := by
    rw [show (365944997671650577/366000000000000000 : ℝ)+(51224322599/64050000000000 : ℝ)*((8281/50000 : ℝ)+(10157/100000 : ℝ))=(10000634070147397/10000000000000000 : ℝ) by norm_num, show 1+(13141126787311333/50000000000000000000 : ℝ)+(2792919367881519/100000000000000000000 : ℝ)=(20005815034588500837/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13141126787311333/50000000000000000000 : ℝ) ≤ ((365944997671650577/366000000000000000 : ℝ)+2*(51224322599/64050000000000 : ℝ)*(8281/50000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (365944997671650577/366000000000000000 : ℝ)+2*(51224322599/64050000000000 : ℝ)*(8281/50000 : ℝ)=(10001146313373387/10000000000000000 : ℝ) by norm_num, show 1+2*(13141126787311333/50000000000000000000 : ℝ)=(25013141126787311333/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (365944997671650577/366000000000000000 : ℝ)*(X 1 0+X 2 0)+(51224322599/64050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (10157/100000 : ℝ)) (hi := (8281/50000 : ℝ)) (c := (365944997671650577/366000000000000000 : ℝ)) (alpha := (51224322599/64050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (365944997671650577/366000000000000000 : ℝ)*(X 0 1+X 2 1)+(51224322599/64050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (10157/100000 : ℝ)) (hi := (8281/50000 : ℝ)) (c := (365944997671650577/366000000000000000 : ℝ)) (alpha := (51224322599/64050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (365944997671650577/366000000000000000 : ℝ)*(X 0 2+X 1 2)+(51224322599/64050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (10157/100000 : ℝ)) (hi := (8281/50000 : ℝ)) (c := (365944997671650577/366000000000000000 : ℝ)) (alpha := (51224322599/64050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-435650077/2500000000 : ℝ)*X 0 0+(5464970607/10000000000 : ℝ)*X 0 1+(2589237917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071177869/2000000000 : ℝ)*X 1 0+(-945229169/5000000000 : ℝ)*X 1 1+(1035695167/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071177869/2000000000 : ℝ)*X 2 0+(1035695167/2000000000 : ℝ)*X 2 1+(-1890458339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4224971883/10000000000 : ℝ)*X 0 0+(778202613/2000000000 : ℝ)*X 0 1+(4581143641/10000000000 : ℝ)*X 0 2+(4224971883/10000000000 : ℝ)*X 1 0+(778202613/2000000000 : ℝ)*X 1 1+(4581143641/10000000000 : ℝ)*X 1 2+(4224971883/10000000000 : ℝ)*X 2 0+(778202613/2000000000 : ℝ)*X 2 1+(4581143641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1742674351/10000000000 : ℝ)*X 0 0+(1295150709/2500000000 : ℝ)*X 0 1+(1092564239/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640010849/5000000000 : ℝ)*X 1 0+(-401528313/2500000000 : ℝ)*X 1 1+(2731410681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528002219/1000000000 : ℝ)*X 2 0+(2731410527/5000000000 : ℝ)*X 2 1+(-1606113/10000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((211257519/500000000 : ℝ)*X 0 0+(4576019367/10000000000 : ℝ)*X 0 1+(3896191421/10000000000 : ℝ)*X 0 2+(211257519/500000000 : ℝ)*X 1 0+(4576019367/10000000000 : ℝ)*X 1 1+(3896191421/10000000000 : ℝ)*X 1 2+(211257519/500000000 : ℝ)*X 2 0+(4576019367/10000000000 : ℝ)*X 2 1+(3896191421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5266535787660065822710951/2135000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (416369689/100000000000000 : ℝ)*(base19) + (24284451/6250000000000 : ℝ)*(base23) + (7449633/50000000000000 : ℝ)*(lower2) + (6237757/10000000000000 : ℝ)*(upper3) + (41394997/100000000000000 : ℝ)*(upper5) + (123487010846197/5000000000000 : ℝ)*(major0) + (123487010846197/5000000000000 : ℝ)*(major1) + (123487010846197/5000000000000 : ℝ)*(major2) + (1745235073752033/50000000000000 : ℝ)*(sp0) + (218154663118071/6250000000000 : ℝ)*(sp1) + (349047463770761/10000000000000 : ℝ)*(sp2) + (362250777753737/25000000000000 : ℝ)*(sp3) + (4878754759/100000000000000 : ℝ)*(sp4) + (2214348709/100000000000000 : ℝ)*(sp7) + (724502662681829/50000000000000 : ℝ)*(f.failure) + (1745237513129413/50000000000000 : ℝ)*(f.sum) + (2672105678497/1281000000000000000000000000 : ℝ)*base65 + (77046476814656561/4270000000000000000000000000000 : ℝ)*base67 + (100487915141466561/4270000000000000000000000000000 : ℝ)*base69 + (65144300100606561/4270000000000000000000000000000 : ℝ)*base71 + (1608610853231/1281000000000000000000000000 : ℝ)*base74 + (62335591059496561/4270000000000000000000000000000 : ℝ)*base75 + (28888756907506561/4270000000000000000000000000000 : ℝ)*base77 + (23869093422376561/4270000000000000000000000000000 : ℝ)*base79 + (7769353786897/1281000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (5789443/5000000000000000000000 : ℝ)*base90 + (5789443/5000000000000000000000 : ℝ)*base92 + (5789443/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88143775620963887506914987/21350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212779249/100000000000000 : ℝ)*(base19) + (32907401/5000000000000 : ℝ)*(base23) + (8928901/20000000000000 : ℝ)*(lower4) + (153354919/100000000000000 : ℝ)*(upper5) + (1253579993180111/50000000000000 : ℝ)*(major0) + (1253579993180111/50000000000000 : ℝ)*(major1) + (1253579993180111/50000000000000 : ℝ)*(major2) + (158357079/100000000000000 : ℝ)*(sp0) + (2817323561/50000000000000 : ℝ)*(sp1) + (7767079817/100000000000000 : ℝ)*(sp2) + (885840010057631/25000000000000 : ℝ)*(sp4) + (221459646947577/6250000000000 : ℝ)*(sp5) + (1771675886679883/50000000000000 : ℝ)*(sp6) + (735479818257849/50000000000000 : ℝ)*(sp7) + (735479818257849/50000000000000 : ℝ)*(f.failure) + (3543360198587603/100000000000000 : ℝ)*(f.sum) + (3362361339641/1601250000000000000000000000 : ℝ)*base66 + (224923126858740557/42700000000000000000000000000000 : ℝ)*base68 + (241001629999440557/42700000000000000000000000000000 : ℝ)*base70 + (223673130602840557/42700000000000000000000000000000 : ℝ)*base72 + (1382563517887/3202500000000000000000000000 : ℝ)*base74 + (743480275947040557/42700000000000000000000000000000 : ℝ)*base76 + (179134057786140557/42700000000000000000000000000000 : ℝ)*base78 + (566458758402140557/42700000000000000000000000000000 : ℝ)*base80 + (19626618938519/6405000000000000000000000000 : ℝ)*base82 + (65895217/5000000000000000000000 : ℝ)*base89 + (65895217/5000000000000000000000 : ℝ)*base91 + (65895217/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1595_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8281/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10157/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (512/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1595_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1595_s4_0 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1742767157/10000000000 : ℝ)*x 0 + (5464146807/10000000000 : ℝ)*x 1 + (5179188879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742767157/10000000000 : ℝ)^4699 ≤ (5355360628099/50000000000000 : ℝ)^3675 := by
    have hnat : (1742767157 : ℕ)^4699*50000000000000^3675 ≤ 5355360628099^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742767157 10000000000 5355360628099 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464146807/10000000000 : ℝ)^4699 ≤ (57715936267/125000000000 : ℝ)^3675 := by
    have hnat : (5464146807 : ℕ)^4699*125000000000^3675 ≤ 57715936267^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464146807 10000000000 57715936267 125000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179188879/10000000000 : ℝ)^4699 ≤ (43116529718297/100000000000000 : ℝ)^3675 := by
    have hnat : (5179188879 : ℕ)^4699*100000000000000^3675 ≤ 43116529718297^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179188879 10000000000 43116529718297 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1742767157/10000000000 : ℝ), (5464146807/10000000000 : ℝ), (5179188879/10000000000 : ℝ)] ![(5355360628099/50000000000000 : ℝ), (57715936267/125000000000 : ℝ), (43116529718297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1742767157/10000000000 : ℝ)|^4699 ≤ (5355360628099/50000000000000 : ℝ)^3675
        have hw : |(-1742767157/10000000000 : ℝ)|=(1742767157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464146807/10000000000 : ℝ)|^4699 ≤ (57715936267/125000000000 : ℝ)^3675
        have hw : |(5464146807/10000000000 : ℝ)|=(5464146807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179188879/10000000000 : ℝ)|^4699 ≤ (43116529718297/100000000000000 : ℝ)^3675
        have hw : |(5179188879/10000000000 : ℝ)|=(5179188879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s4_1 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355669783/10000000000 : ℝ)*x 0 + (-1889807343/10000000000 : ℝ)*x 1 + (80924829/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355669783/10000000000 : ℝ)^4699 ≤ (45003947995777/100000000000000 : ℝ)^3675 := by
    have hnat : (5355669783 : ℕ)^4699*100000000000000^3675 ≤ 45003947995777^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355669783 10000000000 45003947995777 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889807343/10000000000 : ℝ)^4699 ≤ (148494004803/1250000000000 : ℝ)^3675 := by
    have hnat : (1889807343 : ℕ)^4699*1250000000000^3675 ≤ 148494004803^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889807343 10000000000 148494004803 1250000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80924829/156250000 : ℝ)^4699 ≤ (8623306320479/20000000000000 : ℝ)^3675 := by
    have hnat : (80924829 : ℕ)^4699*20000000000000^3675 ≤ 8623306320479^3675*156250000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80924829 156250000 8623306320479 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355669783/10000000000 : ℝ), (-1889807343/10000000000 : ℝ), (80924829/156250000 : ℝ)] ![(45003947995777/100000000000000 : ℝ), (148494004803/1250000000000 : ℝ), (8623306320479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355669783/10000000000 : ℝ)|^4699 ≤ (45003947995777/100000000000000 : ℝ)^3675
        have hw : |(5355669783/10000000000 : ℝ)|=(5355669783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1889807343/10000000000 : ℝ)|^4699 ≤ (148494004803/1250000000000 : ℝ)^3675
        have hw : |(-1889807343/10000000000 : ℝ)|=(1889807343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80924829/156250000 : ℝ)|^4699 ≤ (8623306320479/20000000000000 : ℝ)^3675
        have hw : |(80924829/156250000 : ℝ)|=(80924829/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s4_2 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66945873/125000000 : ℝ)*x 0 + (5179188981/10000000000 : ℝ)*x 1 + (-1889807367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66945873/125000000 : ℝ)^4699 ≤ (11250987152053/25000000000000 : ℝ)^3675 := by
    have hnat : (66945873 : ℕ)^4699*25000000000000^3675 ≤ 11250987152053^3675*125000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66945873 125000000 11250987152053 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179188981/10000000000 : ℝ)^4699 ≤ (2694783175253/6250000000000 : ℝ)^3675 := by
    have hnat : (5179188981 : ℕ)^4699*6250000000000^3675 ≤ 2694783175253^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179188981 10000000000 2694783175253 6250000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889807367/10000000000 : ℝ)^4699 ≤ (11879520577143/100000000000000 : ℝ)^3675 := by
    have hnat : (1889807367 : ℕ)^4699*100000000000000^3675 ≤ 11879520577143^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889807367 10000000000 11879520577143 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66945873/125000000 : ℝ), (5179188981/10000000000 : ℝ), (-1889807367/10000000000 : ℝ)] ![(11250987152053/25000000000000 : ℝ), (2694783175253/6250000000000 : ℝ), (11879520577143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66945873/125000000 : ℝ)|^4699 ≤ (11250987152053/25000000000000 : ℝ)^3675
        have hw : |(66945873/125000000 : ℝ)|=(66945873/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179188981/10000000000 : ℝ)|^4699 ≤ (2694783175253/6250000000000 : ℝ)^3675
        have hw : |(5179188981/10000000000 : ℝ)|=(5179188981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1889807367/10000000000 : ℝ)|^4699 ≤ (11879520577143/100000000000000 : ℝ)^3675
        have hw : |(-1889807367/10000000000 : ℝ)|=(1889807367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s4_3 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (845015799/2000000000 : ℝ)*x 0 + (1946426251/5000000000 : ℝ)*x 1 + (4579281071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845015799/2000000000 : ℝ)^4699 ≤ (33233620385969/100000000000000 : ℝ)^3675 := by
    have hnat : (845015799 : ℕ)^4699*100000000000000^3675 ≤ 33233620385969^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845015799 2000000000 33233620385969 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946426251/5000000000 : ℝ)^4699 ≤ (5985913390219/20000000000000 : ℝ)^3675 := by
    have hnat : (1946426251 : ℕ)^4699*20000000000000^3675 ≤ 5985913390219^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946426251 5000000000 5985913390219 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4579281071/10000000000 : ℝ)^4699 ≤ (920920316367/2500000000000 : ℝ)^3675 := by
    have hnat : (4579281071 : ℕ)^4699*2500000000000^3675 ≤ 920920316367^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579281071 10000000000 920920316367 2500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845015799/2000000000 : ℝ), (1946426251/5000000000 : ℝ), (4579281071/10000000000 : ℝ)] ![(33233620385969/100000000000000 : ℝ), (5985913390219/20000000000000 : ℝ), (920920316367/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845015799/2000000000 : ℝ)|^4699 ≤ (33233620385969/100000000000000 : ℝ)^3675
        have hw : |(845015799/2000000000 : ℝ)|=(845015799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1946426251/5000000000 : ℝ)|^4699 ≤ (5985913390219/20000000000000 : ℝ)^3675
        have hw : |(1946426251/5000000000 : ℝ)|=(1946426251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4579281071/10000000000 : ℝ)|^4699 ≤ (920920316367/2500000000000 : ℝ)^3675
        have hw : |(4579281071/10000000000 : ℝ)|=(4579281071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s4_4 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1742840073/10000000000 : ℝ)*x 0 + (2590646691/5000000000 : ℝ)*x 1 + (5462020213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742840073/10000000000 : ℝ)^4699 ≤ (535564712691/5000000000000 : ℝ)^3675 := by
    have hnat : (1742840073 : ℕ)^4699*5000000000000^3675 ≤ 535564712691^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742840073 10000000000 535564712691 5000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590646691/5000000000 : ℝ)^4699 ≤ (43138932620493/100000000000000 : ℝ)^3675 := by
    have hnat : (2590646691 : ℕ)^4699*100000000000000^3675 ≤ 43138932620493^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590646691 5000000000 43138932620493 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462020213/10000000000 : ℝ)^4699 ≤ (5768721639363/12500000000000 : ℝ)^3675 := by
    have hnat : (5462020213 : ℕ)^4699*12500000000000^3675 ≤ 5768721639363^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462020213 10000000000 5768721639363 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1742840073/10000000000 : ℝ), (2590646691/5000000000 : ℝ), (5462020213/10000000000 : ℝ)] ![(535564712691/5000000000000 : ℝ), (43138932620493/100000000000000 : ℝ), (5768721639363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1742840073/10000000000 : ℝ)|^4699 ≤ (535564712691/5000000000000 : ℝ)^3675
        have hw : |(-1742840073/10000000000 : ℝ)|=(1742840073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590646691/5000000000 : ℝ)|^4699 ≤ (43138932620493/100000000000000 : ℝ)^3675
        have hw : |(2590646691/5000000000 : ℝ)|=(2590646691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462020213/10000000000 : ℝ)|^4699 ≤ (5768721639363/12500000000000 : ℝ)^3675
        have hw : |(5462020213/10000000000 : ℝ)|=(5462020213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s4_5 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280211073/10000000000 : ℝ)*x 0 + (-1606976131/10000000000 : ℝ)*x 1 + (5462020213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280211073/10000000000 : ℝ)^4699 ≤ (44194781196691/100000000000000 : ℝ)^3675 := by
    have hnat : (5280211073 : ℕ)^4699*100000000000000^3675 ≤ 44194781196691^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280211073 10000000000 44194781196691 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1606976131/10000000000 : ℝ)^4699 ≤ (4827722837151/50000000000000 : ℝ)^3675 := by
    have hnat : (1606976131 : ℕ)^4699*50000000000000^3675 ≤ 4827722837151^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606976131 10000000000 4827722837151 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462020213/10000000000 : ℝ)^4699 ≤ (5768721639363/12500000000000 : ℝ)^3675 := by
    have hnat : (5462020213 : ℕ)^4699*12500000000000^3675 ≤ 5768721639363^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462020213 10000000000 5768721639363 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280211073/10000000000 : ℝ), (-1606976131/10000000000 : ℝ), (5462020213/10000000000 : ℝ)] ![(44194781196691/100000000000000 : ℝ), (4827722837151/50000000000000 : ℝ), (5768721639363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280211073/10000000000 : ℝ)|^4699 ≤ (44194781196691/100000000000000 : ℝ)^3675
        have hw : |(5280211073/10000000000 : ℝ)|=(5280211073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1606976131/10000000000 : ℝ)|^4699 ≤ (4827722837151/50000000000000 : ℝ)^3675
        have hw : |(-1606976131/10000000000 : ℝ)|=(1606976131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462020213/10000000000 : ℝ)|^4699 ≤ (5768721639363/12500000000000 : ℝ)^3675
        have hw : |(5462020213/10000000000 : ℝ)|=(5462020213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s4_6 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280211073/10000000000 : ℝ)*x 0 + (5462020213/10000000000 : ℝ)*x 1 + (-1606976131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280211073/10000000000 : ℝ)^4699 ≤ (44194781196691/100000000000000 : ℝ)^3675 := by
    have hnat : (5280211073 : ℕ)^4699*100000000000000^3675 ≤ 44194781196691^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280211073 10000000000 44194781196691 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462020213/10000000000 : ℝ)^4699 ≤ (5768721639363/12500000000000 : ℝ)^3675 := by
    have hnat : (5462020213 : ℕ)^4699*12500000000000^3675 ≤ 5768721639363^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462020213 10000000000 5768721639363 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1606976131/10000000000 : ℝ)^4699 ≤ (4827722837151/50000000000000 : ℝ)^3675 := by
    have hnat : (1606976131 : ℕ)^4699*50000000000000^3675 ≤ 4827722837151^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606976131 10000000000 4827722837151 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280211073/10000000000 : ℝ), (5462020213/10000000000 : ℝ), (-1606976131/10000000000 : ℝ)] ![(44194781196691/100000000000000 : ℝ), (5768721639363/12500000000000 : ℝ), (4827722837151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280211073/10000000000 : ℝ)|^4699 ≤ (44194781196691/100000000000000 : ℝ)^3675
        have hw : |(5280211073/10000000000 : ℝ)|=(5280211073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462020213/10000000000 : ℝ)|^4699 ≤ (5768721639363/12500000000000 : ℝ)^3675
        have hw : |(5462020213/10000000000 : ℝ)|=(5462020213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1606976131/10000000000 : ℝ)|^4699 ≤ (4827722837151/50000000000000 : ℝ)^3675
        have hw : |(-1606976131/10000000000 : ℝ)|=(1606976131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s4_7 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (422525469/1000000000 : ℝ)*x 0 + (1143552881/2500000000 : ℝ)*x 1 + (974493803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422525469/1000000000 : ℝ)^4699 ≤ (33235387452257/100000000000000 : ℝ)^3675 := by
    have hnat : (422525469 : ℕ)^4699*100000000000000^3675 ≤ 33235387452257^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422525469 1000000000 33235387452257 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143552881/2500000000 : ℝ)^4699 ≤ (36784676980579/100000000000000 : ℝ)^3675 := by
    have hnat : (1143552881 : ℕ)^4699*100000000000000^3675 ≤ 36784676980579^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143552881 2500000000 36784676980579 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974493803/2500000000 : ℝ)^4699 ≤ (14989967779357/50000000000000 : ℝ)^3675 := by
    have hnat : (974493803 : ℕ)^4699*50000000000000^3675 ≤ 14989967779357^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974493803 2500000000 14989967779357 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422525469/1000000000 : ℝ), (1143552881/2500000000 : ℝ), (974493803/2500000000 : ℝ)] ![(33235387452257/100000000000000 : ℝ), (36784676980579/100000000000000 : ℝ), (14989967779357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422525469/1000000000 : ℝ)|^4699 ≤ (33235387452257/100000000000000 : ℝ)^3675
        have hw : |(422525469/1000000000 : ℝ)|=(422525469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1143552881/2500000000 : ℝ)|^4699 ≤ (36784676980579/100000000000000 : ℝ)^3675
        have hw : |(1143552881/2500000000 : ℝ)|=(1143552881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(974493803/2500000000 : ℝ)|^4699 ≤ (14989967779357/50000000000000 : ℝ)^3675
        have hw : |(974493803/2500000000 : ℝ)|=(974493803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1595_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (512/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10331/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16367/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (512/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2579/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (512/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2579/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (512/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2579/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (512/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2579/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (512/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2579/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (512/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2579/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2579/25000 : ℝ) ^ (4695/1024 : ℝ) ≤ (14995398204597/500000000000000000 : ℝ) := by
    have hpowers : (2579/25000 : ℝ)^4695 ≤ (14995398204597/500000000000000000 : ℝ)^1024 := by
      have hnat : (2579 : ℕ)^4695*500000000000000000^1024 ≤ 14995398204597^1024*25000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2579 25000 14995398204597 500000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2579/25000 : ℝ)) (X := (14995398204597/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (512/3125 : ℝ) ^ (4695/1024 : ℝ) ≤ (200094934953091/800000000000000000 : ℝ) := by
    have hpowers : (512/3125 : ℝ)^4695 ≤ (200094934953091/800000000000000000 : ℝ)^1024 := by
      have hnat : (512 : ℕ)^4695*800000000000000000^1024 ≤ 200094934953091^1024*3125^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        512 3125 200094934953091 800000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (512/3125 : ℝ)) (X := (200094934953091/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250014995398204597/250000000000000000 : ℝ) ≤ (10000130819405307/10000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (250014995398204597/250000000000000000 : ℝ)^1024 ≤ (10000130819405307/10000000000000000 : ℝ)^4695 := by
      have hnat : (250014995398204597 : ℕ)^1024*10000000000000000^4695 ≤ 10000130819405307^4695*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250014995398204597 250000000000000000 10000130819405307 10000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000130819405307/10000000000000000 : ℝ)) (X := (250014995398204597/250000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001120437860402231/4000000000000000000 : ℝ) ≤ (2500152716020781/2500000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (4001120437860402231/4000000000000000000 : ℝ)^1024 ≤ (2500152716020781/2500000000000000 : ℝ)^4695 := by
      have hnat : (4001120437860402231 : ℕ)^1024*2500000000000000^4695 ≤ 2500152716020781^4695*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001120437860402231 4000000000000000000 2500152716020781 2500000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500152716020781/2500000000000000 : ℝ)) (X := (4001120437860402231/4000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400200094934953091/400000000000000000 : ℝ) ≤ (10001090908760941/10000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (400200094934953091/400000000000000000 : ℝ)^1024 ≤ (10001090908760941/10000000000000000 : ℝ)^4695 := by
      have hnat : (400200094934953091 : ℕ)^1024*10000000000000000^4695 ≤ 10001090908760941^4695*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400200094934953091 400000000000000000 10001090908760941 10000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001090908760941/10000000000000000 : ℝ)) (X := (400200094934953091/400000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14995398204597/500000000000000000 : ℝ) ≤ ((15167722382589670633/15170000000000000000 : ℝ)+2*(480044677817/606800000000000 : ℝ)*(2579/25000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (15167722382589670633/15170000000000000000 : ℝ)+2*(480044677817/606800000000000 : ℝ)*(2579/25000 : ℝ)=(10000130819405307/10000000000000000 : ℝ) by norm_num, show 1+2*(14995398204597/500000000000000000 : ℝ)=(250014995398204597/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(200094934953091/800000000000000000 : ℝ)+(14995398204597/500000000000000000 : ℝ) ≤ ((15167722382589670633/15170000000000000000 : ℝ)+(480044677817/606800000000000 : ℝ)*((512/3125 : ℝ)+(2579/25000 : ℝ)))^(4695/1024 : ℝ) := by
    rw [show (15167722382589670633/15170000000000000000 : ℝ)+(480044677817/606800000000000 : ℝ)*((512/3125 : ℝ)+(2579/25000 : ℝ))=(2500152716020781/2500000000000000 : ℝ) by norm_num, show 1+(200094934953091/800000000000000000 : ℝ)+(14995398204597/500000000000000000 : ℝ)=(4001120437860402231/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(200094934953091/800000000000000000 : ℝ) ≤ ((15167722382589670633/15170000000000000000 : ℝ)+2*(480044677817/606800000000000 : ℝ)*(512/3125 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (15167722382589670633/15170000000000000000 : ℝ)+2*(480044677817/606800000000000 : ℝ)*(512/3125 : ℝ)=(10001090908760941/10000000000000000 : ℝ) by norm_num, show 1+2*(200094934953091/800000000000000000 : ℝ)=(400200094934953091/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15167722382589670633/15170000000000000000 : ℝ)*(X 1 0+X 2 0)+(480044677817/606800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (512/3125 : ℝ)) (c := (15167722382589670633/15170000000000000000 : ℝ)) (alpha := (480044677817/606800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15167722382589670633/15170000000000000000 : ℝ)*(X 0 1+X 2 1)+(480044677817/606800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (512/3125 : ℝ)) (c := (15167722382589670633/15170000000000000000 : ℝ)) (alpha := (480044677817/606800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15167722382589670633/15170000000000000000 : ℝ)*(X 0 2+X 1 2)+(480044677817/606800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (2579/25000 : ℝ)) (hi := (512/3125 : ℝ)) (c := (15167722382589670633/15170000000000000000 : ℝ)) (alpha := (480044677817/606800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1742767157/10000000000 : ℝ)*X 0 0+(5464146807/10000000000 : ℝ)*X 0 1+(5179188879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355669783/10000000000 : ℝ)*X 1 0+(-1889807343/10000000000 : ℝ)*X 1 1+(80924829/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66945873/125000000 : ℝ)*X 2 0+(5179188981/10000000000 : ℝ)*X 2 1+(-1889807367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((845015799/2000000000 : ℝ)*X 0 0+(1946426251/5000000000 : ℝ)*X 0 1+(4579281071/10000000000 : ℝ)*X 0 2+(845015799/2000000000 : ℝ)*X 1 0+(1946426251/5000000000 : ℝ)*X 1 1+(4579281071/10000000000 : ℝ)*X 1 2+(845015799/2000000000 : ℝ)*X 2 0+(1946426251/5000000000 : ℝ)*X 2 1+(4579281071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1742840073/10000000000 : ℝ)*X 0 0+(2590646691/5000000000 : ℝ)*X 0 1+(5462020213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280211073/10000000000 : ℝ)*X 1 0+(-1606976131/10000000000 : ℝ)*X 1 1+(5462020213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280211073/10000000000 : ℝ)*X 2 0+(5462020213/10000000000 : ℝ)*X 2 1+(-1606976131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((422525469/1000000000 : ℝ)*X 0 0+(1143552881/2500000000 : ℝ)*X 0 1+(974493803/2500000000 : ℝ)*X 0 2+(422525469/1000000000 : ℝ)*X 1 0+(1143552881/2500000000 : ℝ)*X 1 1+(974493803/2500000000 : ℝ)*X 1 2+(422525469/1000000000 : ℝ)*X 2 0+(1143552881/2500000000 : ℝ)*X 2 1+(974493803/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1182700655555232660968634351/189625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (972268447/100000000000000 : ℝ)*(base19) + (955160071/100000000000000 : ℝ)*(base23) + (3645723/12500000000000 : ℝ)*(lower2) + (9503641/6250000000000 : ℝ)*(upper3) + (100376441/100000000000000 : ℝ)*(upper5) + (620768088146251/25000000000000 : ℝ)*(major0) + (620768088146251/25000000000000 : ℝ)*(major1) + (620768088146251/25000000000000 : ℝ)*(major2) + (3509303768690163/100000000000000 : ℝ)*(sp0) + (219332261778947/6250000000000 : ℝ)*(sp1) + (3509316205571529/100000000000000 : ℝ)*(sp2) + (291364248495277/20000000000000 : ℝ)*(sp3) + (3348010359/25000000000000 : ℝ)*(sp4) + (304703017/5000000000000 : ℝ)*(sp7) + (58273093461469/4000000000000 : ℝ)*(f.failure) + (8773292901829/250000000000 : ℝ)*(f.sum) + (7852278337693/7585000000000000000000000000 : ℝ)*base66 + (1975037342877671883/379250000000000000000000000000000 : ℝ)*base67 + (726211071845421883/379250000000000000000000000000000 : ℝ)*base69 + (3773249637163671883/379250000000000000000000000000000 : ℝ)*base71 + (1131304354077/7585000000000000000000000000 : ℝ)*base73 + (383406681589328117/379250000000000000000000000000000 : ℝ)*base76 + (3222332373451671883/379250000000000000000000000000000 : ℝ)*base77 + (1536357193010328117/379250000000000000000000000000000 : ℝ)*base80 + (15022075559053/7585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1829323/400000000000000000000 : ℝ)*base90 + (1829323/400000000000000000000 : ℝ)*base92 + (1829323/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (995810949283792357301773197/189625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (409978909/50000000000000 : ℝ)*(base19) + (888075563/100000000000000 : ℝ)*(base23) + (130785407/50000000000000 : ℝ)*(lower1) + (110524383/100000000000000 : ℝ)*(upper3) + (7655821/25000000000000 : ℝ)*(lower4) + (54446703/50000000000000 : ℝ)*(upper5) + (630117650587497/25000000000000 : ℝ)*(major0) + (630117650587497/25000000000000 : ℝ)*(major1) + (630117650587497/25000000000000 : ℝ)*(major2) + (2766579/390625000000 : ℝ)*(sp2) + (178108600381467/5000000000000 : ℝ)*(sp4) + (1781085593835761/50000000000000 : ℝ)*(sp5) + (222635650706847/6250000000000 : ℝ)*(sp6) + (739384511010729/50000000000000 : ℝ)*(sp7) + (739384511010729/50000000000000 : ℝ)*(f.failure) + (178108600381467/5000000000000 : ℝ)*(f.sum) + (1010591277049/7585000000000000000000000000 : ℝ)*base65 + (157405126426899399/379250000000000000000000000000000 : ℝ)*base68 + (832726117836100601/379250000000000000000000000000000 : ℝ)*base69 + (1637967690493600601/379250000000000000000000000000000 : ℝ)*base71 + (17374268572801/7585000000000000000000000000 : ℝ)*base74 + (12166683824669399399/379250000000000000000000000000000 : ℝ)*base76 + (1948607440256100601/379250000000000000000000000000000 : ℝ)*base77 + (1825828728203100601/379250000000000000000000000000000 : ℝ)*base79 + (19693952840089/7585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (45115743/5000000000000000000000 : ℝ)*base90 + (45115743/5000000000000000000000 : ℝ)*base92 + (45115743/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1595_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (512/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10331/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1595_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1595_s5_0 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13615491/78125000 : ℝ)*x 0 + (273203537/500000000 : ℝ)*x 1 + (2589627253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13615491/78125000 : ℝ)^4699 ≤ (10710844560611/100000000000000 : ℝ)^3675 := by
    have hnat : (13615491 : ℕ)^4699*100000000000000^3675 ≤ 10710844560611^3675*78125000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13615491 78125000 10710844560611 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273203537/500000000 : ℝ)^4699 ≤ (23085963568211/50000000000000 : ℝ)^3675 := by
    have hnat : (273203537 : ℕ)^4699*50000000000000^3675 ≤ 23085963568211^3675*500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273203537 500000000 23085963568211 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589627253/5000000000 : ℝ)^4699 ≤ (43117228293989/100000000000000 : ℝ)^3675 := by
    have hnat : (2589627253 : ℕ)^4699*100000000000000^3675 ≤ 43117228293989^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589627253 5000000000 43117228293989 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13615491/78125000 : ℝ), (273203537/500000000 : ℝ), (2589627253/5000000000 : ℝ)] ![(10710844560611/100000000000000 : ℝ), (23085963568211/50000000000000 : ℝ), (43117228293989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13615491/78125000 : ℝ)|^4699 ≤ (10710844560611/100000000000000 : ℝ)^3675
        have hw : |(-13615491/78125000 : ℝ)|=(13615491/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273203537/500000000 : ℝ)|^4699 ≤ (23085963568211/50000000000000 : ℝ)^3675
        have hw : |(273203537/500000000 : ℝ)|=(273203537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589627253/5000000000 : ℝ)|^4699 ≤ (43117228293989/100000000000000 : ℝ)^3675
        have hw : |(2589627253/5000000000 : ℝ)|=(2589627253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s5_1 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355649489/10000000000 : ℝ)*x 0 + (-1889747733/10000000000 : ℝ)*x 1 + (5179254551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355649489/10000000000 : ℝ)^4699 ≤ (9000745989531/20000000000000 : ℝ)^3675 := by
    have hnat : (5355649489 : ℕ)^4699*20000000000000^3675 ≤ 9000745989531^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355649489 10000000000 9000745989531 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889747733/10000000000 : ℝ)^4699 ≤ (11879041261603/100000000000000 : ℝ)^3675 := by
    have hnat : (1889747733 : ℕ)^4699*100000000000000^3675 ≤ 11879041261603^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889747733 10000000000 11879041261603 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179254551/10000000000 : ℝ)^4699 ≤ (21558614386499/50000000000000 : ℝ)^3675 := by
    have hnat : (5179254551 : ℕ)^4699*50000000000000^3675 ≤ 21558614386499^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179254551 10000000000 21558614386499 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355649489/10000000000 : ℝ), (-1889747733/10000000000 : ℝ), (5179254551/10000000000 : ℝ)] ![(9000745989531/20000000000000 : ℝ), (11879041261603/100000000000000 : ℝ), (21558614386499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355649489/10000000000 : ℝ)|^4699 ≤ (9000745989531/20000000000000 : ℝ)^3675
        have hw : |(5355649489/10000000000 : ℝ)|=(5355649489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1889747733/10000000000 : ℝ)|^4699 ≤ (11879041261603/100000000000000 : ℝ)^3675
        have hw : |(-1889747733/10000000000 : ℝ)|=(1889747733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179254551/10000000000 : ℝ)|^4699 ≤ (21558614386499/50000000000000 : ℝ)^3675
        have hw : |(5179254551/10000000000 : ℝ)|=(5179254551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s5_2 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071129883/2000000000 : ℝ)*x 0 + (207170183/400000000 : ℝ)*x 1 + (-1889747801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071129883/2000000000 : ℝ)^4699 ≤ (9000745830513/20000000000000 : ℝ)^3675 := by
    have hnat : (1071129883 : ℕ)^4699*20000000000000^3675 ≤ 9000745830513^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071129883 2000000000 9000745830513 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207170183/400000000 : ℝ)^4699 ≤ (4311722902847/10000000000000 : ℝ)^3675 := by
    have hnat : (207170183 : ℕ)^4699*10000000000000^3675 ≤ 4311722902847^3675*400000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207170183 400000000 4311722902847 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889747801/10000000000 : ℝ)^4699 ≤ (11879041808159/100000000000000 : ℝ)^3675 := by
    have hnat : (1889747801 : ℕ)^4699*100000000000000^3675 ≤ 11879041808159^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889747801 10000000000 11879041808159 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071129883/2000000000 : ℝ), (207170183/400000000 : ℝ), (-1889747801/10000000000 : ℝ)] ![(9000745830513/20000000000000 : ℝ), (4311722902847/10000000000000 : ℝ), (11879041808159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071129883/2000000000 : ℝ)|^4699 ≤ (9000745830513/20000000000000 : ℝ)^3675
        have hw : |(1071129883/2000000000 : ℝ)|=(1071129883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207170183/400000000 : ℝ)|^4699 ≤ (4311722902847/10000000000000 : ℝ)^3675
        have hw : |(207170183/400000000 : ℝ)|=(207170183/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1889747801/10000000000 : ℝ)|^4699 ≤ (11879041808159/100000000000000 : ℝ)^3675
        have hw : |(-1889747801/10000000000 : ℝ)|=(1889747801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s5_3 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (845017753/2000000000 : ℝ)*x 0 + (486627807/1250000000 : ℝ)*x 1 + (114477727/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845017753/2000000000 : ℝ)^4699 ≤ (4154214830997/12500000000000 : ℝ)^3675 := by
    have hnat : (845017753 : ℕ)^4699*12500000000000^3675 ≤ 4154214830997^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845017753 2000000000 4154214830997 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486627807/1250000000 : ℝ)^4699 ≤ (14965618856603/50000000000000 : ℝ)^3675 := by
    have hnat : (486627807 : ℕ)^4699*50000000000000^3675 ≤ 14965618856603^3675*1250000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486627807 1250000000 14965618856603 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114477727/250000000 : ℝ)^4699 ≤ (36835043620211/100000000000000 : ℝ)^3675 := by
    have hnat : (114477727 : ℕ)^4699*100000000000000^3675 ≤ 36835043620211^3675*250000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114477727 250000000 36835043620211 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845017753/2000000000 : ℝ), (486627807/1250000000 : ℝ), (114477727/250000000 : ℝ)] ![(4154214830997/12500000000000 : ℝ), (14965618856603/50000000000000 : ℝ), (36835043620211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845017753/2000000000 : ℝ)|^4699 ≤ (4154214830997/12500000000000 : ℝ)^3675
        have hw : |(845017753/2000000000 : ℝ)|=(845017753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(486627807/1250000000 : ℝ)|^4699 ≤ (14965618856603/50000000000000 : ℝ)^3675
        have hw : |(486627807/1250000000 : ℝ)|=(486627807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114477727/250000000 : ℝ)|^4699 ≤ (36835043620211/100000000000000 : ℝ)^3675
        have hw : |(114477727/250000000 : ℝ)|=(114477727/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s5_4 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-871427837/5000000000 : ℝ)*x 0 + (5181356961/10000000000 : ℝ)*x 1 + (5461946213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871427837/5000000000 : ℝ)^4699 ≤ (2142283370483/20000000000000 : ℝ)^3675 := by
    have hnat : (871427837 : ℕ)^4699*20000000000000^3675 ≤ 2142283370483^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871427837 5000000000 2142283370483 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181356961/10000000000 : ℝ)^4699 ≤ (21569804736271/50000000000000 : ℝ)^3675 := by
    have hnat : (5181356961 : ℕ)^4699*50000000000000^3675 ≤ 21569804736271^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181356961 10000000000 21569804736271 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461946213/10000000000 : ℝ)^4699 ≤ (4614897365761/10000000000000 : ℝ)^3675 := by
    have hnat : (5461946213 : ℕ)^4699*10000000000000^3675 ≤ 4614897365761^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461946213 10000000000 4614897365761 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-871427837/5000000000 : ℝ), (5181356961/10000000000 : ℝ), (5461946213/10000000000 : ℝ)] ![(2142283370483/20000000000000 : ℝ), (21569804736271/50000000000000 : ℝ), (4614897365761/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-871427837/5000000000 : ℝ)|^4699 ≤ (2142283370483/20000000000000 : ℝ)^3675
        have hw : |(-871427837/5000000000 : ℝ)|=(871427837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181356961/10000000000 : ℝ)|^4699 ≤ (21569804736271/50000000000000 : ℝ)^3675
        have hw : |(5181356961/10000000000 : ℝ)|=(5181356961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461946213/10000000000 : ℝ)|^4699 ≤ (4614897365761/10000000000000 : ℝ)^3675
        have hw : |(5461946213/10000000000 : ℝ)|=(5461946213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s5_5 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280228313/10000000000 : ℝ)*x 0 + (-1607056079/10000000000 : ℝ)*x 1 + (5461946281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280228313/10000000000 : ℝ)^4699 ≤ (4419496570047/10000000000000 : ℝ)^3675 := by
    have hnat : (5280228313 : ℕ)^4699*10000000000000^3675 ≤ 4419496570047^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280228313 10000000000 4419496570047 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1607056079/10000000000 : ℝ)^4699 ≤ (9656059890993/100000000000000 : ℝ)^3675 := by
    have hnat : (1607056079 : ℕ)^4699*100000000000000^3675 ≤ 9656059890993^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607056079 10000000000 9656059890993 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461946281/10000000000 : ℝ)^4699 ≤ (9229794878449/20000000000000 : ℝ)^3675 := by
    have hnat : (5461946281 : ℕ)^4699*20000000000000^3675 ≤ 9229794878449^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461946281 10000000000 9229794878449 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280228313/10000000000 : ℝ), (-1607056079/10000000000 : ℝ), (5461946281/10000000000 : ℝ)] ![(4419496570047/10000000000000 : ℝ), (9656059890993/100000000000000 : ℝ), (9229794878449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280228313/10000000000 : ℝ)|^4699 ≤ (4419496570047/10000000000000 : ℝ)^3675
        have hw : |(5280228313/10000000000 : ℝ)|=(5280228313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1607056079/10000000000 : ℝ)|^4699 ≤ (9656059890993/100000000000000 : ℝ)^3675
        have hw : |(-1607056079/10000000000 : ℝ)|=(1607056079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461946281/10000000000 : ℝ)|^4699 ≤ (9229794878449/20000000000000 : ℝ)^3675
        have hw : |(5461946281/10000000000 : ℝ)|=(5461946281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s5_6 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280228423/10000000000 : ℝ)*x 0 + (5461946213/10000000000 : ℝ)*x 1 + (-1607056021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280228423/10000000000 : ℝ)^4699 ≤ (44194966877699/100000000000000 : ℝ)^3675 := by
    have hnat : (5280228423 : ℕ)^4699*100000000000000^3675 ≤ 44194966877699^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280228423 10000000000 44194966877699 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461946213/10000000000 : ℝ)^4699 ≤ (4614897365761/10000000000000 : ℝ)^3675 := by
    have hnat : (5461946213 : ℕ)^4699*10000000000000^3675 ≤ 4614897365761^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461946213 10000000000 4614897365761 10000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1607056021/10000000000 : ℝ)^4699 ≤ (9656059445393/100000000000000 : ℝ)^3675 := by
    have hnat : (1607056021 : ℕ)^4699*100000000000000^3675 ≤ 9656059445393^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607056021 10000000000 9656059445393 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280228423/10000000000 : ℝ), (5461946213/10000000000 : ℝ), (-1607056021/10000000000 : ℝ)] ![(44194966877699/100000000000000 : ℝ), (4614897365761/10000000000000 : ℝ), (9656059445393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280228423/10000000000 : ℝ)|^4699 ≤ (44194966877699/100000000000000 : ℝ)^3675
        have hw : |(5280228423/10000000000 : ℝ)|=(5280228423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461946213/10000000000 : ℝ)|^4699 ≤ (4614897365761/10000000000000 : ℝ)^3675
        have hw : |(5461946213/10000000000 : ℝ)|=(5461946213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1607056021/10000000000 : ℝ)|^4699 ≤ (9656059445393/100000000000000 : ℝ)^3675
        have hw : |(-1607056021/10000000000 : ℝ)|=(1607056021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_s5_7 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26407901/62500000 : ℝ)*x 0 + (4574044789/10000000000 : ℝ)*x 1 + (194906993/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26407901/62500000 : ℝ)^4699 ≤ (33235482698109/100000000000000 : ℝ)^3675 := by
    have hnat : (26407901 : ℕ)^4699*100000000000000^3675 ≤ 33235482698109^3675*62500000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26407901 62500000 33235482698109 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574044789/10000000000 : ℝ)^4699 ≤ (36782962536307/100000000000000 : ℝ)^3675 := by
    have hnat : (4574044789 : ℕ)^4699*100000000000000^3675 ≤ 36782962536307^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574044789 10000000000 36782962536307 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194906993/500000000 : ℝ)^4699 ≤ (29981554752167/100000000000000 : ℝ)^3675 := by
    have hnat : (194906993 : ℕ)^4699*100000000000000^3675 ≤ 29981554752167^3675*500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194906993 500000000 29981554752167 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26407901/62500000 : ℝ), (4574044789/10000000000 : ℝ), (194906993/500000000 : ℝ)] ![(33235482698109/100000000000000 : ℝ), (36782962536307/100000000000000 : ℝ), (29981554752167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26407901/62500000 : ℝ)|^4699 ≤ (33235482698109/100000000000000 : ℝ)^3675
        have hw : |(26407901/62500000 : ℝ)|=(26407901/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574044789/10000000000 : ℝ)|^4699 ≤ (36782962536307/100000000000000 : ℝ)^3675
        have hw : |(4574044789/10000000000 : ℝ)|=(4574044789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(194906993/500000000 : ℝ)|^4699 ≤ (29981554752167/100000000000000 : ℝ)^3675
        have hw : |(194906993/500000000 : ℝ)|=(194906993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1595_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2583/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8183/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16367/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16367/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16367/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16367/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16367/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16367/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (10331/100000 : ℝ) ^ (4695/1024 : ℝ) ≤ (3019125996732953/100000000000000000000 : ℝ) := by
    have hpowers : (10331/100000 : ℝ)^4695 ≤ (3019125996732953/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10331 : ℕ)^4695*100000000000000000000^1024 ≤ 3019125996732953^1024*100000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10331 100000 3019125996732953 100000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10331/100000 : ℝ)) (X := (3019125996732953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16367/100000 : ℝ) ^ (4695/1024 : ℝ) ≤ (24893097904989959/100000000000000000000 : ℝ) := by
    have hpowers : (16367/100000 : ℝ)^4695 ≤ (24893097904989959/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16367 : ℕ)^4695*100000000000000000000^1024 ≤ 24893097904989959^1024*100000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16367 100000 24893097904989959 100000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16367/100000 : ℝ)) (X := (24893097904989959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50003019125996732953/50000000000000000000 : ℝ) ≤ (2500032923450927/2500000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (50003019125996732953/50000000000000000000 : ℝ)^1024 ≤ (2500032923450927/2500000000000000 : ℝ)^4695 := by
      have hnat : (50003019125996732953 : ℕ)^1024*2500000000000000^4695 ≤ 2500032923450927^4695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003019125996732953 50000000000000000000 2500032923450927 2500000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500032923450927/2500000000000000 : ℝ)) (X := (50003019125996732953/50000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125872256996928841/3125000000000000000 : ℝ) ≤ (2500152177842641/2500000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (3125872256996928841/3125000000000000000 : ℝ)^1024 ≤ (2500152177842641/2500000000000000 : ℝ)^4695 := by
      have hnat : (3125872256996928841 : ℕ)^1024*2500000000000000^4695 ≤ 2500152177842641^4695*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125872256996928841 3125000000000000000 2500152177842641 2500000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500152177842641/2500000000000000 : ℝ)) (X := (3125872256996928841/3125000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024893097904989959/50000000000000000000 : ℝ) ≤ (500054286446871/500000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (50024893097904989959/50000000000000000000 : ℝ)^1024 ≤ (500054286446871/500000000000000 : ℝ)^4695 := by
      have hnat : (50024893097904989959 : ℕ)^1024*500000000000000^4695 ≤ 500054286446871^4695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024893097904989959 50000000000000000000 500054286446871 500000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500054286446871/500000000000000 : ℝ)) (X := (50024893097904989959/50000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3019125996732953/100000000000000000000 : ℝ) ≤ ((58936463639485159/58945312500000000 : ℝ)+2*(59627195857/75450000000000 : ℝ)*(10331/100000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (58936463639485159/58945312500000000 : ℝ)+2*(59627195857/75450000000000 : ℝ)*(10331/100000 : ℝ)=(2500032923450927/2500000000000000 : ℝ) by norm_num, show 1+2*(3019125996732953/100000000000000000000 : ℝ)=(50003019125996732953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24893097904989959/100000000000000000000 : ℝ)+(3019125996732953/100000000000000000000 : ℝ) ≤ ((58936463639485159/58945312500000000 : ℝ)+(59627195857/75450000000000 : ℝ)*((16367/100000 : ℝ)+(10331/100000 : ℝ)))^(4695/1024 : ℝ) := by
    rw [show (58936463639485159/58945312500000000 : ℝ)+(59627195857/75450000000000 : ℝ)*((16367/100000 : ℝ)+(10331/100000 : ℝ))=(2500152177842641/2500000000000000 : ℝ) by norm_num, show 1+(24893097904989959/100000000000000000000 : ℝ)+(3019125996732953/100000000000000000000 : ℝ)=(3125872256996928841/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24893097904989959/100000000000000000000 : ℝ) ≤ ((58936463639485159/58945312500000000 : ℝ)+2*(59627195857/75450000000000 : ℝ)*(16367/100000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (58936463639485159/58945312500000000 : ℝ)+2*(59627195857/75450000000000 : ℝ)*(16367/100000 : ℝ)=(500054286446871/500000000000000 : ℝ) by norm_num, show 1+2*(24893097904989959/100000000000000000000 : ℝ)=(50024893097904989959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58936463639485159/58945312500000000 : ℝ)*(X 1 0+X 2 0)+(59627195857/75450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (10331/100000 : ℝ)) (hi := (16367/100000 : ℝ)) (c := (58936463639485159/58945312500000000 : ℝ)) (alpha := (59627195857/75450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58936463639485159/58945312500000000 : ℝ)*(X 0 1+X 2 1)+(59627195857/75450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (10331/100000 : ℝ)) (hi := (16367/100000 : ℝ)) (c := (58936463639485159/58945312500000000 : ℝ)) (alpha := (59627195857/75450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58936463639485159/58945312500000000 : ℝ)*(X 0 2+X 1 2)+(59627195857/75450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (10331/100000 : ℝ)) (hi := (16367/100000 : ℝ)) (c := (58936463639485159/58945312500000000 : ℝ)) (alpha := (59627195857/75450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-13615491/78125000 : ℝ)*X 0 0+(273203537/500000000 : ℝ)*X 0 1+(2589627253/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355649489/10000000000 : ℝ)*X 1 0+(-1889747733/10000000000 : ℝ)*X 1 1+(5179254551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071129883/2000000000 : ℝ)*X 2 0+(207170183/400000000 : ℝ)*X 2 1+(-1889747801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((845017753/2000000000 : ℝ)*X 0 0+(486627807/1250000000 : ℝ)*X 0 1+(114477727/250000000 : ℝ)*X 0 2+(845017753/2000000000 : ℝ)*X 1 0+(486627807/1250000000 : ℝ)*X 1 1+(114477727/250000000 : ℝ)*X 1 2+(845017753/2000000000 : ℝ)*X 2 0+(486627807/1250000000 : ℝ)*X 2 1+(114477727/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-871427837/5000000000 : ℝ)*X 0 0+(5181356961/10000000000 : ℝ)*X 0 1+(5461946213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280228313/10000000000 : ℝ)*X 1 0+(-1607056079/10000000000 : ℝ)*X 1 1+(5461946281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280228423/10000000000 : ℝ)*X 2 0+(5461946213/10000000000 : ℝ)*X 2 1+(-1607056021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((26407901/62500000 : ℝ)*X 0 0+(4574044789/10000000000 : ℝ)*X 0 1+(194906993/500000000 : ℝ)*X 0 2+(26407901/62500000 : ℝ)*X 1 0+(4574044789/10000000000 : ℝ)*X 1 1+(194906993/500000000 : ℝ)*X 1 2+(26407901/62500000 : ℝ)*X 2 0+(4574044789/10000000000 : ℝ)*X 2 1+(194906993/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84169272919016490094050461/7859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (853937401/50000000000000 : ℝ)*(base19) + (19592277/1250000000000 : ℝ)*(base23) + (49260969/100000000000000 : ℝ)*(lower2) + (271159769/100000000000000 : ℝ)*(upper3) + (36511297/25000000000000 : ℝ)*(upper5) + (1242159189416173/50000000000000 : ℝ)*(major0) + (1242159189416173/50000000000000 : ℝ)*(major1) + (1242159189416173/50000000000000 : ℝ)*(major2) + (877764481221533/25000000000000 : ℝ)*(sp0) + (3511076308263961/100000000000000 : ℝ)*(sp1) + (3511076448756603/100000000000000 : ℝ)*(sp2) + (1457549531162669/100000000000000 : ℝ)*(sp3) + (2511406579/12500000000000 : ℝ)*(sp4) + (88533829/1000000000000 : ℝ)*(sp7) + (45548699517049/3125000000000 : ℝ)*(f.failure) + (3511078016138763/100000000000000 : ℝ)*(f.sum) + (8400251121101/7545000000000000000000000000 : ℝ)*base66 + (66684744306053199/3929687500000000000000000000000 : ℝ)*base68 + (68038009737271949/3929687500000000000000000000000 : ℝ)*base70 + (3105059572621489/245605468750000000000000000000 : ℝ)*base72 + (7286404425251/7545000000000000000000000000 : ℝ)*base74 + (76674416049684523/7859375000000000000000000000000 : ℝ)*base76 + (23126290533893787/1964843750000000000000000000000 : ℝ)*base78 + (113198085886778273/7859375000000000000000000000000 : ℝ)*base80 + (10092780520279/7545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (841183/312500000000000000000 : ℝ)*base90 + (841183/312500000000000000000 : ℝ)*base92 + (841183/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18354548590562922139435179/1571875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1755423209/100000000000000 : ℝ)*(base19) + (488558011/25000000000000 : ℝ)*(base23) + (291371091/50000000000000 : ℝ)*(lower1) + (238112869/100000000000000 : ℝ)*(upper3) + (24835807/50000000000000 : ℝ)*(lower4) + (114737249/50000000000000 : ℝ)*(upper5) + (126084922589271/5000000000000 : ℝ)*(major0) + (126084922589271/5000000000000 : ℝ)*(major1) + (126084922589271/5000000000000 : ℝ)*(major2) + (2134821353/100000000000000 : ℝ)*(sp2) + (890976777178017/25000000000000 : ℝ)*(sp4) + (1781952676644429/50000000000000 : ℝ)*(sp5) + (356390301965867/10000000000000 : ℝ)*(sp6) + (369872351407607/25000000000000 : ℝ)*(sp7) + (369872351407607/25000000000000 : ℝ)*(f.failure) + (890976777178017/25000000000000 : ℝ)*(f.sum) + (20268746093/7859375000000000000000000 : ℝ)*base66 + (253316093716423/392968750000000000000000000000 : ℝ)*base68 + (1554263124012101/196484375000000000000000000000 : ℝ)*base69 + (13247547573532779/785937500000000000000000000000 : ℝ)*base71 + (13206568369/251500000000000000000000000 : ℝ)*base74 + (14114279335357779/785937500000000000000000000000 : ℝ)*base75 + (8045527729712433/1571875000000000000000000000000 : ℝ)*base77 + (219790867287433/1571875000000000000000000000000 : ℝ)*base79 + (482302834279/503000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17562369/2500000000000000000000 : ℝ)*base90 + (17562369/2500000000000000000000 : ℝ)*base92 + (17562369/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1595_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1595_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1595_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8281/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10157/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1595_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1595_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1595_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8281/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10157/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1595_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

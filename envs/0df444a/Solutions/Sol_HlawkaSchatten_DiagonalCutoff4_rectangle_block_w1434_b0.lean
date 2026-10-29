-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1434_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:09.50745+00:00
-- url     : https://prove2.me/submissions/d70ad4e4-c906-42f4-8ed4-73379d856cca

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
theorem support_rectangle_w1434_s0_0 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1755986393/10000000000 : ℝ)*x 0 + (5958120349/10000000000 : ℝ)*x 1 + (4832380293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1755986393/10000000000 : ℝ)^2197 ≤ (10350544098983/100000000000000 : ℝ)^1685 := by
    have hnat : (1755986393 : ℕ)^2197*100000000000000^1685 ≤ 10350544098983^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755986393 10000000000 10350544098983 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5958120349/10000000000 : ℝ)^2197 ≤ (6363331297973/12500000000000 : ℝ)^1685 := by
    have hnat : (5958120349 : ℕ)^2197*12500000000000^1685 ≤ 6363331297973^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5958120349 10000000000 6363331297973 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4832380293/10000000000 : ℝ)^2197 ≤ (38742805501367/100000000000000 : ℝ)^1685 := by
    have hnat : (4832380293 : ℕ)^2197*100000000000000^1685 ≤ 38742805501367^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832380293 10000000000 38742805501367 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1755986393/10000000000 : ℝ), (5958120349/10000000000 : ℝ), (4832380293/10000000000 : ℝ)] ![(10350544098983/100000000000000 : ℝ), (6363331297973/12500000000000 : ℝ), (38742805501367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1755986393/10000000000 : ℝ)|^2197 ≤ (10350544098983/100000000000000 : ℝ)^1685
        have hw : |(-1755986393/10000000000 : ℝ)|=(1755986393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5958120349/10000000000 : ℝ)|^2197 ≤ (6363331297973/12500000000000 : ℝ)^1685
        have hw : |(5958120349/10000000000 : ℝ)|=(5958120349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4832380293/10000000000 : ℝ)|^2197 ≤ (38742805501367/100000000000000 : ℝ)^1685
        have hw : |(4832380293/10000000000 : ℝ)|=(4832380293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s0_1 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (171610731/312500000 : ℝ)*x 0 + (-2391693243/10000000000 : ℝ)*x 1 + (2416190219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171610731/312500000 : ℝ)^2197 ≤ (45771864044369/100000000000000 : ℝ)^1685 := by
    have hnat : (171610731 : ℕ)^2197*100000000000000^1685 ≤ 45771864044369^1685*312500000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171610731 312500000 45771864044369 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2391693243/10000000000 : ℝ)^2197 ≤ (7742664458159/50000000000000 : ℝ)^1685 := by
    have hnat : (2391693243 : ℕ)^2197*50000000000000^1685 ≤ 7742664458159^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391693243 10000000000 7742664458159 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416190219/5000000000 : ℝ)^2197 ≤ (38742807017119/100000000000000 : ℝ)^1685 := by
    have hnat : (2416190219 : ℕ)^2197*100000000000000^1685 ≤ 38742807017119^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416190219 5000000000 38742807017119 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171610731/312500000 : ℝ), (-2391693243/10000000000 : ℝ), (2416190219/5000000000 : ℝ)] ![(45771864044369/100000000000000 : ℝ), (7742664458159/50000000000000 : ℝ), (38742807017119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171610731/312500000 : ℝ)|^2197 ≤ (45771864044369/100000000000000 : ℝ)^1685
        have hw : |(171610731/312500000 : ℝ)|=(171610731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2391693243/10000000000 : ℝ)|^2197 ≤ (7742664458159/50000000000000 : ℝ)^1685
        have hw : |(-2391693243/10000000000 : ℝ)|=(2391693243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2416190219/5000000000 : ℝ)|^2197 ≤ (38742807017119/100000000000000 : ℝ)^1685
        have hw : |(2416190219/5000000000 : ℝ)|=(2416190219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s0_2 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (549154349/1000000000 : ℝ)*x 0 + (4832380459/10000000000 : ℝ)*x 1 + (-597923273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549154349/1000000000 : ℝ)^2197 ≤ (9154373021879/20000000000000 : ℝ)^1685 := by
    have hnat : (549154349 : ℕ)^2197*20000000000000^1685 ≤ 9154373021879^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549154349 1000000000 9154373021879 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4832380459/10000000000 : ℝ)^2197 ≤ (19371403618321/50000000000000 : ℝ)^1685 := by
    have hnat : (4832380459 : ℕ)^2197*50000000000000^1685 ≤ 19371403618321^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832380459 10000000000 19371403618321 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597923273/2500000000 : ℝ)^2197 ≤ (15485327641577/100000000000000 : ℝ)^1685 := by
    have hnat : (597923273 : ℕ)^2197*100000000000000^1685 ≤ 15485327641577^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597923273 2500000000 15485327641577 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549154349/1000000000 : ℝ), (4832380459/10000000000 : ℝ), (-597923273/2500000000 : ℝ)] ![(9154373021879/20000000000000 : ℝ), (19371403618321/50000000000000 : ℝ), (15485327641577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549154349/1000000000 : ℝ)|^2197 ≤ (9154373021879/20000000000000 : ℝ)^1685
        have hw : |(549154349/1000000000 : ℝ)|=(549154349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4832380459/10000000000 : ℝ)|^2197 ≤ (19371403618321/50000000000000 : ℝ)^1685
        have hw : |(4832380459/10000000000 : ℝ)|=(4832380459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-597923273/2500000000 : ℝ)|^2197 ≤ (15485327641577/100000000000000 : ℝ)^1685
        have hw : |(-597923273/2500000000 : ℝ)|=(597923273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s0_3 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1041321129/2500000000 : ℝ)*x 0 + (3103237299/10000000000 : ℝ)*x 1 + (5543051239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041321129/2500000000 : ℝ)^2197 ≤ (31920583929533/100000000000000 : ℝ)^1685 := by
    have hnat : (1041321129 : ℕ)^2197*100000000000000^1685 ≤ 31920583929533^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041321129 2500000000 31920583929533 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103237299/10000000000 : ℝ)^2197 ≤ (679593390807/3125000000000 : ℝ)^1685 := by
    have hnat : (3103237299 : ℕ)^2197*3125000000000^1685 ≤ 679593390807^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103237299 10000000000 679593390807 3125000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5543051239/10000000000 : ℝ)^2197 ≤ (1447888361069/3125000000000 : ℝ)^1685 := by
    have hnat : (5543051239 : ℕ)^2197*3125000000000^1685 ≤ 1447888361069^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543051239 10000000000 1447888361069 3125000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041321129/2500000000 : ℝ), (3103237299/10000000000 : ℝ), (5543051239/10000000000 : ℝ)] ![(31920583929533/100000000000000 : ℝ), (679593390807/3125000000000 : ℝ), (1447888361069/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041321129/2500000000 : ℝ)|^2197 ≤ (31920583929533/100000000000000 : ℝ)^1685
        have hw : |(1041321129/2500000000 : ℝ)|=(1041321129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103237299/10000000000 : ℝ)|^2197 ≤ (679593390807/3125000000000 : ℝ)^1685
        have hw : |(3103237299/10000000000 : ℝ)|=(3103237299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5543051239/10000000000 : ℝ)|^2197 ≤ (1447888361069/3125000000000 : ℝ)^1685
        have hw : |(5543051239/10000000000 : ℝ)|=(5543051239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s0_4 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-879989821/5000000000 : ℝ)*x 0 + (972234467/2000000000 : ℝ)*x 1 + (1482075097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (879989821/5000000000 : ℝ)^2197 ≤ (10381244816091/100000000000000 : ℝ)^1685 := by
    have hnat : (879989821 : ℕ)^2197*100000000000000^1685 ≤ 10381244816091^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879989821 5000000000 10381244816091 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972234467/2000000000 : ℝ)^2197 ≤ (19522027034533/50000000000000 : ℝ)^1685 := by
    have hnat : (972234467 : ℕ)^2197*50000000000000^1685 ≤ 19522027034533^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972234467 2000000000 19522027034533 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1482075097/2500000000 : ℝ)^2197 ≤ (50574701105543/100000000000000 : ℝ)^1685 := by
    have hnat : (1482075097 : ℕ)^2197*100000000000000^1685 ≤ 50574701105543^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482075097 2500000000 50574701105543 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-879989821/5000000000 : ℝ), (972234467/2000000000 : ℝ), (1482075097/2500000000 : ℝ)] ![(10381244816091/100000000000000 : ℝ), (19522027034533/50000000000000 : ℝ), (50574701105543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-879989821/5000000000 : ℝ)|^2197 ≤ (10381244816091/100000000000000 : ℝ)^1685
        have hw : |(-879989821/5000000000 : ℝ)|=(879989821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(972234467/2000000000 : ℝ)|^2197 ≤ (19522027034533/50000000000000 : ℝ)^1685
        have hw : |(972234467/2000000000 : ℝ)|=(972234467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1482075097/2500000000 : ℝ)|^2197 ≤ (50574701105543/100000000000000 : ℝ)^1685
        have hw : |(1482075097/2500000000 : ℝ)|=(1482075097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s0_5 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (20251023/39062500 : ℝ)*x 0 + (-259154571/2000000000 : ℝ)*x 1 + (5928300459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20251023/39062500 : ℝ)^2197 ≤ (849224262103/2000000000000 : ℝ)^1685 := by
    have hnat : (20251023 : ℕ)^2197*2000000000000^1685 ≤ 849224262103^1685*39062500^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20251023 39062500 849224262103 2000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259154571/2000000000 : ℝ)^2197 ≤ (3482042489391/50000000000000 : ℝ)^1685 := by
    have hnat : (259154571 : ℕ)^2197*50000000000000^1685 ≤ 3482042489391^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259154571 2000000000 3482042489391 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5928300459/10000000000 : ℝ)^2197 ≤ (395114858557/781250000000 : ℝ)^1685 := by
    have hnat : (5928300459 : ℕ)^2197*781250000000^1685 ≤ 395114858557^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5928300459 10000000000 395114858557 781250000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20251023/39062500 : ℝ), (-259154571/2000000000 : ℝ), (5928300459/10000000000 : ℝ)] ![(849224262103/2000000000000 : ℝ), (3482042489391/50000000000000 : ℝ), (395114858557/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20251023/39062500 : ℝ)|^2197 ≤ (849224262103/2000000000000 : ℝ)^1685
        have hw : |(20251023/39062500 : ℝ)|=(20251023/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259154571/2000000000 : ℝ)|^2197 ≤ (3482042489391/50000000000000 : ℝ)^1685
        have hw : |(-259154571/2000000000 : ℝ)|=(259154571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5928300459/10000000000 : ℝ)|^2197 ≤ (395114858557/781250000000 : ℝ)^1685
        have hw : |(5928300459/10000000000 : ℝ)|=(5928300459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s0_6 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (648032739/1250000000 : ℝ)*x 0 + (2964150151/5000000000 : ℝ)*x 1 + (-129577307/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648032739/1250000000 : ℝ)^2197 ≤ (42461213361449/100000000000000 : ℝ)^1685 := by
    have hnat : (648032739 : ℕ)^2197*100000000000000^1685 ≤ 42461213361449^1685*1250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648032739 1250000000 42461213361449 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2964150151/5000000000 : ℝ)^2197 ≤ (2528735007447/5000000000000 : ℝ)^1685 := by
    have hnat : (2964150151 : ℕ)^2197*5000000000000^1685 ≤ 2528735007447^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2964150151 5000000000 2528735007447 5000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129577307/1000000000 : ℝ)^2197 ≤ (6964086485403/100000000000000 : ℝ)^1685 := by
    have hnat : (129577307 : ℕ)^2197*100000000000000^1685 ≤ 6964086485403^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129577307 1000000000 6964086485403 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648032739/1250000000 : ℝ), (2964150151/5000000000 : ℝ), (-129577307/1000000000 : ℝ)] ![(42461213361449/100000000000000 : ℝ), (2528735007447/5000000000000 : ℝ), (6964086485403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648032739/1250000000 : ℝ)|^2197 ≤ (42461213361449/100000000000000 : ℝ)^1685
        have hw : |(648032739/1250000000 : ℝ)|=(648032739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2964150151/5000000000 : ℝ)|^2197 ≤ (2528735007447/5000000000000 : ℝ)^1685
        have hw : |(2964150151/5000000000 : ℝ)|=(2964150151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129577307/1000000000 : ℝ)|^2197 ≤ (6964086485403/100000000000000 : ℝ)^1685
        have hw : |(-129577307/1000000000 : ℝ)|=(129577307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s0_7 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26087129/62500000 : ℝ)*x 0 + (342540661/625000000 : ℝ)*x 1 + (126714641/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26087129/62500000 : ℝ)^2197 ≤ (16003551994513/50000000000000 : ℝ)^1685 := by
    have hnat : (26087129 : ℕ)^2197*50000000000000^1685 ≤ 16003551994513^1685*62500000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26087129 62500000 16003551994513 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342540661/625000000 : ℝ)^2197 ≤ (9130704156253/20000000000000 : ℝ)^1685 := by
    have hnat : (342540661 : ℕ)^2197*20000000000000^1685 ≤ 9130704156253^1685*625000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342540661 625000000 9130704156253 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126714641/400000000 : ℝ)^2197 ≤ (2792421901879/12500000000000 : ℝ)^1685 := by
    have hnat : (126714641 : ℕ)^2197*12500000000000^1685 ≤ 2792421901879^1685*400000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126714641 400000000 2792421901879 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26087129/62500000 : ℝ), (342540661/625000000 : ℝ), (126714641/400000000 : ℝ)] ![(16003551994513/50000000000000 : ℝ), (9130704156253/20000000000000 : ℝ), (2792421901879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26087129/62500000 : ℝ)|^2197 ≤ (16003551994513/50000000000000 : ℝ)^1685
        have hw : |(26087129/62500000 : ℝ)|=(26087129/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342540661/625000000 : ℝ)|^2197 ≤ (9130704156253/20000000000000 : ℝ)^1685
        have hw : |(342540661/625000000 : ℝ)|=(342540661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126714641/400000000 : ℝ)|^2197 ≤ (2792421901879/12500000000000 : ℝ)^1685
        have hw : |(126714641/400000000 : ℝ)|=(126714641/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1434_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2083/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1639/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4393/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4393 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4393*1^1024 ≤ 0^1024*1^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4393/1024 : ℝ) ≤ (490638729335191807/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4393 ≤ (490638729335191807/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4393*25000000000000000000^1024 ≤ 490638729335191807^1024*5^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 490638729335191807 25000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (490638729335191807/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4393 := by
      have hnat : (1 : ℕ)^1024*1^4393 ≤ 1^4393*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25490638729335191807/25000000000000000000 : ℝ) ≤ (1255675805738421/1250000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (25490638729335191807/25000000000000000000 : ℝ)^1024 ≤ (1255675805738421/1250000000000000 : ℝ)^4393 := by
      have hnat : (25490638729335191807 : ℕ)^1024*1250000000000000^4393 ≤ 1255675805738421^4393*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25490638729335191807 25000000000000000000 1255675805738421 1250000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255675805738421/1250000000000000 : ℝ)) (X := (25490638729335191807/25000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12990638729335191807/12500000000000000000 : ℝ) ≤ (630675805738421/625000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (12990638729335191807/12500000000000000000 : ℝ)^1024 ≤ (630675805738421/625000000000000 : ℝ)^4393 := by
      have hnat : (12990638729335191807 : ℕ)^1024*625000000000000^4393 ≤ 630675805738421^4393*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12990638729335191807 12500000000000000000 630675805738421 625000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (630675805738421/625000000000000 : ℝ)) (X := (12990638729335191807/12500000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5675805738421/500000000000000 : ℝ)*(0 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5675805738421/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(490638729335191807/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5675805738421/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4393/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5675805738421/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1255675805738421/1250000000000000 : ℝ) by norm_num, show 1+(490638729335191807/25000000000000000000 : ℝ)+(0 : ℝ)=(25490638729335191807/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(490638729335191807/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5675805738421/500000000000000 : ℝ)*(2/5 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5675805738421/500000000000000 : ℝ)*(2/5 : ℝ)=(630675805738421/625000000000000 : ℝ) by norm_num, show 1+2*(490638729335191807/25000000000000000000 : ℝ)=(12990638729335191807/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5675805738421/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5675805738421/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5675805738421/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5675805738421/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5675805738421/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5675805738421/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1755986393/10000000000 : ℝ)*X 0 0+(5958120349/10000000000 : ℝ)*X 0 1+(4832380293/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((171610731/312500000 : ℝ)*X 1 0+(-2391693243/10000000000 : ℝ)*X 1 1+(2416190219/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((549154349/1000000000 : ℝ)*X 2 0+(4832380459/10000000000 : ℝ)*X 2 1+(-597923273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1041321129/2500000000 : ℝ)*X 0 0+(3103237299/10000000000 : ℝ)*X 0 1+(5543051239/10000000000 : ℝ)*X 0 2+(1041321129/2500000000 : ℝ)*X 1 0+(3103237299/10000000000 : ℝ)*X 1 1+(5543051239/10000000000 : ℝ)*X 1 2+(1041321129/2500000000 : ℝ)*X 2 0+(3103237299/10000000000 : ℝ)*X 2 1+(5543051239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-879989821/5000000000 : ℝ)*X 0 0+(972234467/2000000000 : ℝ)*X 0 1+(1482075097/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20251023/39062500 : ℝ)*X 1 0+(-259154571/2000000000 : ℝ)*X 1 1+(5928300459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((648032739/1250000000 : ℝ)*X 2 0+(2964150151/5000000000 : ℝ)*X 2 1+(-129577307/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((26087129/62500000 : ℝ)*X 0 0+(342540661/625000000 : ℝ)*X 0 1+(126714641/400000000 : ℝ)*X 0 2+(26087129/62500000 : ℝ)*X 1 0+(342540661/625000000 : ℝ)*X 1 1+(126714641/400000000 : ℝ)*X 1 2+(26087129/62500000 : ℝ)*X 2 0+(342540661/625000000 : ℝ)*X 2 1+(126714641/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51709975280290911776673/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63348047/6250000000000 : ℝ)*(base19) + (500075411/50000000000000 : ℝ)*(base23) + (128029037/100000000000000 : ℝ)*(upper3) + (8036979/50000000000000 : ℝ)*(upper4) + (73652429/50000000000000 : ℝ)*(upper5) + (324545571026429/50000000000000 : ℝ)*(major0) + (324545571026429/50000000000000 : ℝ)*(major1) + (324545571026429/50000000000000 : ℝ)*(major2) + (444153927954367/50000000000000 : ℝ)*(sp0) + (888310570944409/100000000000000 : ℝ)*(sp1) + (444155292181169/50000000000000 : ℝ)*(sp2) + (409868916427823/100000000000000 : ℝ)*(sp3) + (1864302213/50000000000000 : ℝ)*(sp4) + (82263573/5000000000000 : ℝ)*(sp7) + (409870561699283/100000000000000 : ℝ)*(f.failure) + (888311584513161/100000000000000 : ℝ)*(f.sum) + (17980137196391/12500000000000000000000000000 : ℝ)*base66 + (104395403903609/25000000000000000000000000000 : ℝ)*base67 + (103131613053609/25000000000000000000000000000 : ℝ)*base69 + (17380291828609/25000000000000000000000000000 : ℝ)*base71 + (1373218603609/12500000000000000000000000000 : ℝ)*base73 + (99232756746391/25000000000000000000000000000 : ℝ)*base76 + (102335684528609/25000000000000000000000000000 : ℝ)*base77 + (70276147253609/25000000000000000000000000000 : ℝ)*base79 + (8431749533891/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (37660247/10000000000000000000000 : ℝ)*base89 + (37660247/10000000000000000000000 : ℝ)*base91 + (37660247/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (223563347857688509697649/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2042098829/100000000000000 : ℝ)*(base19) + (1029518197/50000000000000 : ℝ)*(base23) + (23239009/12500000000000 : ℝ)*(base32) + (38363437/12500000000000 : ℝ)*(upper3) + (93153879/50000000000000 : ℝ)*(upper5) + (684736536612259/100000000000000 : ℝ)*(major0) + (684736536612259/100000000000000 : ℝ)*(major1) + (684736536612259/100000000000000 : ℝ)*(major2) + (4847316833/100000000000000 : ℝ)*(sp1) + (316242797/6250000000000 : ℝ)*(sp2) + (937093821408413/100000000000000 : ℝ)*(sp4) + (937086931992751/100000000000000 : ℝ)*(sp5) + (234271675621817/25000000000000 : ℝ)*(sp6) + (86475753563913/20000000000000 : ℝ)*(sp7) + (432378953731637/100000000000000 : ℝ)*(f.failure) + (937093821408413/100000000000000 : ℝ)*(f.sum) + (16532080446961/25000000000000000000000000000 : ℝ)*base66 + (221136566153039/50000000000000000000000000000 : ℝ)*base67 + (441388087453039/50000000000000000000000000000 : ℝ)*base69 + (49109604703039/50000000000000000000000000000 : ℝ)*base71 + (483108003039/25000000000000000000000000000 : ℝ)*base73 + (410342021503039/50000000000000000000000000000 : ℝ)*base75 + (96104131103039/50000000000000000000000000000 : ℝ)*base77 + (147891521296961/50000000000000000000000000000 : ℝ)*base80 + (87620926378039/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3926033/10000000000000000000000 : ℝ)*base89 + (3926033/10000000000000000000000 : ℝ)*base91 + (3926033/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1434_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1639/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1434_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1434_s1_0 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1927631063/10000000000 : ℝ)*x 0 + (87550561/156250000 : ℝ)*x 1 + (2538609299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1927631063/10000000000 : ℝ)^2197 ≤ (11688883308379/100000000000000 : ℝ)^1685 := by
    have hnat : (1927631063 : ℕ)^2197*100000000000000^1685 ≤ 11688883308379^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927631063 10000000000 11688883308379 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87550561/156250000 : ℝ)^2197 ≤ (9397885758127/20000000000000 : ℝ)^1685 := by
    have hnat : (87550561 : ℕ)^2197*20000000000000^1685 ≤ 9397885758127^1685*156250000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87550561 156250000 9397885758127 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538609299/5000000000 : ℝ)^2197 ≤ (1291302746297/3125000000000 : ℝ)^1685 := by
    have hnat : (2538609299 : ℕ)^2197*3125000000000^1685 ≤ 1291302746297^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538609299 5000000000 1291302746297 3125000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1927631063/10000000000 : ℝ), (87550561/156250000 : ℝ), (2538609299/5000000000 : ℝ)] ![(11688883308379/100000000000000 : ℝ), (9397885758127/20000000000000 : ℝ), (1291302746297/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1927631063/10000000000 : ℝ)|^2197 ≤ (11688883308379/100000000000000 : ℝ)^1685
        have hw : |(-1927631063/10000000000 : ℝ)|=(1927631063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(87550561/156250000 : ℝ)|^2197 ≤ (9397885758127/20000000000000 : ℝ)^1685
        have hw : |(87550561/156250000 : ℝ)|=(87550561/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538609299/5000000000 : ℝ)|^2197 ≤ (1291302746297/3125000000000 : ℝ)^1685
        have hw : |(2538609299/5000000000 : ℝ)|=(2538609299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s1_1 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5396310771/10000000000 : ℝ)*x 0 + (-2206255097/10000000000 : ℝ)*x 1 + (1015444041/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396310771/10000000000 : ℝ)^2197 ≤ (22369825109807/50000000000000 : ℝ)^1685 := by
    have hnat : (5396310771 : ℕ)^2197*50000000000000^1685 ≤ 22369825109807^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396310771 10000000000 22369825109807 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206255097/10000000000 : ℝ)^2197 ≤ (13938644830947/100000000000000 : ℝ)^1685 := by
    have hnat : (2206255097 : ℕ)^2197*100000000000000^1685 ≤ 13938644830947^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206255097 10000000000 13938644830947 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015444041/2000000000 : ℝ)^2197 ≤ (10330426233601/25000000000000 : ℝ)^1685 := by
    have hnat : (1015444041 : ℕ)^2197*25000000000000^1685 ≤ 10330426233601^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015444041 2000000000 10330426233601 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396310771/10000000000 : ℝ), (-2206255097/10000000000 : ℝ), (1015444041/2000000000 : ℝ)] ![(22369825109807/50000000000000 : ℝ), (13938644830947/100000000000000 : ℝ), (10330426233601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396310771/10000000000 : ℝ)|^2197 ≤ (22369825109807/50000000000000 : ℝ)^1685
        have hw : |(5396310771/10000000000 : ℝ)|=(5396310771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2206255097/10000000000 : ℝ)|^2197 ≤ (13938644830947/100000000000000 : ℝ)^1685
        have hw : |(-2206255097/10000000000 : ℝ)|=(2206255097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015444041/2000000000 : ℝ)|^2197 ≤ (10330426233601/25000000000000 : ℝ)^1685
        have hw : |(1015444041/2000000000 : ℝ)|=(1015444041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s1_2 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2698155987/5000000000 : ℝ)*x 0 + (1269304721/2500000000 : ℝ)*x 1 + (-2206255219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698155987/5000000000 : ℝ)^2197 ≤ (44739663224047/100000000000000 : ℝ)^1685 := by
    have hnat : (2698155987 : ℕ)^2197*100000000000000^1685 ≤ 44739663224047^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698155987 5000000000 44739663224047 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269304721/2500000000 : ℝ)^2197 ≤ (2582605682277/6250000000000 : ℝ)^1685 := by
    have hnat : (1269304721 : ℕ)^2197*6250000000000^1685 ≤ 2582605682277^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269304721 2500000000 2582605682277 6250000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206255219/10000000000 : ℝ)^2197 ≤ (13938645835921/100000000000000 : ℝ)^1685 := by
    have hnat : (2206255219 : ℕ)^2197*100000000000000^1685 ≤ 13938645835921^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206255219 10000000000 13938645835921 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698155987/5000000000 : ℝ), (1269304721/2500000000 : ℝ), (-2206255219/10000000000 : ℝ)] ![(44739663224047/100000000000000 : ℝ), (2582605682277/6250000000000 : ℝ), (13938645835921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698155987/5000000000 : ℝ)|^2197 ≤ (44739663224047/100000000000000 : ℝ)^1685
        have hw : |(2698155987/5000000000 : ℝ)|=(2698155987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269304721/2500000000 : ℝ)|^2197 ≤ (2582605682277/6250000000000 : ℝ)^1685
        have hw : |(1269304721/2500000000 : ℝ)|=(1269304721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2206255219/10000000000 : ℝ)|^2197 ≤ (13938645835921/100000000000000 : ℝ)^1685
        have hw : |(-2206255219/10000000000 : ℝ)|=(2206255219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s1_3 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (427572783/1000000000 : ℝ)*x 0 + (3739557991/10000000000 : ℝ)*x 1 + (2439795749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427572783/1000000000 : ℝ)^2197 ≤ (33028561939031/100000000000000 : ℝ)^1685 := by
    have hnat : (427572783 : ℕ)^2197*100000000000000^1685 ≤ 33028561939031^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427572783 1000000000 33028561939031 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3739557991/10000000000 : ℝ)^2197 ≤ (6933595289149/25000000000000 : ℝ)^1685 := by
    have hnat : (3739557991 : ℕ)^2197*25000000000000^1685 ≤ 6933595289149^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3739557991 10000000000 6933595289149 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2439795749/5000000000 : ℝ)^2197 ≤ (39237056885731/100000000000000 : ℝ)^1685 := by
    have hnat : (2439795749 : ℕ)^2197*100000000000000^1685 ≤ 39237056885731^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439795749 5000000000 39237056885731 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427572783/1000000000 : ℝ), (3739557991/10000000000 : ℝ), (2439795749/5000000000 : ℝ)] ![(33028561939031/100000000000000 : ℝ), (6933595289149/25000000000000 : ℝ), (39237056885731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427572783/1000000000 : ℝ)|^2197 ≤ (33028561939031/100000000000000 : ℝ)^1685
        have hw : |(427572783/1000000000 : ℝ)|=(427572783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3739557991/10000000000 : ℝ)|^2197 ≤ (6933595289149/25000000000000 : ℝ)^1685
        have hw : |(3739557991/10000000000 : ℝ)|=(3739557991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2439795749/5000000000 : ℝ)|^2197 ≤ (39237056885731/100000000000000 : ℝ)^1685
        have hw : |(2439795749/5000000000 : ℝ)|=(2439795749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s1_4 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-385604439/2000000000 : ℝ)*x 0 + (5083362939/10000000000 : ℝ)*x 1 + (5596987901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385604439/2000000000 : ℝ)^2197 ≤ (11691975853143/100000000000000 : ℝ)^1685 := by
    have hnat : (385604439 : ℕ)^2197*100000000000000^1685 ≤ 11691975853143^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385604439 2000000000 11691975853143 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083362939/10000000000 : ℝ)^2197 ≤ (20693450688007/50000000000000 : ℝ)^1685 := by
    have hnat : (5083362939 : ℕ)^2197*50000000000000^1685 ≤ 20693450688007^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083362939 10000000000 20693450688007 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5596987901/10000000000 : ℝ)^2197 ≤ (46921122761363/100000000000000 : ℝ)^1685 := by
    have hnat : (5596987901 : ℕ)^2197*100000000000000^1685 ≤ 46921122761363^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596987901 10000000000 46921122761363 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385604439/2000000000 : ℝ), (5083362939/10000000000 : ℝ), (5596987901/10000000000 : ℝ)] ![(11691975853143/100000000000000 : ℝ), (20693450688007/50000000000000 : ℝ), (46921122761363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385604439/2000000000 : ℝ)|^2197 ≤ (11691975853143/100000000000000 : ℝ)^1685
        have hw : |(-385604439/2000000000 : ℝ)|=(385604439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083362939/10000000000 : ℝ)|^2197 ≤ (20693450688007/50000000000000 : ℝ)^1685
        have hw : |(5083362939/10000000000 : ℝ)|=(5083362939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5596987901/10000000000 : ℝ)|^2197 ≤ (46921122761363/100000000000000 : ℝ)^1685
        have hw : |(5596987901/10000000000 : ℝ)|=(5596987901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s1_5 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2629413199/5000000000 : ℝ)*x 0 + (-1686486707/10000000000 : ℝ)*x 1 + (5596987919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629413199/5000000000 : ℝ)^2197 ≤ (10814807743587/25000000000000 : ℝ)^1685 := by
    have hnat : (2629413199 : ℕ)^2197*25000000000000^1685 ≤ 10814807743587^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629413199 5000000000 10814807743587 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1686486707/10000000000 : ℝ)^2197 ≤ (490982302779/5000000000000 : ℝ)^1685 := by
    have hnat : (1686486707 : ℕ)^2197*5000000000000^1685 ≤ 490982302779^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686486707 10000000000 490982302779 5000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5596987919/10000000000 : ℝ)^2197 ≤ (23460561479057/50000000000000 : ℝ)^1685 := by
    have hnat : (5596987919 : ℕ)^2197*50000000000000^1685 ≤ 23460561479057^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596987919 10000000000 23460561479057 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629413199/5000000000 : ℝ), (-1686486707/10000000000 : ℝ), (5596987919/10000000000 : ℝ)] ![(10814807743587/25000000000000 : ℝ), (490982302779/5000000000000 : ℝ), (23460561479057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629413199/5000000000 : ℝ)|^2197 ≤ (10814807743587/25000000000000 : ℝ)^1685
        have hw : |(2629413199/5000000000 : ℝ)|=(2629413199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1686486707/10000000000 : ℝ)|^2197 ≤ (490982302779/5000000000000 : ℝ)^1685
        have hw : |(-1686486707/10000000000 : ℝ)|=(1686486707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5596987919/10000000000 : ℝ)|^2197 ≤ (23460561479057/50000000000000 : ℝ)^1685
        have hw : |(5596987919/10000000000 : ℝ)|=(5596987919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s1_6 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2629413169/5000000000 : ℝ)*x 0 + (139924697/250000000 : ℝ)*x 1 + (-1686486847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629413169/5000000000 : ℝ)^2197 ≤ (21629615165407/50000000000000 : ℝ)^1685 := by
    have hnat : (2629413169 : ℕ)^2197*50000000000000^1685 ≤ 21629615165407^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629413169 5000000000 21629615165407 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139924697/250000000 : ℝ)^2197 ≤ (46921122531821/100000000000000 : ℝ)^1685 := by
    have hnat : (139924697 : ℕ)^2197*100000000000000^1685 ≤ 46921122531821^1685*250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139924697 250000000 46921122531821 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1686486847/10000000000 : ℝ)^2197 ≤ (2454911779607/25000000000000 : ℝ)^1685 := by
    have hnat : (1686486847 : ℕ)^2197*25000000000000^1685 ≤ 2454911779607^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686486847 10000000000 2454911779607 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629413169/5000000000 : ℝ), (139924697/250000000 : ℝ), (-1686486847/10000000000 : ℝ)] ![(21629615165407/50000000000000 : ℝ), (46921122531821/100000000000000 : ℝ), (2454911779607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629413169/5000000000 : ℝ)|^2197 ≤ (21629615165407/50000000000000 : ℝ)^1685
        have hw : |(2629413169/5000000000 : ℝ)|=(2629413169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(139924697/250000000 : ℝ)|^2197 ≤ (46921122531821/100000000000000 : ℝ)^1685
        have hw : |(139924697/250000000 : ℝ)|=(139924697/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1686486847/10000000000 : ℝ)|^2197 ≤ (2454911779607/25000000000000 : ℝ)^1685
        have hw : |(-1686486847/10000000000 : ℝ)|=(1686486847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s1_7 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4276576379/10000000000 : ℝ)*x 0 + (4866276151/10000000000 : ℝ)*x 1 + (3753097403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4276576379/10000000000 : ℝ)^2197 ≤ (6607421733017/20000000000000 : ℝ)^1685 := by
    have hnat : (4276576379 : ℕ)^2197*20000000000000^1685 ≤ 6607421733017^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4276576379 10000000000 6607421733017 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4866276151/10000000000 : ℝ)^2197 ≤ (39097511526833/100000000000000 : ℝ)^1685 := by
    have hnat : (4866276151 : ℕ)^2197*100000000000000^1685 ≤ 39097511526833^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866276151 10000000000 39097511526833 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3753097403/10000000000 : ℝ)^2197 ≤ (6966344949403/25000000000000 : ℝ)^1685 := by
    have hnat : (3753097403 : ℕ)^2197*25000000000000^1685 ≤ 6966344949403^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3753097403 10000000000 6966344949403 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4276576379/10000000000 : ℝ), (4866276151/10000000000 : ℝ), (3753097403/10000000000 : ℝ)] ![(6607421733017/20000000000000 : ℝ), (39097511526833/100000000000000 : ℝ), (6966344949403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4276576379/10000000000 : ℝ)|^2197 ≤ (6607421733017/20000000000000 : ℝ)^1685
        have hw : |(4276576379/10000000000 : ℝ)|=(4276576379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4866276151/10000000000 : ℝ)|^2197 ≤ (39097511526833/100000000000000 : ℝ)^1685
        have hw : |(4866276151/10000000000 : ℝ)|=(4866276151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3753097403/10000000000 : ℝ)|^2197 ≤ (6966344949403/25000000000000 : ℝ)^1685
        have hw : |(3753097403/10000000000 : ℝ)|=(3753097403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1434_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7693/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18813/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1639/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1639/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1639/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1639/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1639/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1639/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (2083/100000 : ℝ) ^ (4393/1024 : ℝ) ≤ (6125073321399/100000000000000000000 : ℝ) := by
    have hpowers : (2083/100000 : ℝ)^4393 ≤ (6125073321399/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2083 : ℕ)^4393*100000000000000000000^1024 ≤ 6125073321399^1024*100000^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2083 100000 6125073321399 100000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2083/100000 : ℝ)) (X := (6125073321399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1639/6250 : ℝ) ^ (4393/1024 : ℝ) ≤ (320771466271995213/100000000000000000000 : ℝ) := by
    have hpowers : (1639/6250 : ℝ)^4393 ≤ (320771466271995213/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1639 : ℕ)^4393*100000000000000000000^1024 ≤ 320771466271995213^1024*6250^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1639 6250 320771466271995213 100000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1639/6250 : ℝ)) (X := (320771466271995213/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000006125073321399/50000000000000000000 : ℝ) ≤ (10000000285548591/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (50000006125073321399/50000000000000000000 : ℝ)^1024 ≤ (10000000285548591/10000000000000000 : ℝ)^4393 := by
      have hnat : (50000006125073321399 : ℕ)^1024*10000000000000000^4393 ≤ 10000000285548591^4393*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000006125073321399 50000000000000000000 10000000285548591 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000285548591/10000000000000000 : ℝ)) (X := (50000006125073321399/50000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25080194397836329153/25000000000000000000 : ℝ) ≤ (1000746808516441/1000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (25080194397836329153/25000000000000000000 : ℝ)^1024 ≤ (1000746808516441/1000000000000000 : ℝ)^4393 := by
      have hnat : (25080194397836329153 : ℕ)^1024*1000000000000000^4393 ≤ 1000746808516441^4393*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25080194397836329153 25000000000000000000 1000746808516441 1000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000746808516441/1000000000000000 : ℝ)) (X := (25080194397836329153/25000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50320771466271995213/50000000000000000000 : ℝ) ≤ (10014935884780229/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (50320771466271995213/50000000000000000000 : ℝ)^1024 ≤ (10014935884780229/10000000000000000 : ℝ)^4393 := by
      have hnat : (50320771466271995213 : ℕ)^1024*10000000000000000^4393 ≤ 10014935884780229^4393*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50320771466271995213 50000000000000000000 10014935884780229 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014935884780229/10000000000000000 : ℝ)) (X := (50320771466271995213/50000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6125073321399/100000000000000000000 : ℝ) ≤ ((241378896040229033377/241410000000000000000 : ℝ)+2*(7467799615819/2414100000000000 : ℝ)*(2083/100000 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (241378896040229033377/241410000000000000000 : ℝ)+2*(7467799615819/2414100000000000 : ℝ)*(2083/100000 : ℝ)=(10000000285548591/10000000000000000 : ℝ) by norm_num, show 1+2*(6125073321399/100000000000000000000 : ℝ)=(50000006125073321399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(320771466271995213/100000000000000000000 : ℝ)+(6125073321399/100000000000000000000 : ℝ) ≤ ((241378896040229033377/241410000000000000000 : ℝ)+(7467799615819/2414100000000000 : ℝ)*((1639/6250 : ℝ)+(2083/100000 : ℝ)))^(4393/1024 : ℝ) := by
    rw [show (241378896040229033377/241410000000000000000 : ℝ)+(7467799615819/2414100000000000 : ℝ)*((1639/6250 : ℝ)+(2083/100000 : ℝ))=(1000746808516441/1000000000000000 : ℝ) by norm_num, show 1+(320771466271995213/100000000000000000000 : ℝ)+(6125073321399/100000000000000000000 : ℝ)=(25080194397836329153/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(320771466271995213/100000000000000000000 : ℝ) ≤ ((241378896040229033377/241410000000000000000 : ℝ)+2*(7467799615819/2414100000000000 : ℝ)*(1639/6250 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (241378896040229033377/241410000000000000000 : ℝ)+2*(7467799615819/2414100000000000 : ℝ)*(1639/6250 : ℝ)=(10014935884780229/10000000000000000 : ℝ) by norm_num, show 1+2*(320771466271995213/100000000000000000000 : ℝ)=(50320771466271995213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (241378896040229033377/241410000000000000000 : ℝ)*(X 1 0+X 2 0)+(7467799615819/2414100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (2083/100000 : ℝ)) (hi := (1639/6250 : ℝ)) (c := (241378896040229033377/241410000000000000000 : ℝ)) (alpha := (7467799615819/2414100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (241378896040229033377/241410000000000000000 : ℝ)*(X 0 1+X 2 1)+(7467799615819/2414100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (2083/100000 : ℝ)) (hi := (1639/6250 : ℝ)) (c := (241378896040229033377/241410000000000000000 : ℝ)) (alpha := (7467799615819/2414100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (241378896040229033377/241410000000000000000 : ℝ)*(X 0 2+X 1 2)+(7467799615819/2414100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (2083/100000 : ℝ)) (hi := (1639/6250 : ℝ)) (c := (241378896040229033377/241410000000000000000 : ℝ)) (alpha := (7467799615819/2414100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1927631063/10000000000 : ℝ)*X 0 0+(87550561/156250000 : ℝ)*X 0 1+(2538609299/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5396310771/10000000000 : ℝ)*X 1 0+(-2206255097/10000000000 : ℝ)*X 1 1+(1015444041/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2698155987/5000000000 : ℝ)*X 2 0+(1269304721/2500000000 : ℝ)*X 2 1+(-2206255219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((427572783/1000000000 : ℝ)*X 0 0+(3739557991/10000000000 : ℝ)*X 0 1+(2439795749/5000000000 : ℝ)*X 0 2+(427572783/1000000000 : ℝ)*X 1 0+(3739557991/10000000000 : ℝ)*X 1 1+(2439795749/5000000000 : ℝ)*X 1 2+(427572783/1000000000 : ℝ)*X 2 0+(3739557991/10000000000 : ℝ)*X 2 1+(2439795749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-385604439/2000000000 : ℝ)*X 0 0+(5083362939/10000000000 : ℝ)*X 0 1+(5596987901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629413199/5000000000 : ℝ)*X 1 0+(-1686486707/10000000000 : ℝ)*X 1 1+(5596987919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629413169/5000000000 : ℝ)*X 2 0+(139924697/250000000 : ℝ)*X 2 1+(-1686486847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4276576379/10000000000 : ℝ)*X 0 0+(4866276151/10000000000 : ℝ)*X 0 1+(3753097403/10000000000 : ℝ)*X 0 2+(4276576379/10000000000 : ℝ)*X 1 0+(4866276151/10000000000 : ℝ)*X 1 1+(3753097403/10000000000 : ℝ)*X 1 2+(4276576379/10000000000 : ℝ)*X 2 0+(4866276151/10000000000 : ℝ)*X 2 1+(3753097403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127463232310742909427425523/77375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10755261/6250000000000 : ℝ)*(base19) + (253756957/50000000000000 : ℝ)*(base23) + (2636049/20000000000000 : ℝ)*(upper2) + (615141/2000000000000 : ℝ)*(upper3) + (60873091/100000000000000 : ℝ)*(upper4) + (694565417660913/50000000000000 : ℝ)*(major0) + (694565417660913/50000000000000 : ℝ)*(major1) + (694565417660913/50000000000000 : ℝ)*(major2) + (190108383924329/10000000000000 : ℝ)*(sp0) + (1901090582948157/100000000000000 : ℝ)*(sp1) + (1901090247518419/100000000000000 : ℝ)*(sp2) + (877168646863621/100000000000000 : ℝ)*(sp3) + (6915789043/100000000000000 : ℝ)*(sp4) + (2213836223/100000000000000 : ℝ)*(sp7) + (219292715174961/25000000000000 : ℝ)*(f.failure) + (475272688758083/25000000000000 : ℝ)*(f.sum) + (96373730384939/20117500000000000000000000000 : ℝ)*base65 + (26815591618279831067/4023500000000000000000000000000000 : ℝ)*base67 + (11126859987558331067/4023500000000000000000000000000000 : ℝ)*base69 + (32077430877014331067/4023500000000000000000000000000000 : ℝ)*base71 + (79524780127573/40235000000000000000000000000 : ℝ)*base73 + (21532290753041331067/4023500000000000000000000000000000 : ℝ)*base75 + (33358714214627831067/4023500000000000000000000000000000 : ℝ)*base77 + (10349730794906668933/4023500000000000000000000000000000 : ℝ)*base80 + (1897482547189/5029375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (32156451/2500000000000000000000 : ℝ)*base90 + (32156451/2500000000000000000000 : ℝ)*base92 + (32156451/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12703892530832383554688483767/4023500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4027019/25000000000000 : ℝ)*(base1) + (738953079/100000000000000 : ℝ)*(base19) + (707576659/100000000000000 : ℝ)*(base23) + (83972971/100000000000000 : ℝ)*(upper3) + (30113289/50000000000000 : ℝ)*(upper5) + (1422636993717929/100000000000000 : ℝ)*(major0) + (1422636993717929/100000000000000 : ℝ)*(major1) + (1422636993717929/100000000000000 : ℝ)*(major2) + (2269069311/50000000000000 : ℝ)*(sp1) + (4187613347/100000000000000 : ℝ)*(sp2) + (1946945472699417/100000000000000 : ℝ)*(sp4) + (48673504487491/2500000000000 : ℝ)*(sp5) + (243367570175167/12500000000000 : ℝ)*(sp6) + (28072762796531/3125000000000 : ℝ)*(sp7) + (224582106399267/25000000000000 : ℝ)*(f.failure) + (973472728295671/50000000000000 : ℝ)*(f.sum) + (45073620701743/60352500000000000000000000000 : ℝ)*base65 + (17072901809105583767/24141000000000000000000000000000000 : ℝ)*base68 + (135910905254436416233/24141000000000000000000000000000000 : ℝ)*base69 + (62110111827699416233/24141000000000000000000000000000000 : ℝ)*base71 + (67629683065639/120705000000000000000000000000 : ℝ)*base74 + (172234589616063416233/24141000000000000000000000000000000 : ℝ)*base75 + (116299368255524583767/24141000000000000000000000000000000 : ℝ)*base78 + (103102303063929416233/24141000000000000000000000000000000 : ℝ)*base79 + (164392569151049/30176250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (11121703/2500000000000000000000 : ℝ)*base89 + (11121703/2500000000000000000000 : ℝ)*base91 + (11121703/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1434_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7693/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18813/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1434_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1434_s2_0 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1960394383/10000000000 : ℝ)*x 0 + (5457056021/10000000000 : ℝ)*x 1 + (2601151753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1960394383/10000000000 : ℝ)^2197 ≤ (11948589801717/100000000000000 : ℝ)^1685 := by
    have hnat : (1960394383 : ℕ)^2197*100000000000000^1685 ≤ 11948589801717^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960394383 10000000000 11948589801717 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457056021/10000000000 : ℝ)^2197 ≤ (11349356655923/25000000000000 : ℝ)^1685 := by
    have hnat : (5457056021 : ℕ)^2197*25000000000000^1685 ≤ 11349356655923^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457056021 10000000000 11349356655923 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601151753/5000000000 : ℝ)^2197 ≤ (10663495890463/25000000000000 : ℝ)^1685 := by
    have hnat : (2601151753 : ℕ)^2197*25000000000000^1685 ≤ 10663495890463^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601151753 5000000000 10663495890463 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1960394383/10000000000 : ℝ), (5457056021/10000000000 : ℝ), (2601151753/5000000000 : ℝ)] ![(11948589801717/100000000000000 : ℝ), (11349356655923/25000000000000 : ℝ), (10663495890463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1960394383/10000000000 : ℝ)|^2197 ≤ (11948589801717/100000000000000 : ℝ)^1685
        have hw : |(-1960394383/10000000000 : ℝ)|=(1960394383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457056021/10000000000 : ℝ)|^2197 ≤ (11349356655923/25000000000000 : ℝ)^1685
        have hw : |(5457056021/10000000000 : ℝ)|=(5457056021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601151753/5000000000 : ℝ)|^2197 ≤ (10663495890463/25000000000000 : ℝ)^1685
        have hw : |(2601151753/5000000000 : ℝ)|=(2601151753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s2_1 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214392963/400000000 : ℝ)*x 0 + (-1045717307/5000000000 : ℝ)*x 1 + (5202303379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214392963/400000000 : ℝ)^2197 ≤ (354765078101/800000000000 : ℝ)^1685 := by
    have hnat : (214392963 : ℕ)^2197*800000000000^1685 ≤ 354765078101^1685*400000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214392963 400000000 354765078101 800000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045717307/5000000000 : ℝ)^2197 ≤ (6500191504441/50000000000000 : ℝ)^1685 := by
    have hnat : (1045717307 : ℕ)^2197*50000000000000^1685 ≤ 6500191504441^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045717307 5000000000 6500191504441 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5202303379/10000000000 : ℝ)^2197 ≤ (42653982204171/100000000000000 : ℝ)^1685 := by
    have hnat : (5202303379 : ℕ)^2197*100000000000000^1685 ≤ 42653982204171^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202303379 10000000000 42653982204171 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214392963/400000000 : ℝ), (-1045717307/5000000000 : ℝ), (5202303379/10000000000 : ℝ)] ![(354765078101/800000000000 : ℝ), (6500191504441/50000000000000 : ℝ), (42653982204171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214392963/400000000 : ℝ)|^2197 ≤ (354765078101/800000000000 : ℝ)^1685
        have hw : |(214392963/400000000 : ℝ)|=(214392963/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045717307/5000000000 : ℝ)|^2197 ≤ (6500191504441/50000000000000 : ℝ)^1685
        have hw : |(-1045717307/5000000000 : ℝ)|=(1045717307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5202303379/10000000000 : ℝ)|^2197 ≤ (42653982204171/100000000000000 : ℝ)^1685
        have hw : |(5202303379/10000000000 : ℝ)|=(5202303379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s2_2 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267991183/500000000 : ℝ)*x 0 + (5202303841/10000000000 : ℝ)*x 1 + (-2091434559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267991183/500000000 : ℝ)^2197 ≤ (2771601892857/6250000000000 : ℝ)^1685 := by
    have hnat : (267991183 : ℕ)^2197*6250000000000^1685 ≤ 2771601892857^1685*500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267991183 500000000 2771601892857 6250000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202303841/10000000000 : ℝ)^2197 ≤ (42653987143137/100000000000000 : ℝ)^1685 := by
    have hnat : (5202303841 : ℕ)^2197*100000000000000^1685 ≤ 42653987143137^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202303841 10000000000 42653987143137 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091434559/10000000000 : ℝ)^2197 ≤ (6500191281559/50000000000000 : ℝ)^1685 := by
    have hnat : (2091434559 : ℕ)^2197*50000000000000^1685 ≤ 6500191281559^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091434559 10000000000 6500191281559 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267991183/500000000 : ℝ), (5202303841/10000000000 : ℝ), (-2091434559/10000000000 : ℝ)] ![(2771601892857/6250000000000 : ℝ), (42653987143137/100000000000000 : ℝ), (6500191281559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267991183/500000000 : ℝ)|^2197 ≤ (2771601892857/6250000000000 : ℝ)^1685
        have hw : |(267991183/500000000 : ℝ)|=(267991183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202303841/10000000000 : ℝ)|^2197 ≤ (42653987143137/100000000000000 : ℝ)^1685
        have hw : |(5202303841/10000000000 : ℝ)|=(5202303841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091434559/10000000000 : ℝ)|^2197 ≤ (6500191281559/50000000000000 : ℝ)^1685
        have hw : |(-2091434559/10000000000 : ℝ)|=(2091434559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s2_3 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298868119/10000000000 : ℝ)*x 0 + (100768637/250000000 : ℝ)*x 1 + (114571763/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298868119/10000000000 : ℝ)^2197 ≤ (6652363826223/20000000000000 : ℝ)^1685 := by
    have hnat : (4298868119 : ℕ)^2197*20000000000000^1685 ≤ 6652363826223^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298868119 10000000000 6652363826223 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100768637/250000000 : ℝ)^2197 ≤ (6116581005757/20000000000000 : ℝ)^1685 := by
    have hnat : (100768637 : ℕ)^2197*20000000000000^1685 ≤ 6116581005757^1685*250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100768637 250000000 6116581005757 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114571763/250000000 : ℝ)^2197 ≤ (18077637913001/50000000000000 : ℝ)^1685 := by
    have hnat : (114571763 : ℕ)^2197*50000000000000^1685 ≤ 18077637913001^1685*250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114571763 250000000 18077637913001 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298868119/10000000000 : ℝ), (100768637/250000000 : ℝ), (114571763/250000000 : ℝ)] ![(6652363826223/20000000000000 : ℝ), (6116581005757/20000000000000 : ℝ), (18077637913001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298868119/10000000000 : ℝ)|^2197 ≤ (6652363826223/20000000000000 : ℝ)^1685
        have hw : |(4298868119/10000000000 : ℝ)|=(4298868119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100768637/250000000 : ℝ)|^2197 ≤ (6116581005757/20000000000000 : ℝ)^1685
        have hw : |(100768637/250000000 : ℝ)|=(100768637/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114571763/250000000 : ℝ)|^2197 ≤ (18077637913001/50000000000000 : ℝ)^1685
        have hw : |(114571763/250000000 : ℝ)|=(114571763/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s2_4 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-490109741/2500000000 : ℝ)*x 0 + (2601876843/5000000000 : ℝ)*x 1 + (5455593973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490109741/2500000000 : ℝ)^2197 ≤ (11948944088263/100000000000000 : ℝ)^1685 := by
    have hnat : (490109741 : ℕ)^2197*100000000000000^1685 ≤ 11948944088263^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490109741 2500000000 11948944088263 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601876843/5000000000 : ℝ)^2197 ≤ (21334743613253/50000000000000 : ℝ)^1685 := by
    have hnat : (2601876843 : ℕ)^2197*50000000000000^1685 ≤ 21334743613253^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601876843 5000000000 21334743613253 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455593973/10000000000 : ℝ)^2197 ≤ (45381568677983/100000000000000 : ℝ)^1685 := by
    have hnat : (5455593973 : ℕ)^2197*100000000000000^1685 ≤ 45381568677983^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455593973 10000000000 45381568677983 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490109741/2500000000 : ℝ), (2601876843/5000000000 : ℝ), (5455593973/10000000000 : ℝ)] ![(11948944088263/100000000000000 : ℝ), (21334743613253/50000000000000 : ℝ), (45381568677983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490109741/2500000000 : ℝ)|^2197 ≤ (11948944088263/100000000000000 : ℝ)^1685
        have hw : |(-490109741/2500000000 : ℝ)|=(490109741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601876843/5000000000 : ℝ)|^2197 ≤ (21334743613253/50000000000000 : ℝ)^1685
        have hw : |(2601876843/5000000000 : ℝ)|=(2601876843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455593973/10000000000 : ℝ)|^2197 ≤ (45381568677983/100000000000000 : ℝ)^1685
        have hw : |(5455593973/10000000000 : ℝ)|=(5455593973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s2_5 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (330846799/625000000 : ℝ)*x 0 + (-1838143601/10000000000 : ℝ)*x 1 + (1363898637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330846799/625000000 : ℝ)^2197 ≤ (43632021139887/100000000000000 : ℝ)^1685 := by
    have hnat : (330846799 : ℕ)^2197*100000000000000^1685 ≤ 43632021139887^1685*625000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330846799 625000000 43632021139887 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1838143601/10000000000 : ℝ)^2197 ≤ (10986403926519/100000000000000 : ℝ)^1685 := by
    have hnat : (1838143601 : ℕ)^2197*100000000000000^1685 ≤ 10986403926519^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838143601 10000000000 10986403926519 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363898637/2500000000 : ℝ)^2197 ≤ (11345393728601/25000000000000 : ℝ)^1685 := by
    have hnat : (1363898637 : ℕ)^2197*25000000000000^1685 ≤ 11345393728601^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363898637 2500000000 11345393728601 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330846799/625000000 : ℝ), (-1838143601/10000000000 : ℝ), (1363898637/2500000000 : ℝ)] ![(43632021139887/100000000000000 : ℝ), (10986403926519/100000000000000 : ℝ), (11345393728601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330846799/625000000 : ℝ)|^2197 ≤ (43632021139887/100000000000000 : ℝ)^1685
        have hw : |(330846799/625000000 : ℝ)|=(330846799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1838143601/10000000000 : ℝ)|^2197 ≤ (10986403926519/100000000000000 : ℝ)^1685
        have hw : |(-1838143601/10000000000 : ℝ)|=(1838143601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363898637/2500000000 : ℝ)|^2197 ≤ (11345393728601/25000000000000 : ℝ)^1685
        have hw : |(1363898637/2500000000 : ℝ)|=(1363898637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s2_6 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2646774289/5000000000 : ℝ)*x 0 + (1363898627/2500000000 : ℝ)*x 1 + (-1838143941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646774289/5000000000 : ℝ)^2197 ≤ (21816009462999/50000000000000 : ℝ)^1685 := by
    have hnat : (2646774289 : ℕ)^2197*50000000000000^1685 ≤ 21816009462999^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646774289 5000000000 21816009462999 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363898627/2500000000 : ℝ)^2197 ≤ (22690787240283/50000000000000 : ℝ)^1685 := by
    have hnat : (1363898627 : ℕ)^2197*50000000000000^1685 ≤ 22690787240283^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363898627 2500000000 22690787240283 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1838143941/10000000000 : ℝ)^2197 ≤ (10986406576149/100000000000000 : ℝ)^1685 := by
    have hnat : (1838143941 : ℕ)^2197*100000000000000^1685 ≤ 10986406576149^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838143941 10000000000 10986406576149 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646774289/5000000000 : ℝ), (1363898627/2500000000 : ℝ), (-1838143941/10000000000 : ℝ)] ![(21816009462999/50000000000000 : ℝ), (22690787240283/50000000000000 : ℝ), (10986406576149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646774289/5000000000 : ℝ)|^2197 ≤ (21816009462999/50000000000000 : ℝ)^1685
        have hw : |(2646774289/5000000000 : ℝ)|=(2646774289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363898627/2500000000 : ℝ)|^2197 ≤ (22690787240283/50000000000000 : ℝ)^1685
        have hw : |(1363898627/2500000000 : ℝ)|=(1363898627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1838143941/10000000000 : ℝ)|^2197 ≤ (10986406576149/100000000000000 : ℝ)^1685
        have hw : |(-1838143941/10000000000 : ℝ)|=(1838143941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s2_7 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298964679/10000000000 : ℝ)*x 0 + (91594561/200000000 : ℝ)*x 1 + (806782753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298964679/10000000000 : ℝ)^2197 ≤ (33262793269747/100000000000000 : ℝ)^1685 := by
    have hnat : (4298964679 : ℕ)^2197*100000000000000^1685 ≤ 33262793269747^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298964679 10000000000 33262793269747 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91594561/200000000 : ℝ)^2197 ≤ (9030738607121/25000000000000 : ℝ)^1685 := by
    have hnat : (91594561 : ℕ)^2197*25000000000000^1685 ≤ 9030738607121^1685*200000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91594561 200000000 9030738607121 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806782753/2000000000 : ℝ)^2197 ≤ (30614252290117/100000000000000 : ℝ)^1685 := by
    have hnat : (806782753 : ℕ)^2197*100000000000000^1685 ≤ 30614252290117^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806782753 2000000000 30614252290117 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298964679/10000000000 : ℝ), (91594561/200000000 : ℝ), (806782753/2000000000 : ℝ)] ![(33262793269747/100000000000000 : ℝ), (9030738607121/25000000000000 : ℝ), (30614252290117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298964679/10000000000 : ℝ)|^2197 ≤ (33262793269747/100000000000000 : ℝ)^1685
        have hw : |(4298964679/10000000000 : ℝ)|=(4298964679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91594561/200000000 : ℝ)|^2197 ≤ (9030738607121/25000000000000 : ℝ)^1685
        have hw : |(91594561/200000000 : ℝ)|=(91594561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806782753/2000000000 : ℝ)|^2197 ≤ (30614252290117/100000000000000 : ℝ)^1685
        have hw : |(806782753/2000000000 : ℝ)|=(806782753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1434_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18813/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7693/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5197/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1973/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18813/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7693/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18813/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7693/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18813/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7693/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18813/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7693/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18813/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7693/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18813/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7693/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7693/100000 : ℝ) ^ (4393/1024 : ℝ) ≤ (1664589612825389/100000000000000000000 : ℝ) := by
    have hpowers : (7693/100000 : ℝ)^4393 ≤ (1664589612825389/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7693 : ℕ)^4393*100000000000000000000^1024 ≤ 1664589612825389^1024*100000^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7693 100000 1664589612825389 100000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7693/100000 : ℝ)) (X := (1664589612825389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18813/100000 : ℝ) ^ (4393/1024 : ℝ) ≤ (38580399542402461/50000000000000000000 : ℝ) := by
    have hpowers : (18813/100000 : ℝ)^4393 ≤ (38580399542402461/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18813 : ℕ)^4393*50000000000000000000^1024 ≤ 38580399542402461^1024*100000^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18813 100000 38580399542402461 50000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18813/100000 : ℝ)) (X := (38580399542402461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001664589612825389/50000000000000000000 : ℝ) ≤ (10000077601548109/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (50001664589612825389/50000000000000000000 : ℝ)^1024 ≤ (10000077601548109/10000000000000000 : ℝ)^4393 := by
      have hnat : (50001664589612825389 : ℕ)^1024*10000000000000000^4393 ≤ 10000077601548109^4393*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001664589612825389 50000000000000000000 10000077601548109 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000077601548109/10000000000000000 : ℝ)) (X := (50001664589612825389/50000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078825388697630311/100000000000000000000 : ℝ) ≤ (312557401556477/312500000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (100078825388697630311/100000000000000000000 : ℝ)^1024 ≤ (312557401556477/312500000000000 : ℝ)^4393 := by
      have hnat : (100078825388697630311 : ℕ)^1024*312500000000000^4393 ≤ 312557401556477^4393*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078825388697630311 100000000000000000000 312557401556477 312500000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312557401556477/312500000000000 : ℝ)) (X := (100078825388697630311/100000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25038580399542402461/25000000000000000000 : ℝ) ≤ (10003596098066419/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (25038580399542402461/25000000000000000000 : ℝ)^1024 ≤ (10003596098066419/10000000000000000 : ℝ)^4393 := by
      have hnat : (25038580399542402461 : ℕ)^1024*10000000000000000^4393 ≤ 10003596098066419^4393*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25038580399542402461 25000000000000000000 10003596098066419 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003596098066419/10000000000000000 : ℝ)) (X := (25038580399542402461/25000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1664589612825389/100000000000000000000 : ℝ) ≤ ((444695180541998453/444800000000000000 : ℝ)+2*(351849651831/222400000000000 : ℝ)*(7693/100000 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (444695180541998453/444800000000000000 : ℝ)+2*(351849651831/222400000000000 : ℝ)*(7693/100000 : ℝ)=(10000077601548109/10000000000000000 : ℝ) by norm_num, show 1+2*(1664589612825389/100000000000000000000 : ℝ)=(50001664589612825389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38580399542402461/50000000000000000000 : ℝ)+(1664589612825389/100000000000000000000 : ℝ) ≤ ((444695180541998453/444800000000000000 : ℝ)+(351849651831/222400000000000 : ℝ)*((18813/100000 : ℝ)+(7693/100000 : ℝ)))^(4393/1024 : ℝ) := by
    rw [show (444695180541998453/444800000000000000 : ℝ)+(351849651831/222400000000000 : ℝ)*((18813/100000 : ℝ)+(7693/100000 : ℝ))=(312557401556477/312500000000000 : ℝ) by norm_num, show 1+(38580399542402461/50000000000000000000 : ℝ)+(1664589612825389/100000000000000000000 : ℝ)=(100078825388697630311/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38580399542402461/50000000000000000000 : ℝ) ≤ ((444695180541998453/444800000000000000 : ℝ)+2*(351849651831/222400000000000 : ℝ)*(18813/100000 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (444695180541998453/444800000000000000 : ℝ)+2*(351849651831/222400000000000 : ℝ)*(18813/100000 : ℝ)=(10003596098066419/10000000000000000 : ℝ) by norm_num, show 1+2*(38580399542402461/50000000000000000000 : ℝ)=(25038580399542402461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (444695180541998453/444800000000000000 : ℝ)*(X 1 0+X 2 0)+(351849651831/222400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (7693/100000 : ℝ)) (hi := (18813/100000 : ℝ)) (c := (444695180541998453/444800000000000000 : ℝ)) (alpha := (351849651831/222400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (444695180541998453/444800000000000000 : ℝ)*(X 0 1+X 2 1)+(351849651831/222400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (7693/100000 : ℝ)) (hi := (18813/100000 : ℝ)) (c := (444695180541998453/444800000000000000 : ℝ)) (alpha := (351849651831/222400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (444695180541998453/444800000000000000 : ℝ)*(X 0 2+X 1 2)+(351849651831/222400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (7693/100000 : ℝ)) (hi := (18813/100000 : ℝ)) (c := (444695180541998453/444800000000000000 : ℝ)) (alpha := (351849651831/222400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1960394383/10000000000 : ℝ)*X 0 0+(5457056021/10000000000 : ℝ)*X 0 1+(2601151753/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214392963/400000000 : ℝ)*X 1 0+(-1045717307/5000000000 : ℝ)*X 1 1+(5202303379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267991183/500000000 : ℝ)*X 2 0+(5202303841/10000000000 : ℝ)*X 2 1+(-2091434559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298868119/10000000000 : ℝ)*X 0 0+(100768637/250000000 : ℝ)*X 0 1+(114571763/250000000 : ℝ)*X 0 2+(4298868119/10000000000 : ℝ)*X 1 0+(100768637/250000000 : ℝ)*X 1 1+(114571763/250000000 : ℝ)*X 1 2+(4298868119/10000000000 : ℝ)*X 2 0+(100768637/250000000 : ℝ)*X 2 1+(114571763/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-490109741/2500000000 : ℝ)*X 0 0+(2601876843/5000000000 : ℝ)*X 0 1+(5455593973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330846799/625000000 : ℝ)*X 1 0+(-1838143601/10000000000 : ℝ)*X 1 1+(1363898637/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646774289/5000000000 : ℝ)*X 2 0+(1363898627/2500000000 : ℝ)*X 2 1+(-1838143941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298964679/10000000000 : ℝ)*X 0 0+(91594561/200000000 : ℝ)*X 0 1+(806782753/2000000000 : ℝ)*X 0 2+(4298964679/10000000000 : ℝ)*X 1 0+(91594561/200000000 : ℝ)*X 1 1+(806782753/2000000000 : ℝ)*X 1 2+(4298964679/10000000000 : ℝ)*X 2 0+(91594561/200000000 : ℝ)*X 2 1+(806782753/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94721338005716512690636623/11120000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (605888777/50000000000000 : ℝ)*(base19) + (65080969/10000000000000 : ℝ)*(base23) + (137764687/100000000000000 : ℝ)*(lower2) + (27297363/10000000000000 : ℝ)*(upper3) + (14997027/25000000000000 : ℝ)*(upper5) + (1434150188528901/50000000000000 : ℝ)*(major0) + (1434150188528901/50000000000000 : ℝ)*(major1) + (1434150188528901/50000000000000 : ℝ)*(major2) + (785078665632377/20000000000000 : ℝ)*(sp0) + (490675290493481/12500000000000 : ℝ)*(sp1) + (7666802509601/195312500000 : ℝ)*(sp2) + (90559466355213/5000000000000 : ℝ)*(sp3) + (10207563517/100000000000000 : ℝ)*(sp4) + (7607349067/100000000000000 : ℝ)*(sp7) + (1811196934453327/100000000000000 : ℝ)*(f.failure) + (1962701767862701/50000000000000 : ℝ)*(f.sum) + (1966905312669/5560000000000000000000000000 : ℝ)*base66 + (64193424313972153/22240000000000000000000000000000 : ℝ)*base67 + (178123008257812153/22240000000000000000000000000000 : ℝ)*base69 + (39960172409332153/22240000000000000000000000000000 : ℝ)*base71 + (6790985869949/5560000000000000000000000000 : ℝ)*base74 + (243970609985972153/22240000000000000000000000000000 : ℝ)*base75 + (139406214092532153/22240000000000000000000000000000 : ℝ)*base77 + (299292096353172153/22240000000000000000000000000000 : ℝ)*base79 + (40770544222411/5560000000000000000000000000 : ℝ)*base81 + (104897757/10000000000000000000000 : ℝ)*base90 + (104897757/10000000000000000000000 : ℝ)*base92 + (104897757/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123093367040400340546678083/22240000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155295503/100000000000000 : ℝ)*(base19) + (13215307/6250000000000 : ℝ)*(base23) + (91901797/50000000000000 : ℝ)*(upper3) + (3379321/3125000000000 : ℝ)*(lower4) + (2901444849262237/100000000000000 : ℝ)*(major0) + (2901444849262237/100000000000000 : ℝ)*(major1) + (2901444849262237/100000000000000 : ℝ)*(major2) + (908739727/20000000000000 : ℝ)*(sp1) + (5054072577/100000000000000 : ℝ)*(sp2) + (129031821/100000000000000 : ℝ)*(sp3) + (397076340251937/10000000000000 : ℝ)*(sp4) + (248172418970327/6250000000000 : ℝ)*(sp5) + (1985379068500941/50000000000000 : ℝ)*(sp6) + (1832125982480823/100000000000000 : ℝ)*(sp7) + (458031527878161/25000000000000 : ℝ)*(f.failure) + (397076340251937/10000000000000 : ℝ)*(f.sum) + (27807298930373/11120000000000000000000000000 : ℝ)*base66 + (49217572126786639/44480000000000000000000000000000 : ℝ)*base68 + (168529798745213361/44480000000000000000000000000000 : ℝ)*base69 + (22797296312706639/44480000000000000000000000000000 : ℝ)*base72 + (5628549788987/11120000000000000000000000000 : ℝ)*base73 + (192205927638466639/44480000000000000000000000000000 : ℝ)*base76 + (91888151905853361/44480000000000000000000000000000 : ℝ)*base77 + (303680290375426639/44480000000000000000000000000000 : ℝ)*base80 + (5301086894747/11120000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4852349/2500000000000000000000 : ℝ)*base89 + (4852349/2500000000000000000000 : ℝ)*base91 + (4852349/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1434_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18813/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7693/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5197/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1973/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1434_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1434_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5197/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1973/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1434_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1434_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1434_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5197/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1973/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1434_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

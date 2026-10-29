-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:03.434495+00:00
-- url     : https://prove2.me/submissions/52942f01-ede5-4633-af02-1448edf9d5bd

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
theorem support_rectangle_w1421_s3_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-395306119/2000000000 : ℝ)*x 0 + (2709051443/5000000000 : ℝ)*x 1 + (5237984089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395306119/2000000000 : ℝ)^4381 ≤ (12053967085177/100000000000000 : ℝ)^3357 := by
    have hnat : (395306119 : ℕ)^4381*100000000000000^3357 ≤ 12053967085177^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395306119 2000000000 12053967085177 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709051443/5000000000 : ℝ)^4381 ≤ (2247147319787/5000000000000 : ℝ)^3357 := by
    have hnat : (2709051443 : ℕ)^4381*5000000000000^3357 ≤ 2247147319787^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709051443 5000000000 2247147319787 5000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237984089/10000000000 : ℝ)^4381 ≤ (10750771624021/25000000000000 : ℝ)^3357 := by
    have hnat : (5237984089 : ℕ)^4381*25000000000000^3357 ≤ 10750771624021^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237984089 10000000000 10750771624021 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-395306119/2000000000 : ℝ), (2709051443/5000000000 : ℝ), (5237984089/10000000000 : ℝ)] ![(12053967085177/100000000000000 : ℝ), (2247147319787/5000000000000 : ℝ), (10750771624021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-395306119/2000000000 : ℝ)|^4381 ≤ (12053967085177/100000000000000 : ℝ)^3357
        have hw : |(-395306119/2000000000 : ℝ)|=(395306119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709051443/5000000000 : ℝ)|^4381 ≤ (2247147319787/5000000000000 : ℝ)^3357
        have hw : |(2709051443/5000000000 : ℝ)|=(2709051443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237984089/10000000000 : ℝ)|^4381 ≤ (10750771624021/25000000000000 : ℝ)^3357
        have hw : |(5237984089/10000000000 : ℝ)|=(5237984089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s3_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674968693/5000000000 : ℝ)*x 0 + (-2068423039/10000000000 : ℝ)*x 1 + (104759681/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674968693/5000000000 : ℝ)^4381 ≤ (1768258432747/4000000000000 : ℝ)^3357 := by
    have hnat : (2674968693 : ℕ)^4381*4000000000000^3357 ≤ 1768258432747^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674968693 5000000000 1768258432747 4000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068423039/10000000000 : ℝ)^4381 ≤ (255809061827/2000000000000 : ℝ)^3357 := by
    have hnat : (2068423039 : ℕ)^4381*2000000000000^3357 ≤ 255809061827^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068423039 10000000000 255809061827 2000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104759681/200000000 : ℝ)^4381 ≤ (5375385759779/12500000000000 : ℝ)^3357 := by
    have hnat : (104759681 : ℕ)^4381*12500000000000^3357 ≤ 5375385759779^3357*200000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104759681 200000000 5375385759779 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674968693/5000000000 : ℝ), (-2068423039/10000000000 : ℝ), (104759681/200000000 : ℝ)] ![(1768258432747/4000000000000 : ℝ), (255809061827/2000000000000 : ℝ), (5375385759779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674968693/5000000000 : ℝ)|^4381 ≤ (1768258432747/4000000000000 : ℝ)^3357
        have hw : |(2674968693/5000000000 : ℝ)|=(2674968693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068423039/10000000000 : ℝ)|^4381 ≤ (255809061827/2000000000000 : ℝ)^3357
        have hw : |(-2068423039/10000000000 : ℝ)|=(2068423039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104759681/200000000 : ℝ)|^4381 ≤ (5375385759779/12500000000000 : ℝ)^3357
        have hw : |(104759681/200000000 : ℝ)|=(104759681/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s3_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349937389/10000000000 : ℝ)*x 0 + (261899203/500000000 : ℝ)*x 1 + (-2068423021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349937389/10000000000 : ℝ)^4381 ≤ (22103230425513/50000000000000 : ℝ)^3357 := by
    have hnat : (5349937389 : ℕ)^4381*50000000000000^3357 ≤ 22103230425513^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349937389 10000000000 22103230425513 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261899203/500000000 : ℝ)^4381 ≤ (21501543092687/50000000000000 : ℝ)^3357 := by
    have hnat : (261899203 : ℕ)^4381*50000000000000^3357 ≤ 21501543092687^3357*500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261899203 500000000 21501543092687 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068423021/10000000000 : ℝ)^4381 ≤ (3197613236523/25000000000000 : ℝ)^3357 := by
    have hnat : (2068423021 : ℕ)^4381*25000000000000^3357 ≤ 3197613236523^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068423021 10000000000 3197613236523 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349937389/10000000000 : ℝ), (261899203/500000000 : ℝ), (-2068423021/10000000000 : ℝ)] ![(22103230425513/50000000000000 : ℝ), (21501543092687/50000000000000 : ℝ), (3197613236523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349937389/10000000000 : ℝ)|^4381 ≤ (22103230425513/50000000000000 : ℝ)^3357
        have hw : |(5349937389/10000000000 : ℝ)|=(5349937389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261899203/500000000 : ℝ)|^4381 ≤ (21501543092687/50000000000000 : ℝ)^3357
        have hw : |(261899203/500000000 : ℝ)|=(261899203/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068423021/10000000000 : ℝ)|^4381 ≤ (3197613236523/25000000000000 : ℝ)^3357
        have hw : |(-2068423021/10000000000 : ℝ)|=(2068423021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s3_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152850567/5000000000 : ℝ)*x 0 + (4115397313/10000000000 : ℝ)*x 1 + (4503912579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152850567/5000000000 : ℝ)^4381 ≤ (33297737769569/100000000000000 : ℝ)^3357 := by
    have hnat : (2152850567 : ℕ)^4381*100000000000000^3357 ≤ 33297737769569^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152850567 5000000000 33297737769569 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4115397313/10000000000 : ℝ)^4381 ≤ (627804097793/2000000000000 : ℝ)^3357 := by
    have hnat : (4115397313 : ℕ)^4381*2000000000000^3357 ≤ 627804097793^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115397313 10000000000 627804097793 2000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503912579/10000000000 : ℝ)^4381 ≤ (35312057322393/100000000000000 : ℝ)^3357 := by
    have hnat : (4503912579 : ℕ)^4381*100000000000000^3357 ≤ 35312057322393^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503912579 10000000000 35312057322393 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152850567/5000000000 : ℝ), (4115397313/10000000000 : ℝ), (4503912579/10000000000 : ℝ)] ![(33297737769569/100000000000000 : ℝ), (627804097793/2000000000000 : ℝ), (35312057322393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152850567/5000000000 : ℝ)|^4381 ≤ (33297737769569/100000000000000 : ℝ)^3357
        have hw : |(2152850567/5000000000 : ℝ)|=(2152850567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4115397313/10000000000 : ℝ)|^4381 ≤ (627804097793/2000000000000 : ℝ)^3357
        have hw : |(4115397313/10000000000 : ℝ)|=(4115397313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503912579/10000000000 : ℝ)|^4381 ≤ (35312057322393/100000000000000 : ℝ)^3357
        have hw : |(4503912579/10000000000 : ℝ)|=(4503912579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s3_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-197654601/1000000000 : ℝ)*x 0 + (1309676457/2500000000 : ℝ)*x 1 + (5417377189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197654601/1000000000 : ℝ)^4381 ≤ (6027044885223/50000000000000 : ℝ)^3357 := by
    have hnat : (197654601 : ℕ)^4381*50000000000000^3357 ≤ 6027044885223^3357*1000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197654601 1000000000 6027044885223 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309676457/2500000000 : ℝ)^4381 ≤ (21505409736063/50000000000000 : ℝ)^3357 := by
    have hnat : (1309676457 : ℕ)^4381*50000000000000^3357 ≤ 21505409736063^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309676457 2500000000 21505409736063 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417377189/10000000000 : ℝ)^4381 ≤ (8987018147213/20000000000000 : ℝ)^3357 := by
    have hnat : (5417377189 : ℕ)^4381*20000000000000^3357 ≤ 8987018147213^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417377189 10000000000 8987018147213 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197654601/1000000000 : ℝ), (1309676457/2500000000 : ℝ), (5417377189/10000000000 : ℝ)] ![(6027044885223/50000000000000 : ℝ), (21505409736063/50000000000000 : ℝ), (8987018147213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197654601/1000000000 : ℝ)|^4381 ≤ (6027044885223/50000000000000 : ℝ)^3357
        have hw : |(-197654601/1000000000 : ℝ)|=(197654601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309676457/2500000000 : ℝ)|^4381 ≤ (21505409736063/50000000000000 : ℝ)^3357
        have hw : |(1309676457/2500000000 : ℝ)|=(1309676457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417377189/10000000000 : ℝ)|^4381 ≤ (8987018147213/20000000000000 : ℝ)^3357
        have hw : |(5417377189/10000000000 : ℝ)|=(5417377189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s3_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060629777/2000000000 : ℝ)*x 0 + (-944514983/5000000000 : ℝ)*x 1 + (1083475437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060629777/2000000000 : ℝ)^4381 ≤ (5462824035561/12500000000000 : ℝ)^3357 := by
    have hnat : (1060629777 : ℕ)^4381*12500000000000^3357 ≤ 5462824035561^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060629777 2000000000 5462824035561 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (944514983/5000000000 : ℝ)^4381 ≤ (5681158504681/50000000000000 : ℝ)^3357 := by
    have hnat : (944514983 : ℕ)^4381*50000000000000^3357 ≤ 5681158504681^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944514983 5000000000 5681158504681 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083475437/2000000000 : ℝ)^4381 ≤ (22467545346383/50000000000000 : ℝ)^3357 := by
    have hnat : (1083475437 : ℕ)^4381*50000000000000^3357 ≤ 22467545346383^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083475437 2000000000 22467545346383 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060629777/2000000000 : ℝ), (-944514983/5000000000 : ℝ), (1083475437/2000000000 : ℝ)] ![(5462824035561/12500000000000 : ℝ), (5681158504681/50000000000000 : ℝ), (22467545346383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060629777/2000000000 : ℝ)|^4381 ≤ (5462824035561/12500000000000 : ℝ)^3357
        have hw : |(1060629777/2000000000 : ℝ)|=(1060629777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-944514983/5000000000 : ℝ)|^4381 ≤ (5681158504681/50000000000000 : ℝ)^3357
        have hw : |(-944514983/5000000000 : ℝ)|=(944514983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083475437/2000000000 : ℝ)|^4381 ≤ (22467545346383/50000000000000 : ℝ)^3357
        have hw : |(1083475437/2000000000 : ℝ)|=(1083475437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s3_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060629741/2000000000 : ℝ)*x 0 + (5417377383/10000000000 : ℝ)*x 1 + (-94451497/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060629741/2000000000 : ℝ)^4381 ≤ (8740518069731/20000000000000 : ℝ)^3357 := by
    have hnat : (1060629741 : ℕ)^4381*20000000000000^3357 ≤ 8740518069731^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060629741 2000000000 8740518069731 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417377383/10000000000 : ℝ)^4381 ≤ (44935092836069/100000000000000 : ℝ)^3357 := by
    have hnat : (5417377383 : ℕ)^4381*100000000000000^3357 ≤ 44935092836069^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417377383 10000000000 44935092836069 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94451497/500000000 : ℝ)^4381 ≤ (11362316805271/100000000000000 : ℝ)^3357 := by
    have hnat : (94451497 : ℕ)^4381*100000000000000^3357 ≤ 11362316805271^3357*500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94451497 500000000 11362316805271 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060629741/2000000000 : ℝ), (5417377383/10000000000 : ℝ), (-94451497/500000000 : ℝ)] ![(8740518069731/20000000000000 : ℝ), (44935092836069/100000000000000 : ℝ), (11362316805271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060629741/2000000000 : ℝ)|^4381 ≤ (8740518069731/20000000000000 : ℝ)^3357
        have hw : |(1060629741/2000000000 : ℝ)|=(1060629741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417377383/10000000000 : ℝ)|^4381 ≤ (44935092836069/100000000000000 : ℝ)^3357
        have hw : |(5417377383/10000000000 : ℝ)|=(5417377383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94451497/500000000 : ℝ)|^4381 ≤ (11362316805271/100000000000000 : ℝ)^3357
        have hw : |(-94451497/500000000 : ℝ)|=(94451497/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s3_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305734703/10000000000 : ℝ)*x 0 + (4502356189/10000000000 : ℝ)*x 1 + (823392583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305734703/10000000000 : ℝ)^4381 ≤ (4162259570053/12500000000000 : ℝ)^3357 := by
    have hnat : (4305734703 : ℕ)^4381*12500000000000^3357 ≤ 4162259570053^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305734703 10000000000 4162259570053 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502356189/10000000000 : ℝ)^4381 ≤ (35296133382833/100000000000000 : ℝ)^3357 := by
    have hnat : (4502356189 : ℕ)^4381*100000000000000^3357 ≤ 35296133382833^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502356189 10000000000 35296133382833 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (823392583/2000000000 : ℝ)^4381 ≤ (628115800699/2000000000000 : ℝ)^3357 := by
    have hnat : (823392583 : ℕ)^4381*2000000000000^3357 ≤ 628115800699^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823392583 2000000000 628115800699 2000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305734703/10000000000 : ℝ), (4502356189/10000000000 : ℝ), (823392583/2000000000 : ℝ)] ![(4162259570053/12500000000000 : ℝ), (35296133382833/100000000000000 : ℝ), (628115800699/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305734703/10000000000 : ℝ)|^4381 ≤ (4162259570053/12500000000000 : ℝ)^3357
        have hw : |(4305734703/10000000000 : ℝ)|=(4305734703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502356189/10000000000 : ℝ)|^4381 ≤ (35296133382833/100000000000000 : ℝ)^3357
        have hw : |(4502356189/10000000000 : ℝ)|=(4502356189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(823392583/2000000000 : ℝ)|^4381 ≤ (628115800699/2000000000000 : ℝ)^3357
        have hw : |(823392583/2000000000 : ℝ)|=(823392583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (633/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11137/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14951/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (633/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2581/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (633/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2581/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (633/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2581/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (633/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2581/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (633/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2581/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (633/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2581/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2581/25000 : ℝ) ^ (1095/256 : ℝ) ≤ (302593011026687/5000000000000000000 : ℝ) := by
    have hpowers : (2581/25000 : ℝ)^1095 ≤ (302593011026687/5000000000000000000 : ℝ)^256 := by
      have hnat : (2581 : ℕ)^1095*5000000000000000000^256 ≤ 302593011026687^256*25000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2581 25000 302593011026687 5000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2581/25000 : ℝ)) (X := (302593011026687/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (633/4000 : ℝ) ^ (1095/256 : ℝ) ≤ (37611257959927183/100000000000000000000 : ℝ) := by
    have hpowers : (633/4000 : ℝ)^1095 ≤ (37611257959927183/100000000000000000000 : ℝ)^256 := by
      have hnat : (633 : ℕ)^1095*100000000000000000000^256 ≤ 37611257959927183^256*4000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        633 4000 37611257959927183 100000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (633/4000 : ℝ)) (X := (37611257959927183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500302593011026687/2500000000000000000 : ℝ) ≤ (500014147985221/500000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (2500302593011026687/2500000000000000000 : ℝ)^256 ≤ (500014147985221/500000000000000 : ℝ)^1095 := by
      have hnat : (2500302593011026687 : ℕ)^256*500000000000000^1095 ≤ 500014147985221^1095*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500302593011026687 2500000000000000000 500014147985221 500000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014147985221/500000000000000 : ℝ)) (X := (2500302593011026687/2500000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043663118180460923/100000000000000000000 : ℝ) ≤ (10001020629129543/10000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (100043663118180460923/100000000000000000000 : ℝ)^256 ≤ (10001020629129543/10000000000000000 : ℝ)^1095 := by
      have hnat : (100043663118180460923 : ℕ)^256*10000000000000000^1095 ≤ 10001020629129543^1095*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043663118180460923 100000000000000000000 10001020629129543 10000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001020629129543/10000000000000000 : ℝ)) (X := (100043663118180460923/100000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037611257959927183/50000000000000000000 : ℝ) ≤ (5000879149277333/5000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50037611257959927183/50000000000000000000 : ℝ)^256 ≤ (5000879149277333/5000000000000000 : ℝ)^1095 := by
      have hnat : (50037611257959927183 : ℕ)^256*5000000000000000^1095 ≤ 5000879149277333^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037611257959927183 50000000000000000000 5000879149277333 5000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000879149277333/5000000000000000 : ℝ)) (X := (50037611257959927183/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(302593011026687/5000000000000000000 : ℝ) ≤ ((13749081290761018679/13752500000000000000 : ℝ)+2*(737669425123/550100000000000 : ℝ)*(2581/25000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (13749081290761018679/13752500000000000000 : ℝ)+2*(737669425123/550100000000000 : ℝ)*(2581/25000 : ℝ)=(500014147985221/500000000000000 : ℝ) by norm_num, show 1+2*(302593011026687/5000000000000000000 : ℝ)=(2500302593011026687/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37611257959927183/100000000000000000000 : ℝ)+(302593011026687/5000000000000000000 : ℝ) ≤ ((13749081290761018679/13752500000000000000 : ℝ)+(737669425123/550100000000000 : ℝ)*((633/4000 : ℝ)+(2581/25000 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (13749081290761018679/13752500000000000000 : ℝ)+(737669425123/550100000000000 : ℝ)*((633/4000 : ℝ)+(2581/25000 : ℝ))=(10001020629129543/10000000000000000 : ℝ) by norm_num, show 1+(37611257959927183/100000000000000000000 : ℝ)+(302593011026687/5000000000000000000 : ℝ)=(100043663118180460923/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37611257959927183/100000000000000000000 : ℝ) ≤ ((13749081290761018679/13752500000000000000 : ℝ)+2*(737669425123/550100000000000 : ℝ)*(633/4000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (13749081290761018679/13752500000000000000 : ℝ)+2*(737669425123/550100000000000 : ℝ)*(633/4000 : ℝ)=(5000879149277333/5000000000000000 : ℝ) by norm_num, show 1+2*(37611257959927183/100000000000000000000 : ℝ)=(50037611257959927183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13749081290761018679/13752500000000000000 : ℝ)*(X 1 0+X 2 0)+(737669425123/550100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2581/25000 : ℝ)) (hi := (633/4000 : ℝ)) (c := (13749081290761018679/13752500000000000000 : ℝ)) (alpha := (737669425123/550100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13749081290761018679/13752500000000000000 : ℝ)*(X 0 1+X 2 1)+(737669425123/550100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2581/25000 : ℝ)) (hi := (633/4000 : ℝ)) (c := (13749081290761018679/13752500000000000000 : ℝ)) (alpha := (737669425123/550100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13749081290761018679/13752500000000000000 : ℝ)*(X 0 2+X 1 2)+(737669425123/550100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2581/25000 : ℝ)) (hi := (633/4000 : ℝ)) (c := (13749081290761018679/13752500000000000000 : ℝ)) (alpha := (737669425123/550100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-395306119/2000000000 : ℝ)*X 0 0+(2709051443/5000000000 : ℝ)*X 0 1+(5237984089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674968693/5000000000 : ℝ)*X 1 0+(-2068423039/10000000000 : ℝ)*X 1 1+(104759681/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349937389/10000000000 : ℝ)*X 2 0+(261899203/500000000 : ℝ)*X 2 1+(-2068423021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152850567/5000000000 : ℝ)*X 0 0+(4115397313/10000000000 : ℝ)*X 0 1+(4503912579/10000000000 : ℝ)*X 0 2+(2152850567/5000000000 : ℝ)*X 1 0+(4115397313/10000000000 : ℝ)*X 1 1+(4503912579/10000000000 : ℝ)*X 1 2+(2152850567/5000000000 : ℝ)*X 2 0+(4115397313/10000000000 : ℝ)*X 2 1+(4503912579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-197654601/1000000000 : ℝ)*X 0 0+(1309676457/2500000000 : ℝ)*X 0 1+(5417377189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060629777/2000000000 : ℝ)*X 1 0+(-944514983/5000000000 : ℝ)*X 1 1+(1083475437/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060629741/2000000000 : ℝ)*X 2 0+(5417377383/10000000000 : ℝ)*X 2 1+(-94451497/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305734703/10000000000 : ℝ)*X 0 0+(4502356189/10000000000 : ℝ)*X 0 1+(823392583/2000000000 : ℝ)*X 0 2+(4305734703/10000000000 : ℝ)*X 1 0+(4502356189/10000000000 : ℝ)*X 1 1+(823392583/2000000000 : ℝ)*X 1 2+(4305734703/10000000000 : ℝ)*X 2 0+(4502356189/10000000000 : ℝ)*X 2 1+(823392583/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1820300116894264906880992419/343812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1050565719/100000000000000 : ℝ)*(base19) + (995754483/100000000000000 : ℝ)*(base23) + (79465667/50000000000000 : ℝ)*(upper3) + (15494623/50000000000000 : ℝ)*(upper4) + (8671771/6250000000000 : ℝ)*(upper5) + (4062922153389313/100000000000000 : ℝ)*(major0) + (4062922153389313/100000000000000 : ℝ)*(major1) + (4062922153389313/100000000000000 : ℝ)*(major2) + (555190905726153/10000000000000 : ℝ)*(sp0) + (2775962913869617/50000000000000 : ℝ)*(sp1) + (555192588255047/10000000000000 : ℝ)*(sp2) + (128695453364449/5000000000000 : ℝ)*(sp3) + (17821043423/100000000000000 : ℝ)*(sp4) + (1023087853/12500000000000 : ℝ)*(sp7) + (643479312997951/25000000000000 : ℝ)*(f.failure) + (5551926878304953/100000000000000 : ℝ)*(f.sum) + (150230908070439/27505000000000000000000000000 : ℝ)*base65 + (1381960457710547473/1375250000000000000000000000000000 : ℝ)*base68 + (3603744098365202527/1375250000000000000000000000000000 : ℝ)*base69 + (10841847926885452527/1375250000000000000000000000000000 : ℝ)*base71 + (85134172096251/27505000000000000000000000000 : ℝ)*base74 + (7370906485844452527/1375250000000000000000000000000000 : ℝ)*base75 + (13184008001008952527/1375250000000000000000000000000000 : ℝ)*base77 + (15197278759445452527/1375250000000000000000000000000000 : ℝ)*base79 + (67446922977949/27505000000000000000000000000 : ℝ)*base81 + (2577071/1250000000000000000000 : ℝ)*base90 + (2577071/1250000000000000000000 : ℝ)*base92 + (2577071/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236982550780115682620889/27505000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51310701/6250000000000 : ℝ)*(base19) + (793674447/100000000000000 : ℝ)*(base23) + (108247653/100000000000000 : ℝ)*(upper3) + (36556683/50000000000000 : ℝ)*(lower4) + (26850311/25000000000000 : ℝ)*(upper5) + (511976029440957/12500000000000 : ℝ)*(major0) + (511976029440957/12500000000000 : ℝ)*(major1) + (511976029440957/12500000000000 : ℝ)*(major2) + (14812927007/100000000000000 : ℝ)*(sp1) + (176242987/1000000000000 : ℝ)*(sp2) + (174902035781427/3125000000000 : ℝ)*(sp4) + (5596849511107441/100000000000000 : ℝ)*(sp5) + (1399211681758129/25000000000000 : ℝ)*(sp6) + (1297375519425141/50000000000000 : ℝ)*(sp7) + (1297375519425141/50000000000000 : ℝ)*(f.failure) + (174902035781427/3125000000000 : ℝ)*(f.sum) + (85770876070671/13752500000000000000000000000 : ℝ)*base66 + (959639511230401697/171906250000000000000000000000000 : ℝ)*base68 + (1745359408037223303/171906250000000000000000000000000 : ℝ)*base69 + (838801131687995447/171906250000000000000000000000000 : ℝ)*base72 + (187667064840907/27505000000000000000000000000 : ℝ)*base74 + (1694136275960870447/171906250000000000000000000000000 : ℝ)*base76 + (182382316418473303/171906250000000000000000000000000 : ℝ)*base77 + (2637860145149723303/171906250000000000000000000000000 : ℝ)*base79 + (34271193887619/13752500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2982939/2500000000000000000000 : ℝ)*base89 + (2982939/2500000000000000000000 : ℝ)*base91 + (2982939/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1421_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (633/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1421_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1421_s4_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-988736823/5000000000 : ℝ)*x 0 + (5410088749/10000000000 : ℝ)*x 1 + (2622688653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988736823/5000000000 : ℝ)^4381 ≤ (2412294639817/20000000000000 : ℝ)^3357 := by
    have hnat : (988736823 : ℕ)^4381*20000000000000^3357 ≤ 2412294639817^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988736823 5000000000 2412294639817 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410088749/10000000000 : ℝ)^4381 ≤ (44856211282811/100000000000000 : ℝ)^3357 := by
    have hnat : (5410088749 : ℕ)^4381*100000000000000^3357 ≤ 44856211282811^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410088749 10000000000 44856211282811 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622688653/5000000000 : ℝ)^4381 ≤ (5385289439169/12500000000000 : ℝ)^3357 := by
    have hnat : (2622688653 : ℕ)^4381*12500000000000^3357 ≤ 5385289439169^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622688653 5000000000 5385289439169 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-988736823/5000000000 : ℝ), (5410088749/10000000000 : ℝ), (2622688653/5000000000 : ℝ)] ![(2412294639817/20000000000000 : ℝ), (44856211282811/100000000000000 : ℝ), (5385289439169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-988736823/5000000000 : ℝ)|^4381 ≤ (2412294639817/20000000000000 : ℝ)^3357
        have hw : |(-988736823/5000000000 : ℝ)|=(988736823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410088749/10000000000 : ℝ)|^4381 ≤ (44856211282811/100000000000000 : ℝ)^3357
        have hw : |(5410088749/10000000000 : ℝ)|=(5410088749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622688653/5000000000 : ℝ)|^4381 ≤ (5385289439169/12500000000000 : ℝ)^3357
        have hw : |(2622688653/5000000000 : ℝ)|=(2622688653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s4_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267393547/500000000 : ℝ)*x 0 + (-2061362497/10000000000 : ℝ)*x 1 + (1049075479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267393547/500000000 : ℝ)^4381 ≤ (44184178651281/100000000000000 : ℝ)^3357 := by
    have hnat : (267393547 : ℕ)^4381*100000000000000^3357 ≤ 44184178651281^3357*500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267393547 500000000 44184178651281 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061362497/10000000000 : ℝ)^4381 ≤ (3183376217089/25000000000000 : ℝ)^3357 := by
    have hnat : (2061362497 : ℕ)^4381*25000000000000^3357 ≤ 3183376217089^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061362497 10000000000 3183376217089 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049075479/2000000000 : ℝ)^4381 ≤ (43082316467321/100000000000000 : ℝ)^3357 := by
    have hnat : (1049075479 : ℕ)^4381*100000000000000^3357 ≤ 43082316467321^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049075479 2000000000 43082316467321 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267393547/500000000 : ℝ), (-2061362497/10000000000 : ℝ), (1049075479/2000000000 : ℝ)] ![(44184178651281/100000000000000 : ℝ), (3183376217089/25000000000000 : ℝ), (43082316467321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267393547/500000000 : ℝ)|^4381 ≤ (44184178651281/100000000000000 : ℝ)^3357
        have hw : |(267393547/500000000 : ℝ)|=(267393547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061362497/10000000000 : ℝ)|^4381 ≤ (3183376217089/25000000000000 : ℝ)^3357
        have hw : |(-2061362497/10000000000 : ℝ)|=(2061362497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049075479/2000000000 : ℝ)|^4381 ≤ (43082316467321/100000000000000 : ℝ)^3357
        have hw : |(1049075479/2000000000 : ℝ)|=(1049075479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s4_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347870943/10000000000 : ℝ)*x 0 + (5245377417/10000000000 : ℝ)*x 1 + (-64417577/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347870943/10000000000 : ℝ)^4381 ≤ (11046044670907/25000000000000 : ℝ)^3357 := by
    have hnat : (5347870943 : ℕ)^4381*25000000000000^3357 ≤ 11046044670907^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347870943 10000000000 11046044670907 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245377417/10000000000 : ℝ)^4381 ≤ (21541158351567/50000000000000 : ℝ)^3357 := by
    have hnat : (5245377417 : ℕ)^4381*50000000000000^3357 ≤ 21541158351567^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245377417 10000000000 21541158351567 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64417577/312500000 : ℝ)^4381 ≤ (6366752301163/50000000000000 : ℝ)^3357 := by
    have hnat : (64417577 : ℕ)^4381*50000000000000^3357 ≤ 6366752301163^3357*312500000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64417577 312500000 6366752301163 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347870943/10000000000 : ℝ), (5245377417/10000000000 : ℝ), (-64417577/312500000 : ℝ)] ![(11046044670907/25000000000000 : ℝ), (21541158351567/50000000000000 : ℝ), (6366752301163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347870943/10000000000 : ℝ)|^4381 ≤ (11046044670907/25000000000000 : ℝ)^3357
        have hw : |(5347870943/10000000000 : ℝ)|=(5347870943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245377417/10000000000 : ℝ)|^4381 ≤ (21541158351567/50000000000000 : ℝ)^3357
        have hw : |(5245377417/10000000000 : ℝ)|=(5245377417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64417577/312500000 : ℝ)|^4381 ≤ (6366752301163/50000000000000 : ℝ)^3357
        have hw : |(-64417577/312500000 : ℝ)|=(64417577/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s4_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538284777/1250000000 : ℝ)*x 0 + (2065972197/5000000000 : ℝ)*x 1 + (4487226099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538284777/1250000000 : ℝ)^4381 ≤ (520368156379/1562500000000 : ℝ)^3357 := by
    have hnat : (538284777 : ℕ)^4381*1562500000000^3357 ≤ 520368156379^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538284777 1250000000 520368156379 1562500000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065972197/5000000000 : ℝ)^4381 ≤ (6311003594407/20000000000000 : ℝ)^3357 := by
    have hnat : (2065972197 : ℕ)^4381*20000000000000^3357 ≤ 6311003594407^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065972197 5000000000 6311003594407 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487226099/10000000000 : ℝ)^4381 ≤ (35141419998863/100000000000000 : ℝ)^3357 := by
    have hnat : (4487226099 : ℕ)^4381*100000000000000^3357 ≤ 35141419998863^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487226099 10000000000 35141419998863 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538284777/1250000000 : ℝ), (2065972197/5000000000 : ℝ), (4487226099/10000000000 : ℝ)] ![(520368156379/1562500000000 : ℝ), (6311003594407/20000000000000 : ℝ), (35141419998863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538284777/1250000000 : ℝ)|^4381 ≤ (520368156379/1562500000000 : ℝ)^3357
        have hw : |(538284777/1250000000 : ℝ)|=(538284777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065972197/5000000000 : ℝ)|^4381 ≤ (6311003594407/20000000000000 : ℝ)^3357
        have hw : |(2065972197/5000000000 : ℝ)|=(2065972197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487226099/10000000000 : ℝ)|^4381 ≤ (35141419998863/100000000000000 : ℝ)^3357
        have hw : |(4487226099/10000000000 : ℝ)|=(4487226099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s4_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1977485653/10000000000 : ℝ)*x 0 + (5245981199/10000000000 : ℝ)*x 1 + (540948167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977485653/10000000000 : ℝ)^4381 ≤ (6030784387281/50000000000000 : ℝ)^3357 := by
    have hnat : (1977485653 : ℕ)^4381*50000000000000^3357 ≤ 6030784387281^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977485653 10000000000 6030784387281 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245981199/10000000000 : ℝ)^4381 ≤ (43088788606209/100000000000000 : ℝ)^3357 := by
    have hnat : (5245981199 : ℕ)^4381*100000000000000^3357 ≤ 43088788606209^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245981199 10000000000 43088788606209 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540948167/1000000000 : ℝ)^4381 ≤ (44849642606093/100000000000000 : ℝ)^3357 := by
    have hnat : (540948167 : ℕ)^4381*100000000000000^3357 ≤ 44849642606093^3357*1000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540948167 1000000000 44849642606093 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1977485653/10000000000 : ℝ), (5245981199/10000000000 : ℝ), (540948167/1000000000 : ℝ)] ![(6030784387281/50000000000000 : ℝ), (43088788606209/100000000000000 : ℝ), (44849642606093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1977485653/10000000000 : ℝ)|^4381 ≤ (6030784387281/50000000000000 : ℝ)^3357
        have hw : |(-1977485653/10000000000 : ℝ)|=(1977485653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245981199/10000000000 : ℝ)|^4381 ≤ (43088788606209/100000000000000 : ℝ)^3357
        have hw : |(5245981199/10000000000 : ℝ)|=(5245981199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540948167/1000000000 : ℝ)|^4381 ≤ (44849642606093/100000000000000 : ℝ)^3357
        have hw : |(540948167/1000000000 : ℝ)|=(540948167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s4_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663135543/1250000000 : ℝ)*x 0 + (-237157271/1250000000 : ℝ)*x 1 + (2704740857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663135543/1250000000 : ℝ)^4381 ≤ (1748936343187/4000000000000 : ℝ)^3357 := by
    have hnat : (663135543 : ℕ)^4381*4000000000000^3357 ≤ 1748936343187^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663135543 1250000000 1748936343187 4000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237157271/1250000000 : ℝ)^4381 ≤ (1142694833159/10000000000000 : ℝ)^3357 := by
    have hnat : (237157271 : ℕ)^4381*10000000000000^3357 ≤ 1142694833159^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237157271 1250000000 1142694833159 10000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704740857/5000000000 : ℝ)^4381 ≤ (44849643082171/100000000000000 : ℝ)^3357 := by
    have hnat : (2704740857 : ℕ)^4381*100000000000000^3357 ≤ 44849643082171^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704740857 5000000000 44849643082171 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663135543/1250000000 : ℝ), (-237157271/1250000000 : ℝ), (2704740857/5000000000 : ℝ)] ![(1748936343187/4000000000000 : ℝ), (1142694833159/10000000000000 : ℝ), (44849643082171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663135543/1250000000 : ℝ)|^4381 ≤ (1748936343187/4000000000000 : ℝ)^3357
        have hw : |(663135543/1250000000 : ℝ)|=(663135543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237157271/1250000000 : ℝ)|^4381 ≤ (1142694833159/10000000000000 : ℝ)^3357
        have hw : |(-237157271/1250000000 : ℝ)|=(237157271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704740857/5000000000 : ℝ)|^4381 ≤ (44849643082171/100000000000000 : ℝ)^3357
        have hw : |(2704740857/5000000000 : ℝ)|=(2704740857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s4_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1697627/3200000 : ℝ)*x 0 + (5409481707/10000000000 : ℝ)*x 1 + (-948629067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1697627/3200000 : ℝ)^4381 ≤ (21861704456553/50000000000000 : ℝ)^3357 := by
    have hnat : (1697627 : ℕ)^4381*50000000000000^3357 ≤ 21861704456553^3357*3200000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697627 3200000 21861704456553 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409481707/10000000000 : ℝ)^4381 ≤ (44849643006431/100000000000000 : ℝ)^3357 := by
    have hnat : (5409481707 : ℕ)^4381*100000000000000^3357 ≤ 44849643006431^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409481707 10000000000 44849643006431 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948629067/5000000000 : ℝ)^4381 ≤ (2856737016087/25000000000000 : ℝ)^3357 := by
    have hnat : (948629067 : ℕ)^4381*25000000000000^3357 ≤ 2856737016087^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948629067 5000000000 2856737016087 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1697627/3200000 : ℝ), (5409481707/10000000000 : ℝ), (-948629067/5000000000 : ℝ)] ![(21861704456553/50000000000000 : ℝ), (44849643006431/100000000000000 : ℝ), (2856737016087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1697627/3200000 : ℝ)|^4381 ≤ (21861704456553/50000000000000 : ℝ)^3357
        have hw : |(1697627/3200000 : ℝ)|=(1697627/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409481707/10000000000 : ℝ)|^4381 ≤ (44849643006431/100000000000000 : ℝ)^3357
        have hw : |(5409481707/10000000000 : ℝ)|=(5409481707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948629067/5000000000 : ℝ)|^4381 ≤ (2856737016087/25000000000000 : ℝ)^3357
        have hw : |(-948629067/5000000000 : ℝ)|=(948629067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s4_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4306304133/10000000000 : ℝ)*x 0 + (2242961767/5000000000 : ℝ)*x 1 + (2066626891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306304133/10000000000 : ℝ)^4381 ≤ (33303823582899/100000000000000 : ℝ)^3357 := by
    have hnat : (4306304133 : ℕ)^4381*100000000000000^3357 ≤ 33303823582899^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306304133 10000000000 33303823582899 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242961767/5000000000 : ℝ)^4381 ≤ (1405124319793/4000000000000 : ℝ)^3357 := by
    have hnat : (2242961767 : ℕ)^4381*4000000000000^3357 ≤ 1405124319793^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242961767 5000000000 1405124319793 4000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066626891/5000000000 : ℝ)^4381 ≤ (7892017103503/25000000000000 : ℝ)^3357 := by
    have hnat : (2066626891 : ℕ)^4381*25000000000000^3357 ≤ 7892017103503^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066626891 5000000000 7892017103503 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306304133/10000000000 : ℝ), (2242961767/5000000000 : ℝ), (2066626891/5000000000 : ℝ)] ![(33303823582899/100000000000000 : ℝ), (1405124319793/4000000000000 : ℝ), (7892017103503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306304133/10000000000 : ℝ)|^4381 ≤ (33303823582899/100000000000000 : ℝ)^3357
        have hw : |(4306304133/10000000000 : ℝ)|=(4306304133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242961767/5000000000 : ℝ)|^4381 ≤ (1405124319793/4000000000000 : ℝ)^3357
        have hw : |(2242961767/5000000000 : ℝ)|=(2242961767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066626891/5000000000 : ℝ)|^4381 ≤ (7892017103503/25000000000000 : ℝ)^3357
        have hw : |(2066626891/5000000000 : ℝ)|=(2066626891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2259/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14783/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14951/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14951/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14951/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14951/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14951/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14951/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11137/100000 : ℝ) ^ (1095/256 : ℝ) ≤ (2092377352876401/25000000000000000000 : ℝ) := by
    have hpowers : (11137/100000 : ℝ)^1095 ≤ (2092377352876401/25000000000000000000 : ℝ)^256 := by
      have hnat : (11137 : ℕ)^1095*25000000000000000000^256 ≤ 2092377352876401^256*100000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11137 100000 2092377352876401 25000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11137/100000 : ℝ)) (X := (2092377352876401/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14951/100000 : ℝ) ^ (1095/256 : ℝ) ≤ (29497208346327109/100000000000000000000 : ℝ) := by
    have hpowers : (14951/100000 : ℝ)^1095 ≤ (29497208346327109/100000000000000000000 : ℝ)^256 := by
      have hnat : (14951 : ℕ)^1095*100000000000000000000^256 ≤ 29497208346327109^256*100000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14951 100000 29497208346327109 100000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14951/100000 : ℝ)) (X := (29497208346327109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502092377352876401/12500000000000000000 : ℝ) ≤ (200007826327023/200000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (12502092377352876401/12500000000000000000 : ℝ)^256 ≤ (200007826327023/200000000000000 : ℝ)^1095 := by
      have hnat : (12502092377352876401 : ℕ)^256*200000000000000^1095 ≤ 200007826327023^1095*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502092377352876401 12500000000000000000 200007826327023 200000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200007826327023/200000000000000 : ℝ)) (X := (12502092377352876401/12500000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037866717757832713/100000000000000000000 : ℝ) ≤ (2000177031484477/2000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (100037866717757832713/100000000000000000000 : ℝ)^256 ≤ (2000177031484477/2000000000000000 : ℝ)^1095 := by
      have hnat : (100037866717757832713 : ℕ)^256*2000000000000000^1095 ≤ 2000177031484477^1095*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037866717757832713 100000000000000000000 2000177031484477 2000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000177031484477/2000000000000000 : ℝ)) (X := (100037866717757832713/100000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029497208346327109/50000000000000000000 : ℝ) ≤ (500068949924681/500000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50029497208346327109/50000000000000000000 : ℝ)^256 ≤ (500068949924681/500000000000000 : ℝ)^1095 := by
      have hnat : (50029497208346327109 : ℕ)^256*500000000000000^1095 ≤ 500068949924681^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029497208346327109 50000000000000000000 500068949924681 500000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500068949924681/500000000000000 : ℝ)) (X := (50029497208346327109/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2092377352876401/25000000000000000000 : ℝ) ≤ ((3813049266454259771/3814000000000000000 : ℝ)+2*(98768214247/76280000000000 : ℝ)*(11137/100000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (3813049266454259771/3814000000000000000 : ℝ)+2*(98768214247/76280000000000 : ℝ)*(11137/100000 : ℝ)=(200007826327023/200000000000000 : ℝ) by norm_num, show 1+2*(2092377352876401/25000000000000000000 : ℝ)=(12502092377352876401/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29497208346327109/100000000000000000000 : ℝ)+(2092377352876401/25000000000000000000 : ℝ) ≤ ((3813049266454259771/3814000000000000000 : ℝ)+(98768214247/76280000000000 : ℝ)*((14951/100000 : ℝ)+(11137/100000 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (3813049266454259771/3814000000000000000 : ℝ)+(98768214247/76280000000000 : ℝ)*((14951/100000 : ℝ)+(11137/100000 : ℝ))=(2000177031484477/2000000000000000 : ℝ) by norm_num, show 1+(29497208346327109/100000000000000000000 : ℝ)+(2092377352876401/25000000000000000000 : ℝ)=(100037866717757832713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29497208346327109/100000000000000000000 : ℝ) ≤ ((3813049266454259771/3814000000000000000 : ℝ)+2*(98768214247/76280000000000 : ℝ)*(14951/100000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (3813049266454259771/3814000000000000000 : ℝ)+2*(98768214247/76280000000000 : ℝ)*(14951/100000 : ℝ)=(500068949924681/500000000000000 : ℝ) by norm_num, show 1+2*(29497208346327109/100000000000000000000 : ℝ)=(50029497208346327109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3813049266454259771/3814000000000000000 : ℝ)*(X 1 0+X 2 0)+(98768214247/76280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (3813049266454259771/3814000000000000000 : ℝ)) (alpha := (98768214247/76280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3813049266454259771/3814000000000000000 : ℝ)*(X 0 1+X 2 1)+(98768214247/76280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (3813049266454259771/3814000000000000000 : ℝ)) (alpha := (98768214247/76280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3813049266454259771/3814000000000000000 : ℝ)*(X 0 2+X 1 2)+(98768214247/76280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (3813049266454259771/3814000000000000000 : ℝ)) (alpha := (98768214247/76280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-988736823/5000000000 : ℝ)*X 0 0+(5410088749/10000000000 : ℝ)*X 0 1+(2622688653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267393547/500000000 : ℝ)*X 1 0+(-2061362497/10000000000 : ℝ)*X 1 1+(1049075479/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347870943/10000000000 : ℝ)*X 2 0+(5245377417/10000000000 : ℝ)*X 2 1+(-64417577/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((538284777/1250000000 : ℝ)*X 0 0+(2065972197/5000000000 : ℝ)*X 0 1+(4487226099/10000000000 : ℝ)*X 0 2+(538284777/1250000000 : ℝ)*X 1 0+(2065972197/5000000000 : ℝ)*X 1 1+(4487226099/10000000000 : ℝ)*X 1 2+(538284777/1250000000 : ℝ)*X 2 0+(2065972197/5000000000 : ℝ)*X 2 1+(4487226099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1977485653/10000000000 : ℝ)*X 0 0+(5245981199/10000000000 : ℝ)*X 0 1+(540948167/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663135543/1250000000 : ℝ)*X 1 0+(-237157271/1250000000 : ℝ)*X 1 1+(2704740857/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1697627/3200000 : ℝ)*X 2 0+(5409481707/10000000000 : ℝ)*X 2 1+(-948629067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4306304133/10000000000 : ℝ)*X 0 0+(2242961767/5000000000 : ℝ)*X 0 1+(2066626891/5000000000 : ℝ)*X 0 2+(4306304133/10000000000 : ℝ)*X 1 0+(2242961767/5000000000 : ℝ)*X 1 1+(2066626891/5000000000 : ℝ)*X 1 2+(4306304133/10000000000 : ℝ)*X 2 0+(2242961767/5000000000 : ℝ)*X 2 1+(2066626891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (216390929374628696983526823/47675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162233447/25000000000000 : ℝ)*(base19) + (596896719/100000000000000 : ℝ)*(base23) + (2965013/10000000000000 : ℝ)*(lower2) + (16550827/20000000000000 : ℝ)*(upper3) + (84195251/100000000000000 : ℝ)*(upper5) + (1110742455763757/25000000000000 : ℝ)*(major0) + (1110742455763757/25000000000000 : ℝ)*(major1) + (1110742455763757/25000000000000 : ℝ)*(major2) + (1517809936979127/25000000000000 : ℝ)*(sp0) + (6071256150544839/100000000000000 : ℝ)*(sp1) + (6071256202581909/100000000000000 : ℝ)*(sp2) + (1407337572192929/50000000000000 : ℝ)*(sp3) + (17051562119/100000000000000 : ℝ)*(sp4) + (3775474841/50000000000000 : ℝ)*(sp7) + (2814682695335541/100000000000000 : ℝ)*(f.failure) + (1517814199869657/25000000000000 : ℝ)*(f.sum) + (39942828549/381400000000000000000000000 : ℝ)*base65 + (33181050945680353/95350000000000000000000000000000 : ℝ)*base68 + (819452982001530353/95350000000000000000000000000000 : ℝ)*base70 + (103903889039030353/95350000000000000000000000000000 : ℝ)*base72 + (14117543450859/1907000000000000000000000000 : ℝ)*base73 + (1389806954445980353/95350000000000000000000000000000 : ℝ)*base76 + (396007806138480353/95350000000000000000000000000000 : ℝ)*base78 + (1614520742503680353/95350000000000000000000000000000 : ℝ)*base80 + (10539961579/59593750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (37824539/5000000000000000000000 : ℝ)*base89 + (37824539/5000000000000000000000 : ℝ)*base91 + (37824539/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (158482333570407070207193859/47675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (442760587/100000000000000 : ℝ)*(base19) + (55061721/10000000000000 : ℝ)*(base23) + (17325991/25000000000000 : ℝ)*(upper3) + (26735037/100000000000000 : ℝ)*(lower4) + (15890119/25000000000000 : ℝ)*(upper5) + (1118963006683157/25000000000000 : ℝ)*(major0) + (1118963006683157/25000000000000 : ℝ)*(major1) + (1118963006683157/25000000000000 : ℝ)*(major2) + (1960427743/20000000000000 : ℝ)*(sp1) + (1561928219/12500000000000 : ℝ)*(sp2) + (6116189917522199/100000000000000 : ℝ)*(sp4) + (382261229538931/6250000000000 : ℝ)*(sp5) + (6116176871479237/100000000000000 : ℝ)*(sp6) + (567102805027123/20000000000000 : ℝ)*(sp7) + (567102805027123/20000000000000 : ℝ)*(f.failure) + (6116189917522199/100000000000000 : ℝ)*(f.sum) + (886111081711/953500000000000000000000000 : ℝ)*base65 + (513021760208477047/95350000000000000000000000000000 : ℝ)*base67 + (554587231833672953/95350000000000000000000000000000 : ℝ)*base70 + (119165817739322953/95350000000000000000000000000000 : ℝ)*base72 + (7437935031569/1907000000000000000000000000 : ℝ)*base73 + (1034279510867677047/95350000000000000000000000000000 : ℝ)*base75 + (62250554705227047/95350000000000000000000000000000 : ℝ)*base77 + (388711720478777047/95350000000000000000000000000000 : ℝ)*base79 + (15090482189/7628000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5506883/1000000000000000000000 : ℝ)*base90 + (5506883/1000000000000000000000 : ℝ)*base92 + (5506883/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1421_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1421_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1421_s5_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1977617747/10000000000 : ℝ)*x 0 + (5408824567/10000000000 : ℝ)*x 1 + (81977287/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977617747/10000000000 : ℝ)^4381 ≤ (12062620251821/100000000000000 : ℝ)^3357 := by
    have hnat : (1977617747 : ℕ)^4381*100000000000000^3357 ≤ 12062620251821^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977617747 10000000000 12062620251821 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408824567/10000000000 : ℝ)^4381 ≤ (44842532916357/100000000000000 : ℝ)^3357 := by
    have hnat : (5408824567 : ℕ)^4381*100000000000000^3357 ≤ 44842532916357^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408824567 10000000000 44842532916357 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81977287/156250000 : ℝ)^4381 ≤ (1346713963273/3125000000000 : ℝ)^3357 := by
    have hnat : (81977287 : ℕ)^4381*3125000000000^3357 ≤ 1346713963273^3357*156250000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81977287 156250000 1346713963273 3125000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1977617747/10000000000 : ℝ), (5408824567/10000000000 : ℝ), (81977287/156250000 : ℝ)] ![(12062620251821/100000000000000 : ℝ), (44842532916357/100000000000000 : ℝ), (1346713963273/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1977617747/10000000000 : ℝ)|^4381 ≤ (12062620251821/100000000000000 : ℝ)^3357
        have hw : |(-1977617747/10000000000 : ℝ)|=(1977617747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408824567/10000000000 : ℝ)|^4381 ≤ (44842532916357/100000000000000 : ℝ)^3357
        have hw : |(5408824567/10000000000 : ℝ)|=(5408824567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81977287/156250000 : ℝ)|^4381 ≤ (1346713963273/3125000000000 : ℝ)^3357
        have hw : |(81977287/156250000 : ℝ)|=(81977287/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s5_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347543293/10000000000 : ℝ)*x 0 + (-2060242831/10000000000 : ℝ)*x 1 + (5246548961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347543293/10000000000 : ℝ)^4381 ≤ (44180645925581/100000000000000 : ℝ)^3357 := by
    have hnat : (5347543293 : ℕ)^4381*100000000000000^3357 ≤ 44180645925581^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347543293 10000000000 44180645925581 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060242831/10000000000 : ℝ)^4381 ≤ (12724479436187/100000000000000 : ℝ)^3357 := by
    have hnat : (2060242831 : ℕ)^4381*100000000000000^3357 ≤ 12724479436187^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060242831 10000000000 12724479436187 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246548961/10000000000 : ℝ)^4381 ≤ (43094874620351/100000000000000 : ℝ)^3357 := by
    have hnat : (5246548961 : ℕ)^4381*100000000000000^3357 ≤ 43094874620351^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246548961 10000000000 43094874620351 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347543293/10000000000 : ℝ), (-2060242831/10000000000 : ℝ), (5246548961/10000000000 : ℝ)] ![(44180645925581/100000000000000 : ℝ), (12724479436187/100000000000000 : ℝ), (43094874620351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347543293/10000000000 : ℝ)|^4381 ≤ (44180645925581/100000000000000 : ℝ)^3357
        have hw : |(5347543293/10000000000 : ℝ)|=(5347543293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060242831/10000000000 : ℝ)|^4381 ≤ (12724479436187/100000000000000 : ℝ)^3357
        have hw : |(-2060242831/10000000000 : ℝ)|=(2060242831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246548961/10000000000 : ℝ)|^4381 ≤ (43094874620351/100000000000000 : ℝ)^3357
        have hw : |(5246548961/10000000000 : ℝ)|=(5246548961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s5_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336885911/2500000000 : ℝ)*x 0 + (2623273679/5000000000 : ℝ)*x 1 + (-1030122247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336885911/2500000000 : ℝ)^4381 ≤ (22090324855033/50000000000000 : ℝ)^3357 := by
    have hnat : (1336885911 : ℕ)^4381*50000000000000^3357 ≤ 22090324855033^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336885911 2500000000 22090324855033 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623273679/5000000000 : ℝ)^4381 ≤ (21547428718511/50000000000000 : ℝ)^3357 := by
    have hnat : (2623273679 : ℕ)^4381*50000000000000^3357 ≤ 21547428718511^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623273679 5000000000 21547428718511 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030122247/5000000000 : ℝ)^4381 ≤ (1272449284023/10000000000000 : ℝ)^3357 := by
    have hnat : (1030122247 : ℕ)^4381*10000000000000^3357 ≤ 1272449284023^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030122247 5000000000 1272449284023 10000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336885911/2500000000 : ℝ), (2623273679/5000000000 : ℝ), (-1030122247/5000000000 : ℝ)] ![(22090324855033/50000000000000 : ℝ), (21547428718511/50000000000000 : ℝ), (1272449284023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336885911/2500000000 : ℝ)|^4381 ≤ (22090324855033/50000000000000 : ℝ)^3357
        have hw : |(1336885911/2500000000 : ℝ)|=(1336885911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623273679/5000000000 : ℝ)|^4381 ≤ (21547428718511/50000000000000 : ℝ)^3357
        have hw : |(2623273679/5000000000 : ℝ)|=(2623273679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030122247/5000000000 : ℝ)|^4381 ≤ (1272449284023/10000000000000 : ℝ)^3357
        have hw : |(-1030122247/5000000000 : ℝ)|=(1030122247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s5_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153182417/5000000000 : ℝ)*x 0 + (4134561489/10000000000 : ℝ)*x 1 + (1121147003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153182417/5000000000 : ℝ)^4381 ≤ (6660887245353/20000000000000 : ℝ)^3357 := by
    have hnat : (2153182417 : ℕ)^4381*20000000000000^3357 ≤ 6660887245353^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153182417 5000000000 6660887245353 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4134561489/10000000000 : ℝ)^4381 ≤ (3158110336049/10000000000000 : ℝ)^3357 := by
    have hnat : (4134561489 : ℕ)^4381*10000000000000^3357 ≤ 3158110336049^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134561489 10000000000 3158110336049 10000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121147003/2500000000 : ℝ)^4381 ≤ (1097326887491/3125000000000 : ℝ)^3357 := by
    have hnat : (1121147003 : ℕ)^4381*3125000000000^3357 ≤ 1097326887491^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121147003 2500000000 1097326887491 3125000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153182417/5000000000 : ℝ), (4134561489/10000000000 : ℝ), (1121147003/2500000000 : ℝ)] ![(6660887245353/20000000000000 : ℝ), (3158110336049/10000000000000 : ℝ), (1097326887491/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153182417/5000000000 : ℝ)|^4381 ≤ (6660887245353/20000000000000 : ℝ)^3357
        have hw : |(2153182417/5000000000 : ℝ)|=(2153182417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4134561489/10000000000 : ℝ)|^4381 ≤ (3158110336049/10000000000000 : ℝ)^3357
        have hw : |(4134561489/10000000000 : ℝ)|=(4134561489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121147003/2500000000 : ℝ)|^4381 ≤ (1097326887491/3125000000000 : ℝ)^3357
        have hw : |(1121147003/2500000000 : ℝ)|=(1121147003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s5_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1977629023/10000000000 : ℝ)*x 0 + (5247133903/10000000000 : ℝ)*x 1 + (108164683/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977629023/10000000000 : ℝ)^4381 ≤ (12062710010543/100000000000000 : ℝ)^3357 := by
    have hnat : (1977629023 : ℕ)^4381*100000000000000^3357 ≤ 12062710010543^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977629023 10000000000 12062710010543 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247133903/10000000000 : ℝ)^4381 ≤ (10775286250567/25000000000000 : ℝ)^3357 := by
    have hnat : (5247133903 : ℕ)^4381*25000000000000^3357 ≤ 10775286250567^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247133903 10000000000 10775286250567 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108164683/200000000 : ℝ)^4381 ≤ (44836144977139/100000000000000 : ℝ)^3357 := by
    have hnat : (108164683 : ℕ)^4381*100000000000000^3357 ≤ 44836144977139^3357*200000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108164683 200000000 44836144977139 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1977629023/10000000000 : ℝ), (5247133903/10000000000 : ℝ), (108164683/200000000 : ℝ)] ![(12062710010543/100000000000000 : ℝ), (10775286250567/25000000000000 : ℝ), (44836144977139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1977629023/10000000000 : ℝ)|^4381 ≤ (12062710010543/100000000000000 : ℝ)^3357
        have hw : |(-1977629023/10000000000 : ℝ)|=(1977629023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247133903/10000000000 : ℝ)|^4381 ≤ (10775286250567/25000000000000 : ℝ)^3357
        have hw : |(5247133903/10000000000 : ℝ)|=(5247133903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108164683/200000000 : ℝ)|^4381 ≤ (44836144977139/100000000000000 : ℝ)^3357
        have hw : |(108164683/200000000 : ℝ)|=(108164683/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s5_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061077991/2000000000 : ℝ)*x 0 + (-1898557131/10000000000 : ℝ)*x 1 + (1352058537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061077991/2000000000 : ℝ)^4381 ≤ (43726695706253/100000000000000 : ℝ)^3357 := by
    have hnat : (1061077991 : ℕ)^4381*100000000000000^3357 ≤ 43726695706253^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061077991 2000000000 43726695706253 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1898557131/10000000000 : ℝ)^4381 ≤ (2859289830481/25000000000000 : ℝ)^3357 := by
    have hnat : (1898557131 : ℕ)^4381*25000000000000^3357 ≤ 2859289830481^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898557131 10000000000 2859289830481 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352058537/2500000000 : ℝ)^4381 ≤ (89672289911/200000000000 : ℝ)^3357 := by
    have hnat : (1352058537 : ℕ)^4381*200000000000^3357 ≤ 89672289911^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352058537 2500000000 89672289911 200000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061077991/2000000000 : ℝ), (-1898557131/10000000000 : ℝ), (1352058537/2500000000 : ℝ)] ![(43726695706253/100000000000000 : ℝ), (2859289830481/25000000000000 : ℝ), (89672289911/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061077991/2000000000 : ℝ)|^4381 ≤ (43726695706253/100000000000000 : ℝ)^3357
        have hw : |(1061077991/2000000000 : ℝ)|=(1061077991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1898557131/10000000000 : ℝ)|^4381 ≤ (2859289830481/25000000000000 : ℝ)^3357
        have hw : |(-1898557131/10000000000 : ℝ)|=(1898557131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352058537/2500000000 : ℝ)|^4381 ≤ (89672289911/200000000000 : ℝ)^3357
        have hw : |(1352058537/2500000000 : ℝ)|=(1352058537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s5_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652694981/5000000000 : ℝ)*x 0 + (1352058537/2500000000 : ℝ)*x 1 + (-949278561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652694981/5000000000 : ℝ)^4381 ≤ (8745339156309/20000000000000 : ℝ)^3357 := by
    have hnat : (2652694981 : ℕ)^4381*20000000000000^3357 ≤ 8745339156309^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652694981 5000000000 8745339156309 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352058537/2500000000 : ℝ)^4381 ≤ (89672289911/200000000000 : ℝ)^3357 := by
    have hnat : (1352058537 : ℕ)^4381*200000000000^3357 ≤ 89672289911^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352058537 2500000000 89672289911 200000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949278561/5000000000 : ℝ)^4381 ≤ (11437159251169/100000000000000 : ℝ)^3357 := by
    have hnat : (949278561 : ℕ)^4381*100000000000000^3357 ≤ 11437159251169^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949278561 5000000000 11437159251169 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652694981/5000000000 : ℝ), (1352058537/2500000000 : ℝ), (-949278561/5000000000 : ℝ)] ![(8745339156309/20000000000000 : ℝ), (89672289911/200000000000 : ℝ), (11437159251169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652694981/5000000000 : ℝ)|^4381 ≤ (8745339156309/20000000000000 : ℝ)^3357
        have hw : |(2652694981/5000000000 : ℝ)|=(2652694981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352058537/2500000000 : ℝ)|^4381 ≤ (89672289911/200000000000 : ℝ)^3357
        have hw : |(1352058537/2500000000 : ℝ)|=(1352058537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949278561/5000000000 : ℝ)|^4381 ≤ (11437159251169/100000000000000 : ℝ)^3357
        have hw : |(-949278561/5000000000 : ℝ)|=(949278561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s5_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538298691/1250000000 : ℝ)*x 0 + (2241662131/5000000000 : ℝ)*x 1 + (4135831839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538298691/1250000000 : ℝ)^4381 ≤ (33304685459453/100000000000000 : ℝ)^3357 := by
    have hnat : (538298691 : ℕ)^4381*100000000000000^3357 ≤ 33304685459453^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538298691 1250000000 33304685459453 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241662131/5000000000 : ℝ)^4381 ≤ (3510154737861/10000000000000 : ℝ)^3357 := by
    have hnat : (2241662131 : ℕ)^4381*10000000000000^3357 ≤ 3510154737861^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241662131 5000000000 3510154737861 10000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4135831839/10000000000 : ℝ)^4381 ≤ (15796883572289/50000000000000 : ℝ)^3357 := by
    have hnat : (4135831839 : ℕ)^4381*50000000000000^3357 ≤ 15796883572289^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135831839 10000000000 15796883572289 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538298691/1250000000 : ℝ), (2241662131/5000000000 : ℝ), (4135831839/10000000000 : ℝ)] ![(33304685459453/100000000000000 : ℝ), (3510154737861/10000000000000 : ℝ), (15796883572289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538298691/1250000000 : ℝ)|^4381 ≤ (33304685459453/100000000000000 : ℝ)^3357
        have hw : |(538298691/1250000000 : ℝ)|=(538298691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241662131/5000000000 : ℝ)|^4381 ≤ (3510154737861/10000000000000 : ℝ)^3357
        have hw : |(2241662131/5000000000 : ℝ)|=(2241662131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4135831839/10000000000 : ℝ)|^4381 ≤ (15796883572289/50000000000000 : ℝ)^3357
        have hw : |(4135831839/10000000000 : ℝ)|=(4135831839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (283/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2259/20000 : ℝ) ^ (1095/256 : ℝ) ≤ (1777865299788641/20000000000000000000 : ℝ) := by
    have hpowers : (2259/20000 : ℝ)^1095 ≤ (1777865299788641/20000000000000000000 : ℝ)^256 := by
      have hnat : (2259 : ℕ)^1095*20000000000000000000^256 ≤ 1777865299788641^256*20000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2259 20000 1777865299788641 20000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2259/20000 : ℝ)) (X := (1777865299788641/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14783/100000 : ℝ) ^ (1095/256 : ℝ) ≤ (562107193245079/2000000000000000000 : ℝ) := by
    have hpowers : (14783/100000 : ℝ)^1095 ≤ (562107193245079/2000000000000000000 : ℝ)^256 := by
      have hnat : (14783 : ℕ)^1095*2000000000000000000^256 ≤ 562107193245079^256*100000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14783 100000 562107193245079 2000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14783/100000 : ℝ)) (X := (562107193245079/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001777865299788641/10000000000000000000 : ℝ) ≤ (250010390468503/250000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (10001777865299788641/10000000000000000000 : ℝ)^256 ≤ (250010390468503/250000000000000 : ℝ)^1095 := by
      have hnat : (10001777865299788641 : ℕ)^256*250000000000000^1095 ≤ 250010390468503^1095*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001777865299788641 10000000000000000000 250010390468503 250000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250010390468503/250000000000000 : ℝ)) (X := (10001777865299788641/10000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007398937232239431/20000000000000000000 : ℝ) ≤ (10000864776044747/10000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (20007398937232239431/20000000000000000000 : ℝ)^256 ≤ (10000864776044747/10000000000000000 : ℝ)^1095 := by
      have hnat : (20007398937232239431 : ℕ)^256*10000000000000000^1095 ≤ 10000864776044747^1095*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007398937232239431 20000000000000000000 10000864776044747 10000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000864776044747/10000000000000000 : ℝ)) (X := (20007398937232239431/20000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000562107193245079/1000000000000000000 : ℝ) ≤ (5000656966674687/5000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (1000562107193245079/1000000000000000000 : ℝ)^256 ≤ (5000656966674687/5000000000000000 : ℝ)^1095 := by
      have hnat : (1000562107193245079 : ℕ)^256*5000000000000000^1095 ≤ 5000656966674687^1095*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000562107193245079 1000000000000000000 5000656966674687 5000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000656966674687/5000000000000000 : ℝ)) (X := (1000562107193245079/1000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1777865299788641/20000000000000000000 : ℝ) ≤ ((3487130321465401463/3488000000000000000 : ℝ)+2*(449157304627/348800000000000 : ℝ)*(2259/20000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (3487130321465401463/3488000000000000000 : ℝ)+2*(449157304627/348800000000000 : ℝ)*(2259/20000 : ℝ)=(250010390468503/250000000000000 : ℝ) by norm_num, show 1+2*(1777865299788641/20000000000000000000 : ℝ)=(10001777865299788641/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(562107193245079/2000000000000000000 : ℝ)+(1777865299788641/20000000000000000000 : ℝ) ≤ ((3487130321465401463/3488000000000000000 : ℝ)+(449157304627/348800000000000 : ℝ)*((14783/100000 : ℝ)+(2259/20000 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (3487130321465401463/3488000000000000000 : ℝ)+(449157304627/348800000000000 : ℝ)*((14783/100000 : ℝ)+(2259/20000 : ℝ))=(10000864776044747/10000000000000000 : ℝ) by norm_num, show 1+(562107193245079/2000000000000000000 : ℝ)+(1777865299788641/20000000000000000000 : ℝ)=(20007398937232239431/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(562107193245079/2000000000000000000 : ℝ) ≤ ((3487130321465401463/3488000000000000000 : ℝ)+2*(449157304627/348800000000000 : ℝ)*(14783/100000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (3487130321465401463/3488000000000000000 : ℝ)+2*(449157304627/348800000000000 : ℝ)*(14783/100000 : ℝ)=(5000656966674687/5000000000000000 : ℝ) by norm_num, show 1+2*(562107193245079/2000000000000000000 : ℝ)=(1000562107193245079/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3487130321465401463/3488000000000000000 : ℝ)*(X 1 0+X 2 0)+(449157304627/348800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (3487130321465401463/3488000000000000000 : ℝ)) (alpha := (449157304627/348800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3487130321465401463/3488000000000000000 : ℝ)*(X 0 1+X 2 1)+(449157304627/348800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (3487130321465401463/3488000000000000000 : ℝ)) (alpha := (449157304627/348800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3487130321465401463/3488000000000000000 : ℝ)*(X 0 2+X 1 2)+(449157304627/348800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (3487130321465401463/3488000000000000000 : ℝ)) (alpha := (449157304627/348800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1977617747/10000000000 : ℝ)*X 0 0+(5408824567/10000000000 : ℝ)*X 0 1+(81977287/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347543293/10000000000 : ℝ)*X 1 0+(-2060242831/10000000000 : ℝ)*X 1 1+(5246548961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336885911/2500000000 : ℝ)*X 2 0+(2623273679/5000000000 : ℝ)*X 2 1+(-1030122247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153182417/5000000000 : ℝ)*X 0 0+(4134561489/10000000000 : ℝ)*X 0 1+(1121147003/2500000000 : ℝ)*X 0 2+(2153182417/5000000000 : ℝ)*X 1 0+(4134561489/10000000000 : ℝ)*X 1 1+(1121147003/2500000000 : ℝ)*X 1 2+(2153182417/5000000000 : ℝ)*X 2 0+(4134561489/10000000000 : ℝ)*X 2 1+(1121147003/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1977629023/10000000000 : ℝ)*X 0 0+(5247133903/10000000000 : ℝ)*X 0 1+(108164683/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061077991/2000000000 : ℝ)*X 1 0+(-1898557131/10000000000 : ℝ)*X 1 1+(1352058537/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652694981/5000000000 : ℝ)*X 2 0+(1352058537/2500000000 : ℝ)*X 2 1+(-949278561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538298691/1250000000 : ℝ)*X 0 0+(2241662131/5000000000 : ℝ)*X 0 1+(4135831839/10000000000 : ℝ)*X 0 2+(538298691/1250000000 : ℝ)*X 1 0+(2241662131/5000000000 : ℝ)*X 1 1+(4135831839/10000000000 : ℝ)*X 1 2+(538298691/1250000000 : ℝ)*X 2 0+(2241662131/5000000000 : ℝ)*X 2 1+(4135831839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101308578552435511396227639/17440000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89291/250000000000 : ℝ)*(base19) + (37258853/20000000000000 : ℝ)*(base23) + (17876863/25000000000000 : ℝ)*(upper2) + (38778711/10000000000000 : ℝ)*(upper3) + (901937400779251/20000000000000 : ℝ)*(major0) + (901937400779251/20000000000000 : ℝ)*(major1) + (901937400779251/20000000000000 : ℝ)*(major2) + (3081174485221217/50000000000000 : ℝ)*(sp0) + (1232484965671251/20000000000000 : ℝ)*(sp1) + (6162375503807709/100000000000000 : ℝ)*(sp2) + (22319803928859/781250000000 : ℝ)*(sp3) + (3794681511/5000000000000 : ℝ)*(sp4) + (1229349267/2500000000000 : ℝ)*(sp6) + (14047193291/100000000000000 : ℝ)*(sp7) + (714237237521811/25000000000000 : ℝ)*(f.failure) + (1232484972814531/20000000000000 : ℝ)*(f.sum) + (5695400586327/3488000000000000000000000000 : ℝ)*base66 + (222135367138865787/69760000000000000000000000000000 : ℝ)*base68 + (387321660062385787/69760000000000000000000000000000 : ℝ)*base70 + (110716287271345787/69760000000000000000000000000000 : ℝ)*base72 + (4070324461257/3488000000000000000000000000 : ℝ)*base73 + (267076930070065787/69760000000000000000000000000000 : ℝ)*base76 + (234583401811505787/69760000000000000000000000000000 : ℝ)*base78 + (759043307474894213/69760000000000000000000000000000 : ℝ)*base79 + (5954104310281/3488000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5535869/1250000000000000000000 : ℝ)*base89 + (5535869/1250000000000000000000 : ℝ)*base91 + (5535869/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1389636589865229127220187663/174400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (673955781/50000000000000 : ℝ)*(base19) + (1465293493/100000000000000 : ℝ)*(base23) + (80424089/50000000000000 : ℝ)*(upper3) + (24475087/50000000000000 : ℝ)*(lower4) + (169472113/100000000000000 : ℝ)*(upper5) + (4542537435677533/100000000000000 : ℝ)*(major0) + (4542537435677533/100000000000000 : ℝ)*(major1) + (4542537435677533/100000000000000 : ℝ)*(major2) + (220741361/781250000000 : ℝ)*(sp1) + (7596264661/25000000000000 : ℝ)*(sp2) + (387957153362449/6250000000000 : ℝ)*(sp4) + (1241456970198683/20000000000000 : ℝ)*(sp5) + (6207282603447047/100000000000000 : ℝ)*(sp6) + (57555203039051/2000000000000 : ℝ)*(sp7) + (57555203039051/2000000000000 : ℝ)*(f.failure) + (387957153362449/6250000000000 : ℝ)*(f.sum) + (24515032155271/17440000000000000000000000000 : ℝ)*base65 + (1220838640591259221/348800000000000000000000000000000 : ℝ)*base68 + (3218419253866340779/348800000000000000000000000000000 : ℝ)*base69 + (826796497159140779/348800000000000000000000000000000 : ℝ)*base71 + (29236498495911/17440000000000000000000000000 : ℝ)*base73 + (5404795620284059221/348800000000000000000000000000000 : ℝ)*base76 + (158946458026340779/348800000000000000000000000000000 : ℝ)*base77 + (2989774380835940779/348800000000000000000000000000000 : ℝ)*base79 + (39746510569991/17440000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (550171/100000000000000000000 : ℝ)*base90 + (550171/100000000000000000000 : ℝ)*base92 + (550171/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1421_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1421_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1421_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (633/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1421_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1421_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1421_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (633/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1119_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:50.972471+00:00
-- url     : https://prove2.me/submissions/7fe88220-8858-4dc2-9162-824186a130bd

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
theorem support_rectangle_w1119_s0_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-379822313/2000000000 : ℝ)*x 0 + (6059661397/10000000000 : ℝ)*x 1 + (74649321/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379822313/2000000000 : ℝ)^1039 ≤ (2758127069757/25000000000000 : ℝ)^783 := by
    have hnat : (379822313 : ℕ)^1039*25000000000000^783 ≤ 2758127069757^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379822313 2000000000 2758127069757 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6059661397/10000000000 : ℝ)^1039 ≤ (51442298090623/100000000000000 : ℝ)^783 := by
    have hnat : (6059661397 : ℕ)^1039*100000000000000^783 ≤ 51442298090623^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6059661397 10000000000 51442298090623 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74649321/156250000 : ℝ)^1039 ≤ (37525193617051/100000000000000 : ℝ)^783 := by
    have hnat : (74649321 : ℕ)^1039*100000000000000^783 ≤ 37525193617051^783*156250000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74649321 156250000 37525193617051 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379822313/2000000000 : ℝ), (6059661397/10000000000 : ℝ), (74649321/156250000 : ℝ)] ![(2758127069757/25000000000000 : ℝ), (51442298090623/100000000000000 : ℝ), (37525193617051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379822313/2000000000 : ℝ)|^1039 ≤ (2758127069757/25000000000000 : ℝ)^783
        have hw : |(-379822313/2000000000 : ℝ)|=(379822313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6059661397/10000000000 : ℝ)|^1039 ≤ (51442298090623/100000000000000 : ℝ)^783
        have hw : |(6059661397/10000000000 : ℝ)|=(6059661397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74649321/156250000 : ℝ)|^1039 ≤ (37525193617051/100000000000000 : ℝ)^783
        have hw : |(74649321/156250000 : ℝ)|=(74649321/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s0_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1379522281/2500000000 : ℝ)*x 0 + (-658888103/2500000000 : ℝ)*x 1 + (4777556581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379522281/2500000000 : ℝ)^1039 ≤ (45432552760521/100000000000000 : ℝ)^783 := by
    have hnat : (1379522281 : ℕ)^1039*100000000000000^783 ≤ 45432552760521^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379522281 2500000000 45432552760521 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658888103/2500000000 : ℝ)^1039 ≤ (8521126609471/50000000000000 : ℝ)^783 := by
    have hnat : (658888103 : ℕ)^1039*50000000000000^783 ≤ 8521126609471^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658888103 2500000000 8521126609471 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4777556581/10000000000 : ℝ)^1039 ≤ (18762597001341/50000000000000 : ℝ)^783 := by
    have hnat : (4777556581 : ℕ)^1039*50000000000000^783 ≤ 18762597001341^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4777556581 10000000000 18762597001341 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379522281/2500000000 : ℝ), (-658888103/2500000000 : ℝ), (4777556581/10000000000 : ℝ)] ![(45432552760521/100000000000000 : ℝ), (8521126609471/50000000000000 : ℝ), (18762597001341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379522281/2500000000 : ℝ)|^1039 ≤ (45432552760521/100000000000000 : ℝ)^783
        have hw : |(1379522281/2500000000 : ℝ)|=(1379522281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-658888103/2500000000 : ℝ)|^1039 ≤ (8521126609471/50000000000000 : ℝ)^783
        have hw : |(-658888103/2500000000 : ℝ)|=(658888103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4777556581/10000000000 : ℝ)|^1039 ≤ (18762597001341/50000000000000 : ℝ)^783
        have hw : |(4777556581/10000000000 : ℝ)|=(4777556581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s0_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (220723571/400000000 : ℝ)*x 0 + (119438911/250000000 : ℝ)*x 1 + (-329444049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220723571/400000000 : ℝ)^1039 ≤ (11358138602559/25000000000000 : ℝ)^783 := by
    have hnat : (220723571 : ℕ)^1039*25000000000000^783 ≤ 11358138602559^783*400000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220723571 400000000 11358138602559 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119438911/250000000 : ℝ)^1039 ≤ (37525192533113/100000000000000 : ℝ)^783 := by
    have hnat : (119438911 : ℕ)^1039*100000000000000^783 ≤ 37525192533113^783*250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119438911 250000000 37525192533113 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329444049/1250000000 : ℝ)^1039 ≤ (17042253047333/100000000000000 : ℝ)^783 := by
    have hnat : (329444049 : ℕ)^1039*100000000000000^783 ≤ 17042253047333^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329444049 1250000000 17042253047333 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220723571/400000000 : ℝ), (119438911/250000000 : ℝ), (-329444049/1250000000 : ℝ)] ![(11358138602559/25000000000000 : ℝ), (37525192533113/100000000000000 : ℝ), (17042253047333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220723571/400000000 : ℝ)|^1039 ≤ (11358138602559/25000000000000 : ℝ)^783
        have hw : |(220723571/400000000 : ℝ)|=(220723571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119438911/250000000 : ℝ)|^1039 ≤ (37525192533113/100000000000000 : ℝ)^783
        have hw : |(119438911/250000000 : ℝ)|=(119438911/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-329444049/1250000000 : ℝ)|^1039 ≤ (17042253047333/100000000000000 : ℝ)^783
        have hw : |(-329444049/1250000000 : ℝ)|=(329444049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s0_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (65669649/156250000 : ℝ)*x 0 + (1561083987/5000000000 : ℝ)*x 1 + (5661380739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65669649/156250000 : ℝ)^1039 ≤ (6331308618589/20000000000000 : ℝ)^783 := by
    have hnat : (65669649 : ℕ)^1039*20000000000000^783 ≤ 6331308618589^783*156250000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65669649 156250000 6331308618589 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561083987/5000000000 : ℝ)^1039 ≤ (5334699284821/25000000000000 : ℝ)^783 := by
    have hnat : (1561083987 : ℕ)^1039*25000000000000^783 ≤ 5334699284821^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561083987 5000000000 5334699284821 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5661380739/10000000000 : ℝ)^1039 ≤ (5875582469587/12500000000000 : ℝ)^783 := by
    have hnat : (5661380739 : ℕ)^1039*12500000000000^783 ≤ 5875582469587^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661380739 10000000000 5875582469587 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65669649/156250000 : ℝ), (1561083987/5000000000 : ℝ), (5661380739/10000000000 : ℝ)] ![(6331308618589/20000000000000 : ℝ), (5334699284821/25000000000000 : ℝ), (5875582469587/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65669649/156250000 : ℝ)|^1039 ≤ (6331308618589/20000000000000 : ℝ)^783
        have hw : |(65669649/156250000 : ℝ)|=(65669649/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1561083987/5000000000 : ℝ)|^1039 ≤ (5334699284821/25000000000000 : ℝ)^783
        have hw : |(1561083987/5000000000 : ℝ)|=(1561083987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5661380739/10000000000 : ℝ)|^1039 ≤ (5875582469587/12500000000000 : ℝ)^783
        have hw : |(5661380739/10000000000 : ℝ)|=(5661380739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s0_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-238040803/1250000000 : ℝ)*x 0 + (4810642743/10000000000 : ℝ)*x 1 + (6025412919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238040803/1250000000 : ℝ)^1039 ≤ (2214545153137/20000000000000 : ℝ)^783 := by
    have hnat : (238040803 : ℕ)^1039*20000000000000^783 ≤ 2214545153137^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238040803 1250000000 2214545153137 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4810642743/10000000000 : ℝ)^1039 ≤ (18935211757489/50000000000000 : ℝ)^783 := by
    have hnat : (4810642743 : ℕ)^1039*50000000000000^783 ≤ 18935211757489^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810642743 10000000000 18935211757489 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6025412919/10000000000 : ℝ)^1039 ≤ (25528425349719/50000000000000 : ℝ)^783 := by
    have hnat : (6025412919 : ℕ)^1039*50000000000000^783 ≤ 25528425349719^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6025412919 10000000000 25528425349719 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-238040803/1250000000 : ℝ), (4810642743/10000000000 : ℝ), (6025412919/10000000000 : ℝ)] ![(2214545153137/20000000000000 : ℝ), (18935211757489/50000000000000 : ℝ), (25528425349719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-238040803/1250000000 : ℝ)|^1039 ≤ (2214545153137/20000000000000 : ℝ)^783
        have hw : |(-238040803/1250000000 : ℝ)|=(238040803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4810642743/10000000000 : ℝ)|^1039 ≤ (18935211757489/50000000000000 : ℝ)^783
        have hw : |(4810642743/10000000000 : ℝ)|=(4810642743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6025412919/10000000000 : ℝ)|^1039 ≤ (25528425349719/50000000000000 : ℝ)^783
        have hw : |(6025412919/10000000000 : ℝ)|=(6025412919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s0_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5169824561/10000000000 : ℝ)*x 0 + (-346924201/2500000000 : ℝ)*x 1 + (602541619/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169824561/10000000000 : ℝ)^1039 ≤ (20833747743359/50000000000000 : ℝ)^783 := by
    have hnat : (5169824561 : ℕ)^1039*50000000000000^783 ≤ 20833747743359^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169824561 10000000000 20833747743359 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346924201/2500000000 : ℝ)^1039 ≤ (7275617018443/100000000000000 : ℝ)^783 := by
    have hnat : (346924201 : ℕ)^1039*100000000000000^783 ≤ 7275617018443^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346924201 2500000000 7275617018443 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (602541619/1000000000 : ℝ)^1039 ≤ (51056887478579/100000000000000 : ℝ)^783 := by
    have hnat : (602541619 : ℕ)^1039*100000000000000^783 ≤ 51056887478579^783*1000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602541619 1000000000 51056887478579 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169824561/10000000000 : ℝ), (-346924201/2500000000 : ℝ), (602541619/1000000000 : ℝ)] ![(20833747743359/50000000000000 : ℝ), (7275617018443/100000000000000 : ℝ), (51056887478579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169824561/10000000000 : ℝ)|^1039 ≤ (20833747743359/50000000000000 : ℝ)^783
        have hw : |(5169824561/10000000000 : ℝ)|=(5169824561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-346924201/2500000000 : ℝ)|^1039 ≤ (7275617018443/100000000000000 : ℝ)^783
        have hw : |(-346924201/2500000000 : ℝ)|=(346924201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(602541619/1000000000 : ℝ)|^1039 ≤ (51056887478579/100000000000000 : ℝ)^783
        have hw : |(602541619/1000000000 : ℝ)|=(602541619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s0_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2584914353/5000000000 : ℝ)*x 0 + (3012706661/5000000000 : ℝ)*x 1 + (-1387695067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584914353/5000000000 : ℝ)^1039 ≤ (20833769908473/50000000000000 : ℝ)^783 := by
    have hnat : (2584914353 : ℕ)^1039*50000000000000^783 ≤ 20833769908473^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584914353 5000000000 20833769908473 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3012706661/5000000000 : ℝ)^1039 ≤ (12764213807693/25000000000000 : ℝ)^783 := by
    have hnat : (3012706661 : ℕ)^1039*25000000000000^783 ≤ 12764213807693^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3012706661 5000000000 12764213807693 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387695067/10000000000 : ℝ)^1039 ≤ (7275604933941/100000000000000 : ℝ)^783 := by
    have hnat : (1387695067 : ℕ)^1039*100000000000000^783 ≤ 7275604933941^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387695067 10000000000 7275604933941 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584914353/5000000000 : ℝ), (3012706661/5000000000 : ℝ), (-1387695067/10000000000 : ℝ)] ![(20833769908473/50000000000000 : ℝ), (12764213807693/25000000000000 : ℝ), (7275604933941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584914353/5000000000 : ℝ)|^1039 ≤ (20833769908473/50000000000000 : ℝ)^783
        have hw : |(2584914353/5000000000 : ℝ)|=(2584914353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3012706661/5000000000 : ℝ)|^1039 ≤ (12764213807693/25000000000000 : ℝ)^783
        have hw : |(3012706661/5000000000 : ℝ)|=(3012706661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1387695067/10000000000 : ℝ)|^1039 ≤ (7275604933941/100000000000000 : ℝ)^783
        have hw : |(-1387695067/10000000000 : ℝ)|=(1387695067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s0_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (842636399/2000000000 : ℝ)*x 0 + (5595856977/10000000000 : ℝ)*x 1 + (1594996413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842636399/2000000000 : ℝ)^1039 ≤ (3175977505481/10000000000000 : ℝ)^783 := by
    have hnat : (842636399 : ℕ)^1039*10000000000000^783 ≤ 3175977505481^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842636399 2000000000 3175977505481 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5595856977/10000000000 : ℝ)^1039 ≤ (5785517365591/12500000000000 : ℝ)^783 := by
    have hnat : (5595856977 : ℕ)^1039*12500000000000^783 ≤ 5785517365591^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595856977 10000000000 5785517365591 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594996413/5000000000 : ℝ)^1039 ≤ (5489021500789/25000000000000 : ℝ)^783 := by
    have hnat : (1594996413 : ℕ)^1039*25000000000000^783 ≤ 5489021500789^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594996413 5000000000 5489021500789 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842636399/2000000000 : ℝ), (5595856977/10000000000 : ℝ), (1594996413/5000000000 : ℝ)] ![(3175977505481/10000000000000 : ℝ), (5785517365591/12500000000000 : ℝ), (5489021500789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842636399/2000000000 : ℝ)|^1039 ≤ (3175977505481/10000000000000 : ℝ)^783
        have hw : |(842636399/2000000000 : ℝ)|=(842636399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5595856977/10000000000 : ℝ)|^1039 ≤ (5785517365591/12500000000000 : ℝ)^783
        have hw : |(5595856977/10000000000 : ℝ)|=(5595856977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594996413/5000000000 : ℝ)|^1039 ≤ (5489021500789/25000000000000 : ℝ)^783
        have hw : |(1594996413/5000000000 : ℝ)|=(1594996413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (159/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (872/3125 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (8311/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8311 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8311*1^2048 ≤ 0^2048*1^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8311/2048 : ℝ) ≤ (2427266570252791923/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8311 ≤ (2427266570252791923/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8311*100000000000000000000^2048 ≤ 2427266570252791923^2048*5^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2427266570252791923 100000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2427266570252791923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8311 := by
      have hnat : (1 : ℕ)^2048*1^8311 ≤ 1^8311*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102427266570252791923/100000000000000000000 : ℝ) ≤ (10059273405929987/10000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (102427266570252791923/100000000000000000000 : ℝ)^2048 ≤ (10059273405929987/10000000000000000 : ℝ)^8311 := by
      have hnat : (102427266570252791923 : ℕ)^2048*10000000000000000^8311 ≤ 10059273405929987^8311*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102427266570252791923 100000000000000000000 10059273405929987 10000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059273405929987/10000000000000000 : ℝ)) (X := (102427266570252791923/100000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52427266570252791923/50000000000000000000 : ℝ) ≤ (5059273405929987/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (52427266570252791923/50000000000000000000 : ℝ)^2048 ≤ (5059273405929987/5000000000000000 : ℝ)^8311 := by
      have hnat : (52427266570252791923 : ℕ)^2048*5000000000000000^8311 ≤ 5059273405929987^8311*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52427266570252791923 50000000000000000000 5059273405929987 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059273405929987/5000000000000000 : ℝ)) (X := (52427266570252791923/50000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59273405929987/4000000000000000 : ℝ)*(0 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59273405929987/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2427266570252791923/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59273405929987/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (1 : ℝ)+(59273405929987/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059273405929987/10000000000000000 : ℝ) by norm_num, show 1+(2427266570252791923/100000000000000000000 : ℝ)+(0 : ℝ)=(102427266570252791923/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2427266570252791923/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59273405929987/4000000000000000 : ℝ)*(2/5 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59273405929987/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059273405929987/5000000000000000 : ℝ) by norm_num, show 1+2*(2427266570252791923/100000000000000000000 : ℝ)=(52427266570252791923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59273405929987/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59273405929987/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59273405929987/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59273405929987/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59273405929987/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59273405929987/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-379822313/2000000000 : ℝ)*X 0 0+(6059661397/10000000000 : ℝ)*X 0 1+(74649321/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1379522281/2500000000 : ℝ)*X 1 0+(-658888103/2500000000 : ℝ)*X 1 1+(4777556581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((220723571/400000000 : ℝ)*X 2 0+(119438911/250000000 : ℝ)*X 2 1+(-329444049/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((65669649/156250000 : ℝ)*X 0 0+(1561083987/5000000000 : ℝ)*X 0 1+(5661380739/10000000000 : ℝ)*X 0 2+(65669649/156250000 : ℝ)*X 1 0+(1561083987/5000000000 : ℝ)*X 1 1+(5661380739/10000000000 : ℝ)*X 1 2+(65669649/156250000 : ℝ)*X 2 0+(1561083987/5000000000 : ℝ)*X 2 1+(5661380739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-238040803/1250000000 : ℝ)*X 0 0+(4810642743/10000000000 : ℝ)*X 0 1+(6025412919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5169824561/10000000000 : ℝ)*X 1 0+(-346924201/2500000000 : ℝ)*X 1 1+(602541619/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584914353/5000000000 : ℝ)*X 2 0+(3012706661/5000000000 : ℝ)*X 2 1+(-1387695067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((842636399/2000000000 : ℝ)*X 0 0+(5595856977/10000000000 : ℝ)*X 0 1+(1594996413/5000000000 : ℝ)*X 0 2+(842636399/2000000000 : ℝ)*X 1 0+(5595856977/10000000000 : ℝ)*X 1 1+(1594996413/5000000000 : ℝ)*X 1 2+(842636399/2000000000 : ℝ)*X 2 0+(5595856977/10000000000 : ℝ)*X 2 1+(1594996413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7244846750872918851/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40384559/50000000000000 : ℝ)*(base1) + (448251997/25000000000000 : ℝ)*(base19) + (337331847/20000000000000 : ℝ)*(base23) + (15961553/12500000000000 : ℝ)*(base24) + (413417837/100000000000000 : ℝ)*(upper3) + (586902672676717/100000000000000 : ℝ)*(major0) + (586902672676717/100000000000000 : ℝ)*(major1) + (586902672676717/100000000000000 : ℝ)*(major2) + (779973338289669/100000000000000 : ℝ)*(sp0) + (389987684678299/50000000000000 : ℝ)*(sp1) + (779975348012927/100000000000000 : ℝ)*(sp2) + (196912346942037/50000000000000 : ℝ)*(sp3) + (780968807/20000000000000 : ℝ)*(sp4) + (3166840761/100000000000000 : ℝ)*(sp7) + (393827941493953/100000000000000 : ℝ)*(f.failure) + (389988581182293/50000000000000 : ℝ)*(f.sum) + (610390580212679/200000000000000000000000000000 : ℝ)*base65 + (1768966481387321/400000000000000000000000000000 : ℝ)*base68 + (817119362187321/400000000000000000000000000000 : ℝ)*base70 + (703342017387321/400000000000000000000000000000 : ℝ)*base72 + (485811747612679/200000000000000000000000000000 : ℝ)*base73 + (1394335096987321/400000000000000000000000000000 : ℝ)*base76 + (198789126587321/400000000000000000000000000000 : ℝ)*base78 + (2500688194187321/400000000000000000000000000000 : ℝ)*base80 + (513654009412679/200000000000000000000000000000 : ℝ)*base81 + (3267489/2500000000000000000000 : ℝ)*base90 + (3267489/2500000000000000000000 : ℝ)*base92 + (3267489/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (876598889450337307445217/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1202719469/100000000000000 : ℝ)*(base19) + (74089849/3125000000000 : ℝ)*(base23) + (221784761/50000000000000 : ℝ)*(base39) + (79487637/25000000000000 : ℝ)*(upper3) + (322151159/100000000000000 : ℝ)*(upper5) + (61942517183617/10000000000000 : ℝ)*(major0) + (61942517183617/10000000000000 : ℝ)*(major1) + (77428091033331/12500000000000 : ℝ)*(major2) + (1720339783/50000000000000 : ℝ)*(sp1) + (4588034327/100000000000000 : ℝ)*(sp2) + (102899771137869/12500000000000 : ℝ)*(sp4) + (205798381425979/25000000000000 : ℝ)*(sp5) + (823191653762979/100000000000000 : ℝ)*(sp6) + (103912859700057/25000000000000 : ℝ)*(sp7) + (103912859700057/25000000000000 : ℝ)*(f.failure) + (411599306336237/50000000000000 : ℝ)*(f.sum) + (459202862301683/200000000000000000000000000000 : ℝ)*base65 + (353874464796697/50000000000000000000000000000 : ℝ)*base67 + (5973876782979/40000000000000000000000000000 : ℝ)*base69 + (261167073396697/50000000000000000000000000000 : ℝ)*base71 + (1249682484701683/200000000000000000000000000000 : ℝ)*base73 + (140114396862979/40000000000000000000000000000 : ℝ)*base75 + (128881407062979/40000000000000000000000000000 : ℝ)*base77 + (8862589537021/40000000000000000000000000000 : ℝ)*base80 + (79160334402979/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4991641/625000000000000000000 : ℝ)*base90 + (4991641/625000000000000000000 : ℝ)*base92 + (4991641/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1119_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (872/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1119_s1_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052715889/5000000000 : ℝ)*x 0 + (2853858241/5000000000 : ℝ)*x 1 + (4997405267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052715889/5000000000 : ℝ)^1039 ≤ (6325271527677/50000000000000 : ℝ)^783 := by
    have hnat : (1052715889 : ℕ)^1039*50000000000000^783 ≤ 6325271527677^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052715889 5000000000 6325271527677 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2853858241/5000000000 : ℝ)^1039 ≤ (5939479120719/12500000000000 : ℝ)^783 := by
    have hnat : (2853858241 : ℕ)^1039*12500000000000^783 ≤ 5939479120719^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2853858241 5000000000 5939479120719 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4997405267/10000000000 : ℝ)^1039 ≤ (39833623960023/100000000000000 : ℝ)^783 := by
    have hnat : (4997405267 : ℕ)^1039*100000000000000^783 ≤ 39833623960023^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997405267 10000000000 39833623960023 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052715889/5000000000 : ℝ), (2853858241/5000000000 : ℝ), (4997405267/10000000000 : ℝ)] ![(6325271527677/50000000000000 : ℝ), (5939479120719/12500000000000 : ℝ), (39833623960023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052715889/5000000000 : ℝ)|^1039 ≤ (6325271527677/50000000000000 : ℝ)^783
        have hw : |(-1052715889/5000000000 : ℝ)|=(1052715889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2853858241/5000000000 : ℝ)|^1039 ≤ (5939479120719/12500000000000 : ℝ)^783
        have hw : |(2853858241/5000000000 : ℝ)|=(2853858241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4997405267/10000000000 : ℝ)|^1039 ≤ (39833623960023/100000000000000 : ℝ)^783
        have hw : |(4997405267/10000000000 : ℝ)|=(4997405267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s1_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5420390919/10000000000 : ℝ)*x 0 + (-2489208517/10000000000 : ℝ)*x 1 + (2498702537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420390919/10000000000 : ℝ)^1039 ≤ (44368275101399/100000000000000 : ℝ)^783 := by
    have hnat : (5420390919 : ℕ)^1039*100000000000000^783 ≤ 44368275101399^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420390919 10000000000 44368275101399 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2489208517/10000000000 : ℝ)^1039 ≤ (7899051484541/50000000000000 : ℝ)^783 := by
    have hnat : (2489208517 : ℕ)^1039*50000000000000^783 ≤ 7899051484541^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489208517 10000000000 7899051484541 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2498702537/5000000000 : ℝ)^1039 ≤ (19916810959339/50000000000000 : ℝ)^783 := by
    have hnat : (2498702537 : ℕ)^1039*50000000000000^783 ≤ 19916810959339^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498702537 5000000000 19916810959339 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420390919/10000000000 : ℝ), (-2489208517/10000000000 : ℝ), (2498702537/5000000000 : ℝ)] ![(44368275101399/100000000000000 : ℝ), (7899051484541/50000000000000 : ℝ), (19916810959339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420390919/10000000000 : ℝ)|^1039 ≤ (44368275101399/100000000000000 : ℝ)^783
        have hw : |(5420390919/10000000000 : ℝ)|=(5420390919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2489208517/10000000000 : ℝ)|^1039 ≤ (7899051484541/50000000000000 : ℝ)^783
        have hw : |(-2489208517/10000000000 : ℝ)|=(2489208517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2498702537/5000000000 : ℝ)|^1039 ≤ (19916810959339/50000000000000 : ℝ)^783
        have hw : |(2498702537/5000000000 : ℝ)|=(2498702537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s1_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5420392401/10000000000 : ℝ)*x 0 + (4997403707/10000000000 : ℝ)*x 1 + (-1244604161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420392401/10000000000 : ℝ)^1039 ≤ (22184145599181/50000000000000 : ℝ)^783 := by
    have hnat : (5420392401 : ℕ)^1039*50000000000000^783 ≤ 22184145599181^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420392401 10000000000 22184145599181 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4997403707/10000000000 : ℝ)^1039 ≤ (9958401865009/25000000000000 : ℝ)^783 := by
    have hnat : (4997403707 : ℕ)^1039*25000000000000^783 ≤ 9958401865009^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997403707 10000000000 9958401865009 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244604161/5000000000 : ℝ)^1039 ≤ (15798101326859/100000000000000 : ℝ)^783 := by
    have hnat : (1244604161 : ℕ)^1039*100000000000000^783 ≤ 15798101326859^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244604161 5000000000 15798101326859 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420392401/10000000000 : ℝ), (4997403707/10000000000 : ℝ), (-1244604161/5000000000 : ℝ)] ![(22184145599181/50000000000000 : ℝ), (9958401865009/25000000000000 : ℝ), (15798101326859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420392401/10000000000 : ℝ)|^1039 ≤ (22184145599181/50000000000000 : ℝ)^783
        have hw : |(5420392401/10000000000 : ℝ)|=(5420392401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4997403707/10000000000 : ℝ)|^1039 ≤ (9958401865009/25000000000000 : ℝ)^783
        have hw : |(4997403707/10000000000 : ℝ)|=(4997403707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1244604161/5000000000 : ℝ)|^1039 ≤ (15798101326859/100000000000000 : ℝ)^783
        have hw : |(-1244604161/5000000000 : ℝ)|=(1244604161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s1_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4319375717/10000000000 : ℝ)*x 0 + (229541917/625000000 : ℝ)*x 1 + (634930297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319375717/10000000000 : ℝ)^1039 ≤ (2051647528291/6250000000000 : ℝ)^783 := by
    have hnat : (4319375717 : ℕ)^1039*6250000000000^783 ≤ 2051647528291^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319375717 10000000000 2051647528291 6250000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229541917/625000000 : ℝ)^1039 ≤ (26469995983561/100000000000000 : ℝ)^783 := by
    have hnat : (229541917 : ℕ)^1039*100000000000000^783 ≤ 26469995983561^783*625000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229541917 625000000 26469995983561 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634930297/1250000000 : ℝ)^1039 ≤ (2035182177501/5000000000000 : ℝ)^783 := by
    have hnat : (634930297 : ℕ)^1039*5000000000000^783 ≤ 2035182177501^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634930297 1250000000 2035182177501 5000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319375717/10000000000 : ℝ), (229541917/625000000 : ℝ), (634930297/1250000000 : ℝ)] ![(2051647528291/6250000000000 : ℝ), (26469995983561/100000000000000 : ℝ), (2035182177501/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319375717/10000000000 : ℝ)|^1039 ≤ (2051647528291/6250000000000 : ℝ)^783
        have hw : |(4319375717/10000000000 : ℝ)|=(4319375717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229541917/625000000 : ℝ)|^1039 ≤ (26469995983561/100000000000000 : ℝ)^783
        have hw : |(229541917/625000000 : ℝ)|=(229541917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634930297/1250000000 : ℝ)|^1039 ≤ (2035182177501/5000000000000 : ℝ)^783
        have hw : |(634930297/1250000000 : ℝ)|=(634930297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s1_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106270713/10000000000 : ℝ)*x 0 + (5007189911/10000000000 : ℝ)*x 1 + (5697736491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106270713/10000000000 : ℝ)^1039 ≤ (3164308080007/25000000000000 : ℝ)^783 := by
    have hnat : (2106270713 : ℕ)^1039*25000000000000^783 ≤ 3164308080007^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106270713 10000000000 3164308080007 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5007189911/10000000000 : ℝ)^1039 ≤ (39937148422971/100000000000000 : ℝ)^783 := by
    have hnat : (5007189911 : ℕ)^1039*100000000000000^783 ≤ 39937148422971^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007189911 10000000000 39937148422971 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5697736491/10000000000 : ℝ)^1039 ≤ (47405619239329/100000000000000 : ℝ)^783 := by
    have hnat : (5697736491 : ℕ)^1039*100000000000000^783 ≤ 47405619239329^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697736491 10000000000 47405619239329 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106270713/10000000000 : ℝ), (5007189911/10000000000 : ℝ), (5697736491/10000000000 : ℝ)] ![(3164308080007/25000000000000 : ℝ), (39937148422971/100000000000000 : ℝ), (47405619239329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106270713/10000000000 : ℝ)|^1039 ≤ (3164308080007/25000000000000 : ℝ)^783
        have hw : |(-2106270713/10000000000 : ℝ)|=(2106270713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5007189911/10000000000 : ℝ)|^1039 ≤ (39937148422971/100000000000000 : ℝ)^783
        have hw : |(5007189911/10000000000 : ℝ)|=(5007189911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5697736491/10000000000 : ℝ)|^1039 ≤ (47405619239329/100000000000000 : ℝ)^783
        have hw : |(5697736491/10000000000 : ℝ)|=(5697736491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s1_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1309622763/2500000000 : ℝ)*x 0 + (-1788876723/10000000000 : ℝ)*x 1 + (356108517/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309622763/2500000000 : ℝ)^1039 ≤ (42403464278929/100000000000000 : ℝ)^783 := by
    have hnat : (1309622763 : ℕ)^1039*100000000000000^783 ≤ 42403464278929^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309622763 2500000000 42403464278929 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788876723/10000000000 : ℝ)^1039 ≤ (2547729722323/25000000000000 : ℝ)^783 := by
    have hnat : (1788876723 : ℕ)^1039*25000000000000^783 ≤ 2547729722323^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788876723 10000000000 2547729722323 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356108517/625000000 : ℝ)^1039 ≤ (47405616821501/100000000000000 : ℝ)^783 := by
    have hnat : (356108517 : ℕ)^1039*100000000000000^783 ≤ 47405616821501^783*625000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356108517 625000000 47405616821501 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309622763/2500000000 : ℝ), (-1788876723/10000000000 : ℝ), (356108517/625000000 : ℝ)] ![(42403464278929/100000000000000 : ℝ), (2547729722323/25000000000000 : ℝ), (47405616821501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309622763/2500000000 : ℝ)|^1039 ≤ (42403464278929/100000000000000 : ℝ)^783
        have hw : |(1309622763/2500000000 : ℝ)|=(1309622763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1788876723/10000000000 : ℝ)|^1039 ≤ (2547729722323/25000000000000 : ℝ)^783
        have hw : |(-1788876723/10000000000 : ℝ)|=(1788876723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356108517/625000000 : ℝ)|^1039 ≤ (47405616821501/100000000000000 : ℝ)^783
        have hw : |(356108517/625000000 : ℝ)|=(356108517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s1_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1047698217/2000000000 : ℝ)*x 0 + (227909457/400000000 : ℝ)*x 1 + (-1788876451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047698217/2000000000 : ℝ)^1039 ≤ (21201732316693/50000000000000 : ℝ)^783 := by
    have hnat : (1047698217 : ℕ)^1039*50000000000000^783 ≤ 21201732316693^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047698217 2000000000 21201732316693 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227909457/400000000 : ℝ)^1039 ≤ (11851404627667/25000000000000 : ℝ)^783 := by
    have hnat : (227909457 : ℕ)^1039*25000000000000^783 ≤ 11851404627667^783*400000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227909457 400000000 11851404627667 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1788876451/10000000000 : ℝ)^1039 ≤ (5095458416569/50000000000000 : ℝ)^783 := by
    have hnat : (1788876451 : ℕ)^1039*50000000000000^783 ≤ 5095458416569^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788876451 10000000000 5095458416569 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047698217/2000000000 : ℝ), (227909457/400000000 : ℝ), (-1788876451/10000000000 : ℝ)] ![(21201732316693/50000000000000 : ℝ), (11851404627667/25000000000000 : ℝ), (5095458416569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047698217/2000000000 : ℝ)|^1039 ≤ (21201732316693/50000000000000 : ℝ)^783
        have hw : |(1047698217/2000000000 : ℝ)|=(1047698217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227909457/400000000 : ℝ)|^1039 ≤ (11851404627667/25000000000000 : ℝ)^783
        have hw : |(227909457/400000000 : ℝ)|=(227909457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1788876451/10000000000 : ℝ)|^1039 ≤ (5095458416569/50000000000000 : ℝ)^783
        have hw : |(-1788876451/10000000000 : ℝ)|=(1788876451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s1_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (270064693/625000000 : ℝ)*x 0 + (2530032309/5000000000 : ℝ)*x 1 + (3692435127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270064693/625000000 : ℝ)^1039 ≤ (32843095475293/100000000000000 : ℝ)^783 := by
    have hnat : (270064693 : ℕ)^1039*100000000000000^783 ≤ 32843095475293^783*625000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270064693 625000000 32843095475293 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530032309/5000000000 : ℝ)^1039 ≤ (8099544248071/20000000000000 : ℝ)^783 := by
    have hnat : (2530032309 : ℕ)^1039*20000000000000^783 ≤ 8099544248071^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530032309 5000000000 8099544248071 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3692435127/10000000000 : ℝ)^1039 ≤ (13329591636029/50000000000000 : ℝ)^783 := by
    have hnat : (3692435127 : ℕ)^1039*50000000000000^783 ≤ 13329591636029^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692435127 10000000000 13329591636029 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270064693/625000000 : ℝ), (2530032309/5000000000 : ℝ), (3692435127/10000000000 : ℝ)] ![(32843095475293/100000000000000 : ℝ), (8099544248071/20000000000000 : ℝ), (13329591636029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270064693/625000000 : ℝ)|^1039 ≤ (32843095475293/100000000000000 : ℝ)^783
        have hw : |(270064693/625000000 : ℝ)|=(270064693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2530032309/5000000000 : ℝ)|^1039 ≤ (8099544248071/20000000000000 : ℝ)^783
        have hw : |(2530032309/5000000000 : ℝ)|=(2530032309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3692435127/10000000000 : ℝ)|^1039 ≤ (13329591636029/50000000000000 : ℝ)^783
        have hw : |(3692435127/10000000000 : ℝ)|=(3692435127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (872/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (159/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (69/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20543/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (872/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (159/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (872/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (159/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (872/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (159/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (872/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (159/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (872/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (159/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (872/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (159/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (159/50000 : ℝ) ^ (8311/2048 : ℝ) ≤ (1464252023/20000000000000000000 : ℝ) := by
    have hpowers : (159/50000 : ℝ)^8311 ≤ (1464252023/20000000000000000000 : ℝ)^2048 := by
      have hnat : (159 : ℕ)^8311*20000000000000000000^2048 ≤ 1464252023^2048*50000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        159 50000 1464252023 20000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (159/50000 : ℝ)) (X := (1464252023/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (872/3125 : ℝ) ^ (8311/2048 : ℝ) ≤ (562932137502015473/100000000000000000000 : ℝ) := by
    have hpowers : (872/3125 : ℝ)^8311 ≤ (562932137502015473/100000000000000000000 : ℝ)^2048 := by
      have hnat : (872 : ℕ)^8311*100000000000000000000^2048 ≤ 562932137502015473^2048*3125^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        872 3125 562932137502015473 100000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (872/3125 : ℝ)) (X := (562932137502015473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000001464252023/10000000000000000000 : ℝ) ≤ (5000000000180411/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (10000000001464252023/10000000000000000000 : ℝ)^2048 ≤ (5000000000180411/5000000000000000 : ℝ)^8311 := by
      have hnat : (10000000001464252023 : ℕ)^2048*5000000000000000^8311 ≤ 5000000000180411^8311*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000001464252023 10000000000000000000 5000000000180411 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000180411/5000000000000000 : ℝ)) (X := (10000000001464252023/10000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25140733036205818897/25000000000000000000 : ℝ) ≤ (1251730308773117/1250000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (25140733036205818897/25000000000000000000 : ℝ)^2048 ≤ (1251730308773117/1250000000000000 : ℝ)^8311 := by
      have hnat : (25140733036205818897 : ℕ)^2048*1250000000000000^8311 ≤ 1251730308773117^8311*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25140733036205818897 25000000000000000000 1251730308773117 1250000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251730308773117/1250000000000000 : ℝ)) (X := (25140733036205818897/25000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50562932137502015473/50000000000000000000 : ℝ) ≤ (200553698800181/200000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (50562932137502015473/50000000000000000000 : ℝ)^2048 ≤ (200553698800181/200000000000000 : ℝ)^8311 := by
      have hnat : (50562932137502015473 : ℕ)^2048*200000000000000^8311 ≤ 200553698800181^8311*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50562932137502015473 50000000000000000000 200553698800181 200000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200553698800181/200000000000000 : ℝ)) (X := (50562932137502015473/50000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1464252023/20000000000000000000 : ℝ) ≤ ((68962799049786374797/68965000000000000000 : ℝ)+2*(6921234912057/1379300000000000 : ℝ)*(159/50000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (68962799049786374797/68965000000000000000 : ℝ)+2*(6921234912057/1379300000000000 : ℝ)*(159/50000 : ℝ)=(5000000000180411/5000000000000000 : ℝ) by norm_num, show 1+2*(1464252023/20000000000000000000 : ℝ)=(10000000001464252023/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(562932137502015473/100000000000000000000 : ℝ)+(1464252023/20000000000000000000 : ℝ) ≤ ((68962799049786374797/68965000000000000000 : ℝ)+(6921234912057/1379300000000000 : ℝ)*((872/3125 : ℝ)+(159/50000 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (68962799049786374797/68965000000000000000 : ℝ)+(6921234912057/1379300000000000 : ℝ)*((872/3125 : ℝ)+(159/50000 : ℝ))=(1251730308773117/1250000000000000 : ℝ) by norm_num, show 1+(562932137502015473/100000000000000000000 : ℝ)+(1464252023/20000000000000000000 : ℝ)=(25140733036205818897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(562932137502015473/100000000000000000000 : ℝ) ≤ ((68962799049786374797/68965000000000000000 : ℝ)+2*(6921234912057/1379300000000000 : ℝ)*(872/3125 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (68962799049786374797/68965000000000000000 : ℝ)+2*(6921234912057/1379300000000000 : ℝ)*(872/3125 : ℝ)=(200553698800181/200000000000000 : ℝ) by norm_num, show 1+2*(562932137502015473/100000000000000000000 : ℝ)=(50562932137502015473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68962799049786374797/68965000000000000000 : ℝ)*(X 1 0+X 2 0)+(6921234912057/1379300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (159/50000 : ℝ)) (hi := (872/3125 : ℝ)) (c := (68962799049786374797/68965000000000000000 : ℝ)) (alpha := (6921234912057/1379300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68962799049786374797/68965000000000000000 : ℝ)*(X 0 1+X 2 1)+(6921234912057/1379300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (159/50000 : ℝ)) (hi := (872/3125 : ℝ)) (c := (68962799049786374797/68965000000000000000 : ℝ)) (alpha := (6921234912057/1379300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68962799049786374797/68965000000000000000 : ℝ)*(X 0 2+X 1 2)+(6921234912057/1379300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (159/50000 : ℝ)) (hi := (872/3125 : ℝ)) (c := (68962799049786374797/68965000000000000000 : ℝ)) (alpha := (6921234912057/1379300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1052715889/5000000000 : ℝ)*X 0 0+(2853858241/5000000000 : ℝ)*X 0 1+(4997405267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420390919/10000000000 : ℝ)*X 1 0+(-2489208517/10000000000 : ℝ)*X 1 1+(2498702537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420392401/10000000000 : ℝ)*X 2 0+(4997403707/10000000000 : ℝ)*X 2 1+(-1244604161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319375717/10000000000 : ℝ)*X 0 0+(229541917/625000000 : ℝ)*X 0 1+(634930297/1250000000 : ℝ)*X 0 2+(4319375717/10000000000 : ℝ)*X 1 0+(229541917/625000000 : ℝ)*X 1 1+(634930297/1250000000 : ℝ)*X 1 2+(4319375717/10000000000 : ℝ)*X 2 0+(229541917/625000000 : ℝ)*X 2 1+(634930297/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2106270713/10000000000 : ℝ)*X 0 0+(5007189911/10000000000 : ℝ)*X 0 1+(5697736491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309622763/2500000000 : ℝ)*X 1 0+(-1788876723/10000000000 : ℝ)*X 1 1+(356108517/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1047698217/2000000000 : ℝ)*X 2 0+(227909457/400000000 : ℝ)*X 2 1+(-1788876451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((270064693/625000000 : ℝ)*X 0 0+(2530032309/5000000000 : ℝ)*X 0 1+(3692435127/10000000000 : ℝ)*X 0 2+(270064693/625000000 : ℝ)*X 1 0+(2530032309/5000000000 : ℝ)*X 1 1+(3692435127/10000000000 : ℝ)*X 1 2+(270064693/625000000 : ℝ)*X 2 0+(2530032309/5000000000 : ℝ)*X 2 1+(3692435127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (550218161228288727934199781/344825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6939053/6250000000000 : ℝ)*(base1) + (81655129/50000000000000 : ℝ)*(base19) + (464160567/100000000000000 : ℝ)*(base23) + (50235459/50000000000000 : ℝ)*(base37) + (26716669/50000000000000 : ℝ)*(lower2) + (211867973747291/20000000000000 : ℝ)*(major0) + (211867973747291/20000000000000 : ℝ)*(major1) + (211867973747291/20000000000000 : ℝ)*(major2) + (1407832997335957/100000000000000 : ℝ)*(sp0) + (14078327093317/1000000000000 : ℝ)*(sp1) + (703916420434911/50000000000000 : ℝ)*(sp2) + (177711541939649/25000000000000 : ℝ)*(sp3) + (5233991/1250000000000 : ℝ)*(sp4) + (432388431/100000000000000 : ℝ)*(sp5) + (710846379254363/100000000000000 : ℝ)*(f.failure) + (1407833305030389/100000000000000 : ℝ)*(f.sum) + (11909333151191/13793000000000000000000000000 : ℝ)*base66 + (1232801577294974927/1379300000000000000000000000000000 : ℝ)*base67 + (438044138164725073/1379300000000000000000000000000000 : ℝ)*base70 + (1567510079520425073/1379300000000000000000000000000000 : ℝ)*base72 + (1653833125669/689650000000000000000000000 : ℝ)*base73 + (3209586155581625073/1379300000000000000000000000000000 : ℝ)*base76 + (8985897075683425073/1379300000000000000000000000000000 : ℝ)*base78 + (629119354745025073/1379300000000000000000000000000000 : ℝ)*base80 + (35242309539871/13793000000000000000000000000 : ℝ)*base81 + (18930181/2500000000000000000000 : ℝ)*base89 + (18930181/2500000000000000000000 : ℝ)*base91 + (18930181/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15649972500123810264043207023/1724125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26675857/25000000000000 : ℝ)*(base1) + (1005704079/50000000000000 : ℝ)*(base19) + (2039292937/100000000000000 : ℝ)*(base23) + (100829181/50000000000000 : ℝ)*(upper3) + (102810309/50000000000000 : ℝ)*(upper5) + (1089660427557647/100000000000000 : ℝ)*(major0) + (1089660427557647/100000000000000 : ℝ)*(major1) + (1089660427557647/100000000000000 : ℝ)*(major2) + (4078010989/50000000000000 : ℝ)*(sp1) + (108703537/1250000000000 : ℝ)*(sp2) + (181016043202043/12500000000000 : ℝ)*(sp4) + (72405903574139/5000000000000 : ℝ)*(sp5) + (1448117503337019/100000000000000 : ℝ)*(sp6) + (731192206930541/100000000000000 : ℝ)*(sp7) + (731192313633969/100000000000000 : ℝ)*(f.failure) + (362032059728229/25000000000000 : ℝ)*(f.sum) + (97597425792639/68965000000000000000000000000 : ℝ)*base65 + (21223421154586372659/6896500000000000000000000000000000 : ℝ)*base67 + (2335846336597872659/6896500000000000000000000000000000 : ℝ)*base69 + (33422493605684372659/6896500000000000000000000000000000 : ℝ)*base71 + (94487625943899/68965000000000000000000000000 : ℝ)*base73 + (17181916866095872659/6896500000000000000000000000000000 : ℝ)*base75 + (26566957208799872659/6896500000000000000000000000000000 : ℝ)*base77 + (12422150025875127341/6896500000000000000000000000000000 : ℝ)*base80 + (150303589556491/68965000000000000000000000000 : ℝ)*base82 + (12986897/2500000000000000000000 : ℝ)*base90 + (12986897/2500000000000000000000 : ℝ)*base92 + (12986897/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1119_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (872/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (159/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (69/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20543/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1119_s2_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079954831/5000000000 : ℝ)*x 0 + (5515253847/10000000000 : ℝ)*x 1 + (2577625209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079954831/5000000000 : ℝ)^1039 ≤ (13086721944151/100000000000000 : ℝ)^783 := by
    have hnat : (1079954831 : ℕ)^1039*100000000000000^783 ≤ 13086721944151^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079954831 5000000000 13086721944151 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5515253847/10000000000 : ℝ)^1039 ≤ (22700789596683/50000000000000 : ℝ)^783 := by
    have hnat : (5515253847 : ℕ)^1039*50000000000000^783 ≤ 22700789596683^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515253847 10000000000 22700789596683 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2577625209/5000000000 : ℝ)^1039 ≤ (41511698846457/100000000000000 : ℝ)^783 := by
    have hnat : (2577625209 : ℕ)^1039*100000000000000^783 ≤ 41511698846457^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577625209 5000000000 41511698846457 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079954831/5000000000 : ℝ), (5515253847/10000000000 : ℝ), (2577625209/5000000000 : ℝ)] ![(13086721944151/100000000000000 : ℝ), (22700789596683/50000000000000 : ℝ), (41511698846457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079954831/5000000000 : ℝ)|^1039 ≤ (13086721944151/100000000000000 : ℝ)^783
        have hw : |(-1079954831/5000000000 : ℝ)|=(1079954831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5515253847/10000000000 : ℝ)|^1039 ≤ (22700789596683/50000000000000 : ℝ)^783
        have hw : |(5515253847/10000000000 : ℝ)|=(5515253847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2577625209/5000000000 : ℝ)|^1039 ≤ (41511698846457/100000000000000 : ℝ)^783
        have hw : |(2577625209/5000000000 : ℝ)|=(2577625209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s2_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2687431427/5000000000 : ℝ)*x 0 + (-2347246493/10000000000 : ℝ)*x 1 + (5155251861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687431427/5000000000 : ℝ)^1039 ≤ (10968611393849/25000000000000 : ℝ)^783 := by
    have hnat : (2687431427 : ℕ)^1039*25000000000000^783 ≤ 10968611393849^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687431427 5000000000 10968611393849 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2347246493/10000000000 : ℝ)^1039 ≤ (2922768030167/20000000000000 : ℝ)^783 := by
    have hnat : (2347246493 : ℕ)^1039*20000000000000^783 ≤ 2922768030167^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347246493 10000000000 2922768030167 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5155251861/10000000000 : ℝ)^1039 ≤ (41511714264913/100000000000000 : ℝ)^783 := by
    have hnat : (5155251861 : ℕ)^1039*100000000000000^783 ≤ 41511714264913^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155251861 10000000000 41511714264913 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687431427/5000000000 : ℝ), (-2347246493/10000000000 : ℝ), (5155251861/10000000000 : ℝ)] ![(10968611393849/25000000000000 : ℝ), (2922768030167/20000000000000 : ℝ), (41511714264913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687431427/5000000000 : ℝ)|^1039 ≤ (10968611393849/25000000000000 : ℝ)^783
        have hw : |(2687431427/5000000000 : ℝ)|=(2687431427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2347246493/10000000000 : ℝ)|^1039 ≤ (2922768030167/20000000000000 : ℝ)^783
        have hw : |(-2347246493/10000000000 : ℝ)|=(2347246493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5155251861/10000000000 : ℝ)|^1039 ≤ (41511714264913/100000000000000 : ℝ)^783
        have hw : |(5155251861/10000000000 : ℝ)|=(5155251861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s2_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2687431391/5000000000 : ℝ)*x 0 + (5155251917/10000000000 : ℝ)*x 1 + (-1173623257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687431391/5000000000 : ℝ)^1039 ≤ (43874444795511/100000000000000 : ℝ)^783 := by
    have hnat : (2687431391 : ℕ)^1039*100000000000000^783 ≤ 43874444795511^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687431391 5000000000 43874444795511 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5155251917/10000000000 : ℝ)^1039 ≤ (41511714863273/100000000000000 : ℝ)^783 := by
    have hnat : (5155251917 : ℕ)^1039*100000000000000^783 ≤ 41511714863273^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155251917 10000000000 41511714863273 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1173623257/5000000000 : ℝ)^1039 ≤ (14613840324327/100000000000000 : ℝ)^783 := by
    have hnat : (1173623257 : ℕ)^1039*100000000000000^783 ≤ 14613840324327^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173623257 5000000000 14613840324327 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687431391/5000000000 : ℝ), (5155251917/10000000000 : ℝ), (-1173623257/5000000000 : ℝ)] ![(43874444795511/100000000000000 : ℝ), (41511714863273/100000000000000 : ℝ), (14613840324327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687431391/5000000000 : ℝ)|^1039 ≤ (43874444795511/100000000000000 : ℝ)^783
        have hw : |(2687431391/5000000000 : ℝ)|=(2687431391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5155251917/10000000000 : ℝ)|^1039 ≤ (41511714863273/100000000000000 : ℝ)^783
        have hw : |(5155251917/10000000000 : ℝ)|=(5155251917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1173623257/5000000000 : ℝ)|^1039 ≤ (14613840324327/100000000000000 : ℝ)^783
        have hw : |(-1173623257/5000000000 : ℝ)|=(1173623257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s2_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (871338577/2000000000 : ℝ)*x 0 + (501841423/1250000000 : ℝ)*x 1 + (2363857883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871338577/2000000000 : ℝ)^1039 ≤ (6640643382811/20000000000000 : ℝ)^783 := by
    have hnat : (871338577 : ℕ)^1039*20000000000000^783 ≤ 6640643382811^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871338577 2000000000 6640643382811 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501841423/1250000000 : ℝ)^1039 ≤ (595803315297/2000000000000 : ℝ)^783 := by
    have hnat : (501841423 : ℕ)^1039*2000000000000^783 ≤ 595803315297^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501841423 1250000000 595803315297 2000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363857883/5000000000 : ℝ)^1039 ≤ (37006617298059/100000000000000 : ℝ)^783 := by
    have hnat : (2363857883 : ℕ)^1039*100000000000000^783 ≤ 37006617298059^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363857883 5000000000 37006617298059 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871338577/2000000000 : ℝ), (501841423/1250000000 : ℝ), (2363857883/5000000000 : ℝ)] ![(6640643382811/20000000000000 : ℝ), (595803315297/2000000000000 : ℝ), (37006617298059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871338577/2000000000 : ℝ)|^1039 ≤ (6640643382811/20000000000000 : ℝ)^783
        have hw : |(871338577/2000000000 : ℝ)|=(871338577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501841423/1250000000 : ℝ)|^1039 ≤ (595803315297/2000000000000 : ℝ)^783
        have hw : |(501841423/1250000000 : ℝ)|=(501841423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2363857883/5000000000 : ℝ)|^1039 ≤ (37006617298059/100000000000000 : ℝ)^783
        have hw : |(2363857883/5000000000 : ℝ)|=(2363857883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s2_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-270002357/1250000000 : ℝ)*x 0 + (1031554693/2000000000 : ℝ)*x 1 + (5512705113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270002357/1250000000 : ℝ)^1039 ≤ (2617519971413/20000000000000 : ℝ)^783 := by
    have hnat : (270002357 : ℕ)^1039*20000000000000^783 ≤ 2617519971413^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270002357 1250000000 2617519971413 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031554693/2000000000 : ℝ)^1039 ≤ (20769329880139/50000000000000 : ℝ)^783 := by
    have hnat : (1031554693 : ℕ)^1039*50000000000000^783 ≤ 20769329880139^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031554693 2000000000 20769329880139 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5512705113/10000000000 : ℝ)^1039 ≤ (11343435091509/25000000000000 : ℝ)^783 := by
    have hnat : (5512705113 : ℕ)^1039*25000000000000^783 ≤ 11343435091509^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512705113 10000000000 11343435091509 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270002357/1250000000 : ℝ), (1031554693/2000000000 : ℝ), (5512705113/10000000000 : ℝ)] ![(2617519971413/20000000000000 : ℝ), (20769329880139/50000000000000 : ℝ), (11343435091509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270002357/1250000000 : ℝ)|^1039 ≤ (2617519971413/20000000000000 : ℝ)^783
        have hw : |(-270002357/1250000000 : ℝ)|=(270002357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031554693/2000000000 : ℝ)|^1039 ≤ (20769329880139/50000000000000 : ℝ)^783
        have hw : |(1031554693/2000000000 : ℝ)|=(1031554693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5512705113/10000000000 : ℝ)|^1039 ≤ (11343435091509/25000000000000 : ℝ)^783
        have hw : |(5512705113/10000000000 : ℝ)|=(5512705113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s2_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5283661457/10000000000 : ℝ)*x 0 + (-1989791681/10000000000 : ℝ)*x 1 + (689088201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283661457/10000000000 : ℝ)^1039 ≤ (21444663442219/50000000000000 : ℝ)^783 := by
    have hnat : (5283661457 : ℕ)^1039*50000000000000^783 ≤ 21444663442219^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283661457 10000000000 21444663442219 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989791681/10000000000 : ℝ)^1039 ≤ (11736927337043/100000000000000 : ℝ)^783 := by
    have hnat : (1989791681 : ℕ)^1039*100000000000000^783 ≤ 11736927337043^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989791681 10000000000 11736927337043 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689088201/1250000000 : ℝ)^1039 ≤ (283585911077/625000000000 : ℝ)^783 := by
    have hnat : (689088201 : ℕ)^1039*625000000000^783 ≤ 283585911077^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689088201 1250000000 283585911077 625000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283661457/10000000000 : ℝ), (-1989791681/10000000000 : ℝ), (689088201/1250000000 : ℝ)] ![(21444663442219/50000000000000 : ℝ), (11736927337043/100000000000000 : ℝ), (283585911077/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283661457/10000000000 : ℝ)|^1039 ≤ (21444663442219/50000000000000 : ℝ)^783
        have hw : |(5283661457/10000000000 : ℝ)|=(5283661457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989791681/10000000000 : ℝ)|^1039 ≤ (11736927337043/100000000000000 : ℝ)^783
        have hw : |(-1989791681/10000000000 : ℝ)|=(1989791681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(689088201/1250000000 : ℝ)|^1039 ≤ (283585911077/625000000000 : ℝ)^783
        have hw : |(689088201/1250000000 : ℝ)|=(689088201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s2_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1056732069/2000000000 : ℝ)*x 0 + (5512705523/10000000000 : ℝ)*x 1 + (-1989793329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056732069/2000000000 : ℝ)^1039 ≤ (10722328726689/25000000000000 : ℝ)^783 := by
    have hnat : (1056732069 : ℕ)^1039*25000000000000^783 ≤ 10722328726689^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056732069 2000000000 10722328726689 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512705523/10000000000 : ℝ)^1039 ≤ (708964763187/1562500000000 : ℝ)^783 := by
    have hnat : (5512705523 : ℕ)^1039*1562500000000^783 ≤ 708964763187^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512705523 10000000000 708964763187 1562500000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989793329/10000000000 : ℝ)^1039 ≤ (11736940236097/100000000000000 : ℝ)^783 := by
    have hnat : (1989793329 : ℕ)^1039*100000000000000^783 ≤ 11736940236097^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989793329 10000000000 11736940236097 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056732069/2000000000 : ℝ), (5512705523/10000000000 : ℝ), (-1989793329/10000000000 : ℝ)] ![(10722328726689/25000000000000 : ℝ), (708964763187/1562500000000 : ℝ), (11736940236097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056732069/2000000000 : ℝ)|^1039 ≤ (10722328726689/25000000000000 : ℝ)^783
        have hw : |(1056732069/2000000000 : ℝ)|=(1056732069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512705523/10000000000 : ℝ)|^1039 ≤ (708964763187/1562500000000 : ℝ)^783
        have hw : |(5512705523/10000000000 : ℝ)|=(5512705523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989793329/10000000000 : ℝ)|^1039 ≤ (11736940236097/100000000000000 : ℝ)^783
        have hw : |(-1989793329/10000000000 : ℝ)|=(1989793329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s2_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4356908847/10000000000 : ℝ)*x 0 + (944543983/2000000000 : ℝ)*x 1 + (16079111/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356908847/10000000000 : ℝ)^1039 ≤ (6641080188069/20000000000000 : ℝ)^783 := by
    have hnat : (4356908847 : ℕ)^1039*20000000000000^783 ≤ 6641080188069^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356908847 10000000000 6641080188069 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (944543983/2000000000 : ℝ)^1039 ≤ (18477367676681/50000000000000 : ℝ)^783 := by
    have hnat : (944543983 : ℕ)^1039*50000000000000^783 ≤ 18477367676681^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944543983 2000000000 18477367676681 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16079111/40000000 : ℝ)^1039 ≤ (7459965919781/25000000000000 : ℝ)^783 := by
    have hnat : (16079111 : ℕ)^1039*25000000000000^783 ≤ 7459965919781^783*40000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16079111 40000000 7459965919781 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356908847/10000000000 : ℝ), (944543983/2000000000 : ℝ), (16079111/40000000 : ℝ)] ![(6641080188069/20000000000000 : ℝ), (18477367676681/50000000000000 : ℝ), (7459965919781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356908847/10000000000 : ℝ)|^1039 ≤ (6641080188069/20000000000000 : ℝ)^783
        have hw : |(4356908847/10000000000 : ℝ)|=(4356908847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(944543983/2000000000 : ℝ)|^1039 ≤ (18477367676681/50000000000000 : ℝ)^783
        have hw : |(944543983/2000000000 : ℝ)|=(944543983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16079111/40000000 : ℝ)|^1039 ≤ (7459965919781/25000000000000 : ℝ)^783
        have hw : |(16079111/40000000 : ℝ)|=(16079111/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20543/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (1793/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4143/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20543/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (69/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20543/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (69/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20543/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (69/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20543/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (69/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20543/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (69/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20543/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (69/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (69/1250 : ℝ) ^ (8311/2048 : ℝ) ≤ (98076758640217/12500000000000000000 : ℝ) := by
    have hpowers : (69/1250 : ℝ)^8311 ≤ (98076758640217/12500000000000000000 : ℝ)^2048 := by
      have hnat : (69 : ℕ)^8311*12500000000000000000^2048 ≤ 98076758640217^2048*1250^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69 1250 98076758640217 12500000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69/1250 : ℝ)) (X := (98076758640217/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20543/100000 : ℝ) ^ (8311/2048 : ℝ) ≤ (40612290592927209/25000000000000000000 : ℝ) := by
    have hpowers : (20543/100000 : ℝ)^8311 ≤ (40612290592927209/25000000000000000000 : ℝ)^2048 := by
      have hnat : (20543 : ℕ)^8311*25000000000000000000^2048 ≤ 40612290592927209^2048*100000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20543 100000 40612290592927209 25000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20543/100000 : ℝ)) (X := (40612290592927209/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250098076758640217/6250000000000000000 : ℝ) ≤ (5000019334377483/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (6250098076758640217/6250000000000000000 : ℝ)^2048 ≤ (5000019334377483/5000000000000000 : ℝ)^8311 := by
      have hnat : (6250098076758640217 : ℕ)^2048*5000000000000000^8311 ≤ 5000019334377483^8311*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250098076758640217 6250000000000000000 5000019334377483 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000019334377483/5000000000000000 : ℝ)) (X := (6250098076758640217/6250000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25040808444110207643/25000000000000000000 : ℝ) ≤ (500200997086867/500000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (25040808444110207643/25000000000000000000 : ℝ)^2048 ≤ (500200997086867/500000000000000 : ℝ)^8311 := by
      have hnat : (25040808444110207643 : ℕ)^2048*500000000000000^8311 ≤ 500200997086867^8311*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25040808444110207643 25000000000000000000 500200997086867 500000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500200997086867/500000000000000 : ℝ)) (X := (25040808444110207643/25000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12540612290592927209/12500000000000000000 : ℝ) ≤ (5004000607359857/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (12540612290592927209/12500000000000000000 : ℝ)^2048 ≤ (5004000607359857/5000000000000000 : ℝ)^8311 := by
      have hnat : (12540612290592927209 : ℕ)^2048*5000000000000000^8311 ≤ 5004000607359857^8311*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12540612290592927209 12500000000000000000 5004000607359857 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004000607359857/5000000000000000 : ℝ)) (X := (12540612290592927209/12500000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(98076758640217/12500000000000000000 : ℝ) ≤ ((75093313833490222629/75115000000000000000 : ℝ)+2*(1990636491187/751150000000000 : ℝ)*(69/1250 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (75093313833490222629/75115000000000000000 : ℝ)+2*(1990636491187/751150000000000 : ℝ)*(69/1250 : ℝ)=(5000019334377483/5000000000000000 : ℝ) by norm_num, show 1+2*(98076758640217/12500000000000000000 : ℝ)=(6250098076758640217/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40612290592927209/25000000000000000000 : ℝ)+(98076758640217/12500000000000000000 : ℝ) ≤ ((75093313833490222629/75115000000000000000 : ℝ)+(1990636491187/751150000000000 : ℝ)*((20543/100000 : ℝ)+(69/1250 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (75093313833490222629/75115000000000000000 : ℝ)+(1990636491187/751150000000000 : ℝ)*((20543/100000 : ℝ)+(69/1250 : ℝ))=(500200997086867/500000000000000 : ℝ) by norm_num, show 1+(40612290592927209/25000000000000000000 : ℝ)+(98076758640217/12500000000000000000 : ℝ)=(25040808444110207643/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40612290592927209/25000000000000000000 : ℝ) ≤ ((75093313833490222629/75115000000000000000 : ℝ)+2*(1990636491187/751150000000000 : ℝ)*(20543/100000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (75093313833490222629/75115000000000000000 : ℝ)+2*(1990636491187/751150000000000 : ℝ)*(20543/100000 : ℝ)=(5004000607359857/5000000000000000 : ℝ) by norm_num, show 1+2*(40612290592927209/25000000000000000000 : ℝ)=(12540612290592927209/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (75093313833490222629/75115000000000000000 : ℝ)*(X 1 0+X 2 0)+(1990636491187/751150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (69/1250 : ℝ)) (hi := (20543/100000 : ℝ)) (c := (75093313833490222629/75115000000000000000 : ℝ)) (alpha := (1990636491187/751150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (75093313833490222629/75115000000000000000 : ℝ)*(X 0 1+X 2 1)+(1990636491187/751150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (69/1250 : ℝ)) (hi := (20543/100000 : ℝ)) (c := (75093313833490222629/75115000000000000000 : ℝ)) (alpha := (1990636491187/751150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (75093313833490222629/75115000000000000000 : ℝ)*(X 0 2+X 1 2)+(1990636491187/751150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (69/1250 : ℝ)) (hi := (20543/100000 : ℝ)) (c := (75093313833490222629/75115000000000000000 : ℝ)) (alpha := (1990636491187/751150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079954831/5000000000 : ℝ)*X 0 0+(5515253847/10000000000 : ℝ)*X 0 1+(2577625209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687431427/5000000000 : ℝ)*X 1 0+(-2347246493/10000000000 : ℝ)*X 1 1+(5155251861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687431391/5000000000 : ℝ)*X 2 0+(5155251917/10000000000 : ℝ)*X 2 1+(-1173623257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871338577/2000000000 : ℝ)*X 0 0+(501841423/1250000000 : ℝ)*X 0 1+(2363857883/5000000000 : ℝ)*X 0 2+(871338577/2000000000 : ℝ)*X 1 0+(501841423/1250000000 : ℝ)*X 1 1+(2363857883/5000000000 : ℝ)*X 1 2+(871338577/2000000000 : ℝ)*X 2 0+(501841423/1250000000 : ℝ)*X 2 1+(2363857883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-270002357/1250000000 : ℝ)*X 0 0+(1031554693/2000000000 : ℝ)*X 0 1+(5512705113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283661457/10000000000 : ℝ)*X 1 0+(-1989791681/10000000000 : ℝ)*X 1 1+(689088201/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056732069/2000000000 : ℝ)*X 2 0+(5512705523/10000000000 : ℝ)*X 2 1+(-1989793329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356908847/10000000000 : ℝ)*X 0 0+(944543983/2000000000 : ℝ)*X 0 1+(16079111/40000000 : ℝ)*X 0 2+(4356908847/10000000000 : ℝ)*X 1 0+(944543983/2000000000 : ℝ)*X 1 1+(16079111/40000000 : ℝ)*X 1 2+(4356908847/10000000000 : ℝ)*X 2 0+(944543983/2000000000 : ℝ)*X 2 1+(16079111/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16688982659662507792989426891/3755750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175657/2000000000000 : ℝ)*(base29) + (47984619/50000000000000 : ℝ)*(upper2) + (414703/1000000000000 : ℝ)*(upper3) + (75969283/100000000000000 : ℝ)*(upper4) + (9707053/20000000000000 : ℝ)*(upper5) + (522541247567357/25000000000000 : ℝ)*(major0) + (2090164999052279/100000000000000 : ℝ)*(major1) + (2090164999052279/100000000000000 : ℝ)*(major2) + (1388880671514759/50000000000000 : ℝ)*(sp0) + (694442815397777/25000000000000 : ℝ)*(sp1) + (1388885630795553/50000000000000 : ℝ)*(sp2) + (1402557002467207/100000000000000 : ℝ)*(sp3) + (248183611/2500000000000 : ℝ)*(sp4) + (788571993/50000000000000 : ℝ)*(sp7) + (1402558579611193/100000000000000 : ℝ)*(f.failure) + (1388885635186979/50000000000000 : ℝ)*(f.sum) + (153561990635531/75115000000000000000000000000 : ℝ)*base65 + (34081645014961121491/7511500000000000000000000000000000 : ℝ)*base67 + (59589111970218121491/7511500000000000000000000000000000 : ℝ)*base69 + (19463161120721571553/1877875000000000000000000000000000 : ℝ)*base71 + (612556082281299/75115000000000000000000000000 : ℝ)*base73 + (63140695988251578509/7511500000000000000000000000000000 : ℝ)*base76 + (3659500953574071553/1877875000000000000000000000000000 : ℝ)*base77 + (54346624208203421491/7511500000000000000000000000000000 : ℝ)*base79 + (295295024299739/75115000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base88 + (4820391/2500000000000000000000 : ℝ)*base89 + (20179609/2500000000000000000000 : ℝ)*base92 + (20179609/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1874365730860087727228168571/469468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24932221/4000000000000 : ℝ)*(base19) + (239830687/100000000000000 : ℝ)*(base23) + (22026783/10000000000000 : ℝ)*(upper2) + (23588093/100000000000000 : ℝ)*(upper3) + (30158339/25000000000000 : ℝ)*(upper5) + (530003907884067/25000000000000 : ℝ)*(major0) + (530003907884067/25000000000000 : ℝ)*(major1) + (530003907884067/25000000000000 : ℝ)*(major2) + (949190967/100000000000000 : ℝ)*(sp0) + (375485729/3125000000000 : ℝ)*(sp1) + (352180125048569/12500000000000 : ℝ)*(sp4) + (2817429310730667/100000000000000 : ℝ)*(sp5) + (2817441709748833/100000000000000 : ℝ)*(sp6) + (284517836081769/20000000000000 : ℝ)*(sp7) + (284517836081769/20000000000000 : ℝ)*(f.failure) + (2201126523109/78125000000 : ℝ)*(f.sum) + (140399726020403/75115000000000000000000000000 : ℝ)*base66 + (9797666141305852143/1877875000000000000000000000000000 : ℝ)*base67 + (19554131098325352143/1877875000000000000000000000000000 : ℝ)*base69 + (2467248234172602143/1877875000000000000000000000000000 : ℝ)*base71 + (16479169210543/18778750000000000000000000000 : ℝ)*base73 + (473093246159602143/1877875000000000000000000000000000 : ℝ)*base75 + (2793782806007647857/1877875000000000000000000000000000 : ℝ)*base78 + (2019260143257102143/1877875000000000000000000000000000 : ℝ)*base79 + (92376576559463/75115000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1331703/500000000000000000000 : ℝ)*base89 + (1331703/500000000000000000000 : ℝ)*base91 + (1331703/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1119_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20543/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1793/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4143/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1119_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1793/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4143/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1119_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1119_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1119_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1793/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4143/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1119_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

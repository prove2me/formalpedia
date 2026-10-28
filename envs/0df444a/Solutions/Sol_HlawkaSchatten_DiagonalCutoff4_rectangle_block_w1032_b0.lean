-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1032_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:40:13.14952+00:00
-- url     : https://prove2.me/submissions/525af8fe-70c5-47e1-ae1c-12b32d2f1a46

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
theorem support_rectangle_w1032_s0_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1368031037/2500000000 : ℝ)*x 0 + (-2719503631/10000000000 : ℝ)*x 1 + (598820501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1368031037/2500000000 : ℝ)^8225 ≤ (22403242778777/50000000000000 : ℝ)^6177 := by
    have hnat : (1368031037 : ℕ)^8225*50000000000000^6177 ≤ 22403242778777^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368031037 2500000000 22403242778777 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719503631/10000000000 : ℝ)^8225 ≤ (17660103779389/100000000000000 : ℝ)^6177 := by
    have hnat : (2719503631 : ℕ)^8225*100000000000000^6177 ≤ 17660103779389^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719503631 10000000000 17660103779389 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598820501/1250000000 : ℝ)^8225 ≤ (1172919082751/3125000000000 : ℝ)^6177 := by
    have hnat : (598820501 : ℕ)^8225*3125000000000^6177 ≤ 1172919082751^6177*1250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598820501 1250000000 1172919082751 3125000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1368031037/2500000000 : ℝ), (-2719503631/10000000000 : ℝ), (598820501/1250000000 : ℝ)] ![(22403242778777/50000000000000 : ℝ), (17660103779389/100000000000000 : ℝ), (1172919082751/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1368031037/2500000000 : ℝ)|^8225 ≤ (22403242778777/50000000000000 : ℝ)^6177
        have hw : |(1368031037/2500000000 : ℝ)|=(1368031037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2719503631/10000000000 : ℝ)|^8225 ≤ (17660103779389/100000000000000 : ℝ)^6177
        have hw : |(-2719503631/10000000000 : ℝ)|=(2719503631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598820501/1250000000 : ℝ)|^8225 ≤ (1172919082751/3125000000000 : ℝ)^6177
        have hw : |(598820501/1250000000 : ℝ)|=(598820501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s0_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5461108297/10000000000 : ℝ)*x 0 + (23991327/50000000 : ℝ)*x 1 + (-681023351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5461108297/10000000000 : ℝ)^8225 ≤ (5585802574897/12500000000000 : ℝ)^6177 := by
    have hnat : (5461108297 : ℕ)^8225*12500000000000^6177 ≤ 5585802574897^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461108297 10000000000 5585802574897 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23991327/50000000 : ℝ)^8225 ≤ (7522755412863/20000000000000 : ℝ)^6177 := by
    have hnat : (23991327 : ℕ)^8225*20000000000000^6177 ≤ 7522755412863^6177*50000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23991327 50000000 7522755412863 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681023351/2500000000 : ℝ)^8225 ≤ (17699802322299/100000000000000 : ℝ)^6177 := by
    have hnat : (681023351 : ℕ)^8225*100000000000000^6177 ≤ 17699802322299^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681023351 2500000000 17699802322299 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5461108297/10000000000 : ℝ), (23991327/50000000 : ℝ), (-681023351/2500000000 : ℝ)] ![(5585802574897/12500000000000 : ℝ), (7522755412863/20000000000000 : ℝ), (17699802322299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5461108297/10000000000 : ℝ)|^8225 ≤ (5585802574897/12500000000000 : ℝ)^6177
        have hw : |(5461108297/10000000000 : ℝ)|=(5461108297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(23991327/50000000 : ℝ)|^8225 ≤ (7522755412863/20000000000000 : ℝ)^6177
        have hw : |(23991327/50000000 : ℝ)|=(23991327/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-681023351/2500000000 : ℝ)|^8225 ≤ (17699802322299/100000000000000 : ℝ)^6177
        have hw : |(-681023351/2500000000 : ℝ)|=(681023351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s0_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-30196821/156250000 : ℝ)*x 0 + (4800337471/10000000000 : ℝ)*x 1 + (1511247251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30196821/156250000 : ℝ)^8225 ≤ (1400778661351/12500000000000 : ℝ)^6177 := by
    have hnat : (30196821 : ℕ)^8225*12500000000000^6177 ≤ 1400778661351^6177*156250000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30196821 156250000 1400778661351 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4800337471/10000000000 : ℝ)^8225 ≤ (9408851768383/25000000000000 : ℝ)^6177 := by
    have hnat : (4800337471 : ℕ)^8225*25000000000000^6177 ≤ 9408851768383^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800337471 10000000000 9408851768383 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1511247251/2500000000 : ℝ)^8225 ≤ (25579181808373/50000000000000 : ℝ)^6177 := by
    have hnat : (1511247251 : ℕ)^8225*50000000000000^6177 ≤ 25579181808373^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511247251 2500000000 25579181808373 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-30196821/156250000 : ℝ), (4800337471/10000000000 : ℝ), (1511247251/2500000000 : ℝ)] ![(1400778661351/12500000000000 : ℝ), (9408851768383/25000000000000 : ℝ), (25579181808373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-30196821/156250000 : ℝ)|^8225 ≤ (1400778661351/12500000000000 : ℝ)^6177
        have hw : |(-30196821/156250000 : ℝ)|=(30196821/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4800337471/10000000000 : ℝ)|^8225 ≤ (9408851768383/25000000000000 : ℝ)^6177
        have hw : |(4800337471/10000000000 : ℝ)|=(4800337471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1511247251/2500000000 : ℝ)|^8225 ≤ (25579181808373/50000000000000 : ℝ)^6177
        have hw : |(1511247251/2500000000 : ℝ)|=(1511247251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s0_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1291654943/2500000000 : ℝ)*x 0 + (-702868793/5000000000 : ℝ)*x 1 + (1511247211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1291654943/2500000000 : ℝ)^8225 ≤ (10376703302287/25000000000000 : ℝ)^6177 := by
    have hnat : (1291654943 : ℕ)^8225*25000000000000^6177 ≤ 10376703302287^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291654943 2500000000 10376703302287 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702868793/5000000000 : ℝ)^8225 ≤ (7334824965099/100000000000000 : ℝ)^6177 := by
    have hnat : (702868793 : ℕ)^8225*100000000000000^6177 ≤ 7334824965099^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702868793 5000000000 7334824965099 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1511247211/2500000000 : ℝ)^8225 ≤ (51158361813731/100000000000000 : ℝ)^6177 := by
    have hnat : (1511247211 : ℕ)^8225*100000000000000^6177 ≤ 51158361813731^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511247211 2500000000 51158361813731 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1291654943/2500000000 : ℝ), (-702868793/5000000000 : ℝ), (1511247211/2500000000 : ℝ)] ![(10376703302287/25000000000000 : ℝ), (7334824965099/100000000000000 : ℝ), (51158361813731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1291654943/2500000000 : ℝ)|^8225 ≤ (10376703302287/25000000000000 : ℝ)^6177
        have hw : |(1291654943/2500000000 : ℝ)|=(1291654943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-702868793/5000000000 : ℝ)|^8225 ≤ (7334824965099/100000000000000 : ℝ)^6177
        have hw : |(-702868793/5000000000 : ℝ)|=(702868793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1511247211/2500000000 : ℝ)|^8225 ≤ (51158361813731/100000000000000 : ℝ)^6177
        have hw : |(1511247211/2500000000 : ℝ)|=(1511247211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s0_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2583309863/5000000000 : ℝ)*x 0 + (6044988881/10000000000 : ℝ)*x 1 + (-1405737597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583309863/5000000000 : ℝ)^8225 ≤ (1660272508683/4000000000000 : ℝ)^6177 := by
    have hnat : (2583309863 : ℕ)^8225*4000000000000^6177 ≤ 1660272508683^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583309863 5000000000 1660272508683 4000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6044988881/10000000000 : ℝ)^8225 ≤ (25579181115339/50000000000000 : ℝ)^6177 := by
    have hnat : (6044988881 : ℕ)^8225*50000000000000^6177 ≤ 25579181115339^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6044988881 10000000000 25579181115339 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1405737597/10000000000 : ℝ)^8225 ≤ (1833706260381/25000000000000 : ℝ)^6177 := by
    have hnat : (1405737597 : ℕ)^8225*25000000000000^6177 ≤ 1833706260381^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405737597 10000000000 1833706260381 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583309863/5000000000 : ℝ), (6044988881/10000000000 : ℝ), (-1405737597/10000000000 : ℝ)] ![(1660272508683/4000000000000 : ℝ), (25579181115339/50000000000000 : ℝ), (1833706260381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583309863/5000000000 : ℝ)|^8225 ≤ (1660272508683/4000000000000 : ℝ)^6177
        have hw : |(2583309863/5000000000 : ℝ)|=(2583309863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6044988881/10000000000 : ℝ)|^8225 ≤ (25579181115339/50000000000000 : ℝ)^6177
        have hw : |(6044988881/10000000000 : ℝ)|=(6044988881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1405737597/10000000000 : ℝ)|^8225 ≤ (1833706260381/25000000000000 : ℝ)^6177
        have hw : |(-1405737597/10000000000 : ℝ)|=(1405737597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s0_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (844140219/2000000000 : ℝ)*x 0 + (702248209/1250000000 : ℝ)*x 1 + (159754781/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844140219/2000000000 : ℝ)^8225 ≤ (7927201904139/25000000000000 : ℝ)^6177 := by
    have hnat : (844140219 : ℕ)^8225*25000000000000^6177 ≤ 7927201904139^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844140219 2000000000 7927201904139 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702248209/1250000000 : ℝ)^8225 ≤ (46403789682291/100000000000000 : ℝ)^6177 := by
    have hnat : (702248209 : ℕ)^8225*100000000000000^6177 ≤ 46403789682291^6177*1250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702248209 1250000000 46403789682291 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159754781/500000000 : ℝ)^8225 ≤ (5471850671551/25000000000000 : ℝ)^6177 := by
    have hnat : (159754781 : ℕ)^8225*25000000000000^6177 ≤ 5471850671551^6177*500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159754781 500000000 5471850671551 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844140219/2000000000 : ℝ), (702248209/1250000000 : ℝ), (159754781/500000000 : ℝ)] ![(7927201904139/25000000000000 : ℝ), (46403789682291/100000000000000 : ℝ), (5471850671551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844140219/2000000000 : ℝ)|^8225 ≤ (7927201904139/25000000000000 : ℝ)^6177
        have hw : |(844140219/2000000000 : ℝ)|=(844140219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(702248209/1250000000 : ℝ)|^8225 ≤ (46403789682291/100000000000000 : ℝ)^6177
        have hw : |(702248209/1250000000 : ℝ)|=(702248209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159754781/500000000 : ℝ)|^8225 ≤ (5471850671551/25000000000000 : ℝ)^6177
        have hw : |(159754781/500000000 : ℝ)|=(159754781/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14121/50000 : ℝ)*pair X 0 0 := by
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
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpowlo : (0 : ℝ) ^ (257/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^257 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^257*1^64 ≤ 0^64*1^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (257/64 : ℝ) ≤ (1261804747268244153/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^257 ≤ (1261804747268244153/50000000000000000000 : ℝ)^64 := by
      have hnat : (2 : ℕ)^257*50000000000000000000^64 ≤ 1261804747268244153^64*5^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1261804747268244153 50000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1261804747268244153/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^257 := by
      have hnat : (1 : ℕ)^64*1^257 ≤ 1^257*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (51261804747268244153/50000000000000000000 : ℝ) ≤ (2515564466768473/2500000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (51261804747268244153/50000000000000000000 : ℝ)^64 ≤ (2515564466768473/2500000000000000 : ℝ)^257 := by
      have hnat : (51261804747268244153 : ℕ)^64*2500000000000000^257 ≤ 2515564466768473^257*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51261804747268244153 50000000000000000000 2515564466768473 2500000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515564466768473/2500000000000000 : ℝ)) (X := (51261804747268244153/50000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (26261804747268244153/25000000000000000000 : ℝ) ≤ (1265564466768473/1250000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (26261804747268244153/25000000000000000000 : ℝ)^64 ≤ (1265564466768473/1250000000000000 : ℝ)^257 := by
      have hnat : (26261804747268244153 : ℕ)^64*1250000000000000^257 ≤ 1265564466768473^257*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26261804747268244153 25000000000000000000 1265564466768473 1250000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265564466768473/1250000000000000 : ℝ)) (X := (26261804747268244153/25000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15564466768473/1000000000000000 : ℝ)*(0 : ℝ))^(257/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(15564466768473/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1261804747268244153/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15564466768473/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(257/64 : ℝ) := by
    rw [show (1 : ℝ)+(15564466768473/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2515564466768473/2500000000000000 : ℝ) by norm_num, show 1+(1261804747268244153/50000000000000000000 : ℝ)+(0 : ℝ)=(51261804747268244153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1261804747268244153/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15564466768473/1000000000000000 : ℝ)*(2/5 : ℝ))^(257/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(15564466768473/1000000000000000 : ℝ)*(2/5 : ℝ)=(1265564466768473/1250000000000000 : ℝ) by norm_num, show 1+2*(1261804747268244153/50000000000000000000 : ℝ)=(26261804747268244153/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15564466768473/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15564466768473/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15564466768473/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15564466768473/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15564466768473/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15564466768473/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1368031037/2500000000 : ℝ)*X 1 0+(-2719503631/10000000000 : ℝ)*X 1 1+(598820501/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5461108297/10000000000 : ℝ)*X 2 0+(23991327/50000000 : ℝ)*X 2 1+(-681023351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s0_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-30196821/156250000 : ℝ)*X 0 0+(4800337471/10000000000 : ℝ)*X 0 1+(1511247251/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s0_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1291654943/2500000000 : ℝ)*X 1 0+(-702868793/5000000000 : ℝ)*X 1 1+(1511247211/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s0_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2583309863/5000000000 : ℝ)*X 2 0+(6044988881/10000000000 : ℝ)*X 2 1+(-1405737597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s0_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((844140219/2000000000 : ℝ)*X 0 0+(702248209/1250000000 : ℝ)*X 0 1+(159754781/500000000 : ℝ)*X 0 2+(844140219/2000000000 : ℝ)*X 1 0+(702248209/1250000000 : ℝ)*X 1 1+(159754781/500000000 : ℝ)*X 1 2+(844140219/2000000000 : ℝ)*X 2 0+(702248209/1250000000 : ℝ)*X 2 1+(159754781/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s0_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (601946352804135777/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (411177/12500000000000 : ℝ)*(base1) + (128116227/20000000000000 : ℝ)*(base19) + (630438643/100000000000000 : ℝ)*(base23) + (81190813/100000000000000 : ℝ)*(upper3) + (3931319/5000000000000 : ℝ)*(upper5) + (608084013778681/100000000000000 : ℝ)*(major0) + (608084013778681/100000000000000 : ℝ)*(major1) + (608084013778681/100000000000000 : ℝ)*(major2) + (250818199/20000000000000 : ℝ)*(sp0) + (1248557767/100000000000000 : ℝ)*(sp1) + (803437702579489/100000000000000 : ℝ)*(sp2) + (803435804617943/100000000000000 : ℝ)*(sp3) + (803435820293663/100000000000000 : ℝ)*(sp4) + (82546048943671/20000000000000 : ℝ)*(sp5) + (103182562001943/25000000000000 : ℝ)*(f.failure) + (803437699290073/100000000000000 : ℝ)*(f.sum) + (28849254874113/50000000000000000000000000000 : ℝ)*base65 + (488544297575887/100000000000000000000000000000 : ℝ)*base68 + (194765484724113/100000000000000000000000000000 : ℝ)*base69 + (7101607775887/100000000000000000000000000000 : ℝ)*base72 + (177400165525887/50000000000000000000000000000 : ℝ)*base74 + (286745795124113/100000000000000000000000000000 : ℝ)*base75 + (34848895875887/100000000000000000000000000000 : ℝ)*base78 + (76983355975887/100000000000000000000000000000 : ℝ)*base80 + (11445469274113/50000000000000000000000000000 : ℝ)*base81 + (19210067/2500000000000000000000 : ℝ)*base89 + (19210067/2500000000000000000000 : ℝ)*base91 + (19210067/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1032_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1032_s1_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-427920759/2000000000 : ℝ)*x 0 + (5731569643/10000000000 : ℝ)*x 1 + (4978861459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427920759/2000000000 : ℝ)^8225 ≤ (12832275889391/100000000000000 : ℝ)^6177 := by
    have hnat : (427920759 : ℕ)^8225*100000000000000^6177 ≤ 12832275889391^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427920759 2000000000 12832275889391 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5731569643/10000000000 : ℝ)^8225 ≤ (5957150576869/12500000000000 : ℝ)^6177 := by
    have hnat : (5731569643 : ℕ)^8225*12500000000000^6177 ≤ 5957150576869^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5731569643 10000000000 5957150576869 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4978861459/10000000000 : ℝ)^8225 ≤ (19755259743683/50000000000000 : ℝ)^6177 := by
    have hnat : (4978861459 : ℕ)^8225*50000000000000^6177 ≤ 19755259743683^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978861459 10000000000 19755259743683 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427920759/2000000000 : ℝ), (5731569643/10000000000 : ℝ), (4978861459/10000000000 : ℝ)] ![(12832275889391/100000000000000 : ℝ), (5957150576869/12500000000000 : ℝ), (19755259743683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427920759/2000000000 : ℝ)|^8225 ≤ (12832275889391/100000000000000 : ℝ)^6177
        have hw : |(-427920759/2000000000 : ℝ)|=(427920759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5731569643/10000000000 : ℝ)|^8225 ≤ (5957150576869/12500000000000 : ℝ)^6177
        have hw : |(5731569643/10000000000 : ℝ)|=(5731569643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4978861459/10000000000 : ℝ)|^8225 ≤ (19755259743683/50000000000000 : ℝ)^6177
        have hw : |(4978861459/10000000000 : ℝ)|=(4978861459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s1_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (27125941/50000000 : ℝ)*x 0 + (-2548135933/10000000000 : ℝ)*x 1 + (497886177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27125941/50000000 : ℝ)^8225 ≤ (44295475220581/100000000000000 : ℝ)^6177 := by
    have hnat : (27125941 : ℕ)^8225*100000000000000^6177 ≤ 44295475220581^6177*50000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27125941 50000000 44295475220581 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548135933/10000000000 : ℝ)^8225 ≤ (506062562091/3125000000000 : ℝ)^6177 := by
    have hnat : (2548135933 : ℕ)^8225*3125000000000^6177 ≤ 506062562091^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548135933 10000000000 506062562091 3125000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497886177/1000000000 : ℝ)^8225 ≤ (19755261386811/50000000000000 : ℝ)^6177 := by
    have hnat : (497886177 : ℕ)^8225*50000000000000^6177 ≤ 19755261386811^6177*1000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497886177 1000000000 19755261386811 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27125941/50000000 : ℝ), (-2548135933/10000000000 : ℝ), (497886177/1000000000 : ℝ)] ![(44295475220581/100000000000000 : ℝ), (506062562091/3125000000000 : ℝ), (19755261386811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27125941/50000000 : ℝ)|^8225 ≤ (44295475220581/100000000000000 : ℝ)^6177
        have hw : |(27125941/50000000 : ℝ)|=(27125941/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2548135933/10000000000 : ℝ)|^8225 ≤ (506062562091/3125000000000 : ℝ)^6177
        have hw : |(-2548135933/10000000000 : ℝ)|=(2548135933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497886177/1000000000 : ℝ)|^8225 ≤ (19755261386811/50000000000000 : ℝ)^6177
        have hw : |(497886177/1000000000 : ℝ)|=(497886177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s1_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5425188519/10000000000 : ℝ)*x 0 + (4978861353/10000000000 : ℝ)*x 1 + (-509627209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5425188519/10000000000 : ℝ)^8225 ≤ (44295478688697/100000000000000 : ℝ)^6177 := by
    have hnat : (5425188519 : ℕ)^8225*100000000000000^6177 ≤ 44295478688697^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425188519 10000000000 44295478688697 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4978861353/10000000000 : ℝ)^8225 ≤ (9877629591823/25000000000000 : ℝ)^6177 := by
    have hnat : (4978861353 : ℕ)^8225*25000000000000^6177 ≤ 9877629591823^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978861353 10000000000 9877629591823 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509627209/2000000000 : ℝ)^8225 ≤ (16194002934693/100000000000000 : ℝ)^6177 := by
    have hnat : (509627209 : ℕ)^8225*100000000000000^6177 ≤ 16194002934693^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509627209 2000000000 16194002934693 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5425188519/10000000000 : ℝ), (4978861353/10000000000 : ℝ), (-509627209/2000000000 : ℝ)] ![(44295478688697/100000000000000 : ℝ), (9877629591823/25000000000000 : ℝ), (16194002934693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5425188519/10000000000 : ℝ)|^8225 ≤ (44295478688697/100000000000000 : ℝ)^6177
        have hw : |(5425188519/10000000000 : ℝ)|=(5425188519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4978861353/10000000000 : ℝ)|^8225 ≤ (9877629591823/25000000000000 : ℝ)^6177
        have hw : |(4978861353/10000000000 : ℝ)|=(4978861353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-509627209/2000000000 : ℝ)|^8225 ≤ (16194002934693/100000000000000 : ℝ)^6177
        have hw : |(-509627209/2000000000 : ℝ)|=(509627209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s1_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (865345049/2000000000 : ℝ)*x 0 + (3656738633/10000000000 : ℝ)*x 1 + (2560995111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865345049/2000000000 : ℝ)^8225 ≤ (32773816478943/100000000000000 : ℝ)^6177 := by
    have hnat : (865345049 : ℕ)^8225*100000000000000^6177 ≤ 32773816478943^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865345049 2000000000 32773816478943 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3656738633/10000000000 : ℝ)^8225 ≤ (26196097749673/100000000000000 : ℝ)^6177 := by
    have hnat : (3656738633 : ℕ)^8225*100000000000000^6177 ≤ 26196097749673^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3656738633 10000000000 26196097749673 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2560995111/5000000000 : ℝ)^8225 ≤ (41030085768999/100000000000000 : ℝ)^6177 := by
    have hnat : (2560995111 : ℕ)^8225*100000000000000^6177 ≤ 41030085768999^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560995111 5000000000 41030085768999 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865345049/2000000000 : ℝ), (3656738633/10000000000 : ℝ), (2560995111/5000000000 : ℝ)] ![(32773816478943/100000000000000 : ℝ), (26196097749673/100000000000000 : ℝ), (41030085768999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865345049/2000000000 : ℝ)|^8225 ≤ (32773816478943/100000000000000 : ℝ)^6177
        have hw : |(865345049/2000000000 : ℝ)|=(865345049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3656738633/10000000000 : ℝ)|^8225 ≤ (26196097749673/100000000000000 : ℝ)^6177
        have hw : |(3656738633/10000000000 : ℝ)|=(3656738633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2560995111/5000000000 : ℝ)|^8225 ≤ (41030085768999/100000000000000 : ℝ)^6177
        have hw : |(2560995111/5000000000 : ℝ)|=(2560995111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s1_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-133786097/625000000 : ℝ)*x 0 + (249478221/500000000 : ℝ)*x 1 + (2860322643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133786097/625000000 : ℝ)^8225 ≤ (12840052887407/100000000000000 : ℝ)^6177 := by
    have hnat : (133786097 : ℕ)^8225*100000000000000^6177 ≤ 12840052887407^6177*625000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133786097 625000000 12840052887407 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249478221/500000000 : ℝ)^8225 ≤ (4952956896601/12500000000000 : ℝ)^6177 := by
    have hnat : (249478221 : ℕ)^8225*12500000000000^6177 ≤ 4952956896601^6177*500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249478221 500000000 4952956896601 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2860322643/5000000000 : ℝ)^8225 ≤ (47536291926773/100000000000000 : ℝ)^6177 := by
    have hnat : (2860322643 : ℕ)^8225*100000000000000^6177 ≤ 47536291926773^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860322643 5000000000 47536291926773 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133786097/625000000 : ℝ), (249478221/500000000 : ℝ), (2860322643/5000000000 : ℝ)] ![(12840052887407/100000000000000 : ℝ), (4952956896601/12500000000000 : ℝ), (47536291926773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133786097/625000000 : ℝ)|^8225 ≤ (12840052887407/100000000000000 : ℝ)^6177
        have hw : |(-133786097/625000000 : ℝ)|=(133786097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249478221/500000000 : ℝ)|^8225 ≤ (4952956896601/12500000000000 : ℝ)^6177
        have hw : |(249478221/500000000 : ℝ)|=(249478221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2860322643/5000000000 : ℝ)|^8225 ≤ (47536291926773/100000000000000 : ℝ)^6177
        have hw : |(2860322643/5000000000 : ℝ)|=(2860322643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s1_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5233288261/10000000000 : ℝ)*x 0 + (-903175529/5000000000 : ℝ)*x 1 + (5720646277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233288261/10000000000 : ℝ)^8225 ≤ (8444300466913/20000000000000 : ℝ)^6177 := by
    have hnat : (5233288261 : ℕ)^8225*20000000000000^6177 ≤ 8444300466913^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233288261 10000000000 8444300466913 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903175529/5000000000 : ℝ)^8225 ≤ (10242194768549/100000000000000 : ℝ)^6177 := by
    have hnat : (903175529 : ℕ)^8225*100000000000000^6177 ≤ 10242194768549^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903175529 5000000000 10242194768549 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5720646277/10000000000 : ℝ)^8225 ≤ (5942037861483/12500000000000 : ℝ)^6177 := by
    have hnat : (5720646277 : ℕ)^8225*12500000000000^6177 ≤ 5942037861483^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720646277 10000000000 5942037861483 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5233288261/10000000000 : ℝ), (-903175529/5000000000 : ℝ), (5720646277/10000000000 : ℝ)] ![(8444300466913/20000000000000 : ℝ), (10242194768549/100000000000000 : ℝ), (5942037861483/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5233288261/10000000000 : ℝ)|^8225 ≤ (8444300466913/20000000000000 : ℝ)^6177
        have hw : |(5233288261/10000000000 : ℝ)|=(5233288261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-903175529/5000000000 : ℝ)|^8225 ≤ (10242194768549/100000000000000 : ℝ)^6177
        have hw : |(-903175529/5000000000 : ℝ)|=(903175529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5720646277/10000000000 : ℝ)|^8225 ≤ (5942037861483/12500000000000 : ℝ)^6177
        have hw : |(5720646277/10000000000 : ℝ)|=(5720646277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s1_6 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (523328643/1000000000 : ℝ)*x 0 + (2860324143/5000000000 : ℝ)*x 1 + (-903175359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523328643/1000000000 : ℝ)^8225 ≤ (42221482664507/100000000000000 : ℝ)^6177 := by
    have hnat : (523328643 : ℕ)^8225*100000000000000^6177 ≤ 42221482664507^6177*1000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523328643 1000000000 42221482664507 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2860324143/5000000000 : ℝ)^8225 ≤ (9507265024159/20000000000000 : ℝ)^6177 := by
    have hnat : (2860324143 : ℕ)^8225*20000000000000^6177 ≤ 9507265024159^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860324143 5000000000 9507265024159 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903175359/5000000000 : ℝ)^8225 ≤ (160034253149/1562500000000 : ℝ)^6177 := by
    have hnat : (903175359 : ℕ)^8225*1562500000000^6177 ≤ 160034253149^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903175359 5000000000 160034253149 1562500000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523328643/1000000000 : ℝ), (2860324143/5000000000 : ℝ), (-903175359/5000000000 : ℝ)] ![(42221482664507/100000000000000 : ℝ), (9507265024159/20000000000000 : ℝ), (160034253149/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523328643/1000000000 : ℝ)|^8225 ≤ (42221482664507/100000000000000 : ℝ)^6177
        have hw : |(523328643/1000000000 : ℝ)|=(523328643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2860324143/5000000000 : ℝ)|^8225 ≤ (9507265024159/20000000000000 : ℝ)^6177
        have hw : |(2860324143/5000000000 : ℝ)|=(2860324143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-903175359/5000000000 : ℝ)|^8225 ≤ (160034253149/1562500000000 : ℝ)^6177
        have hw : |(-903175359/5000000000 : ℝ)|=(903175359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s1_7 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4328617987/10000000000 : ℝ)*x 0 + (1020230429/2000000000 : ℝ)*x 1 + (735600437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328617987/10000000000 : ℝ)^8225 ≤ (8198227092143/25000000000000 : ℝ)^6177 := by
    have hnat : (4328617987 : ℕ)^8225*25000000000000^6177 ≤ 8198227092143^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328617987 10000000000 8198227092143 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020230429/2000000000 : ℝ)^8225 ≤ (5100995804901/12500000000000 : ℝ)^6177 := by
    have hnat : (1020230429 : ℕ)^8225*12500000000000^6177 ≤ 5100995804901^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020230429 2000000000 5100995804901 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735600437/2000000000 : ℝ)^8225 ≤ (5279825034929/20000000000000 : ℝ)^6177 := by
    have hnat : (735600437 : ℕ)^8225*20000000000000^6177 ≤ 5279825034929^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735600437 2000000000 5279825034929 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328617987/10000000000 : ℝ), (1020230429/2000000000 : ℝ), (735600437/2000000000 : ℝ)] ![(8198227092143/25000000000000 : ℝ), (5100995804901/12500000000000 : ℝ), (5279825034929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328617987/10000000000 : ℝ)|^8225 ≤ (8198227092143/25000000000000 : ℝ)^6177
        have hw : |(4328617987/10000000000 : ℝ)|=(4328617987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1020230429/2000000000 : ℝ)|^8225 ≤ (5100995804901/12500000000000 : ℝ)^6177
        have hw : |(1020230429/2000000000 : ℝ)|=(1020230429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(735600437/2000000000 : ℝ)|^8225 ≤ (5279825034929/20000000000000 : ℝ)^6177
        have hw : |(735600437/2000000000 : ℝ)|=(735600437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (251/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20947/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14121/50000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (0 : ℝ) ^ (257/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^257 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^257*1^64 ≤ 0^64*1^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14121/50000 : ℝ) ^ (257/64 : ℝ) ≤ (311868879904202691/50000000000000000000 : ℝ) := by
    have hpowers : (14121/50000 : ℝ)^257 ≤ (311868879904202691/50000000000000000000 : ℝ)^64 := by
      have hnat : (14121 : ℕ)^257*50000000000000000000^64 ≤ 311868879904202691^64*50000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14121 50000 311868879904202691 50000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14121/50000 : ℝ)) (X := (311868879904202691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^257 := by
      have hnat : (1 : ℕ)^64*1^257 ≤ 1^257*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50311868879904202691/50000000000000000000 : ℝ) ≤ (10015496522458911/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (50311868879904202691/50000000000000000000 : ℝ)^64 ≤ (10015496522458911/10000000000000000 : ℝ)^257 := by
      have hnat : (50311868879904202691 : ℕ)^64*10000000000000000^257 ≤ 10015496522458911^257*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50311868879904202691 50000000000000000000 10015496522458911 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015496522458911/10000000000000000 : ℝ)) (X := (50311868879904202691/50000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25311868879904202691/25000000000000000000 : ℝ) ≤ (5015496522458911/5000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (25311868879904202691/25000000000000000000 : ℝ)^64 ≤ (5015496522458911/5000000000000000 : ℝ)^257 := by
      have hnat : (25311868879904202691 : ℕ)^64*5000000000000000^257 ≤ 5015496522458911^257*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25311868879904202691 25000000000000000000 5015496522458911 5000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015496522458911/5000000000000000 : ℝ)) (X := (25311868879904202691/25000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15496522458911/2824200000000000 : ℝ)*(0 : ℝ))^(257/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(15496522458911/2824200000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(311868879904202691/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15496522458911/2824200000000000 : ℝ)*((14121/50000 : ℝ)+(0 : ℝ)))^(257/64 : ℝ) := by
    rw [show (1 : ℝ)+(15496522458911/2824200000000000 : ℝ)*((14121/50000 : ℝ)+(0 : ℝ))=(10015496522458911/10000000000000000 : ℝ) by norm_num, show 1+(311868879904202691/50000000000000000000 : ℝ)+(0 : ℝ)=(50311868879904202691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(311868879904202691/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15496522458911/2824200000000000 : ℝ)*(14121/50000 : ℝ))^(257/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(15496522458911/2824200000000000 : ℝ)*(14121/50000 : ℝ)=(5015496522458911/5000000000000000 : ℝ) by norm_num, show 1+2*(311868879904202691/50000000000000000000 : ℝ)=(25311868879904202691/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15496522458911/2824200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (0 : ℝ)) (hi := (14121/50000 : ℝ)) (c := (1 : ℝ)) (alpha := (15496522458911/2824200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15496522458911/2824200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (0 : ℝ)) (hi := (14121/50000 : ℝ)) (c := (1 : ℝ)) (alpha := (15496522458911/2824200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15496522458911/2824200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (0 : ℝ)) (hi := (14121/50000 : ℝ)) (c := (1 : ℝ)) (alpha := (15496522458911/2824200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-427920759/2000000000 : ℝ)*X 0 0+(5731569643/10000000000 : ℝ)*X 0 1+(4978861459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((27125941/50000000 : ℝ)*X 1 0+(-2548135933/10000000000 : ℝ)*X 1 1+(497886177/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5425188519/10000000000 : ℝ)*X 2 0+(4978861353/10000000000 : ℝ)*X 2 1+(-509627209/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865345049/2000000000 : ℝ)*X 0 0+(3656738633/10000000000 : ℝ)*X 0 1+(2560995111/5000000000 : ℝ)*X 0 2+(865345049/2000000000 : ℝ)*X 1 0+(3656738633/10000000000 : ℝ)*X 1 1+(2560995111/5000000000 : ℝ)*X 1 2+(865345049/2000000000 : ℝ)*X 2 0+(3656738633/10000000000 : ℝ)*X 2 1+(2560995111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-133786097/625000000 : ℝ)*X 0 0+(249478221/500000000 : ℝ)*X 0 1+(2860322643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5233288261/10000000000 : ℝ)*X 1 0+(-903175529/5000000000 : ℝ)*X 1 1+(5720646277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((523328643/1000000000 : ℝ)*X 2 0+(2860324143/5000000000 : ℝ)*X 2 1+(-903175359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328617987/10000000000 : ℝ)*X 0 0+(1020230429/2000000000 : ℝ)*X 0 1+(735600437/2000000000 : ℝ)*X 0 2+(4328617987/10000000000 : ℝ)*X 1 0+(1020230429/2000000000 : ℝ)*X 1 1+(735600437/2000000000 : ℝ)*X 1 2+(4328617987/10000000000 : ℝ)*X 2 0+(1020230429/2000000000 : ℝ)*X 2 1+(735600437/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21386608496695861965411/2615000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123720897/100000000000000 : ℝ)*(base1) + (1860000503/100000000000000 : ℝ)*(base19) + (121132447/6250000000000 : ℝ)*(base23) + (204406869/100000000000000 : ℝ)*(upper3) + (188868113/100000000000000 : ℝ)*(upper5) + (502760223065583/50000000000000 : ℝ)*(major0) + (502760223065583/50000000000000 : ℝ)*(major1) + (502760223065583/50000000000000 : ℝ)*(major2) + (132854538450621/10000000000000 : ℝ)*(sp0) + (332138240529487/25000000000000 : ℝ)*(sp1) + (1328552883999299/100000000000000 : ℝ)*(sp2) + (682481026371491/100000000000000 : ℝ)*(sp3) + (4780666569/50000000000000 : ℝ)*(sp4) + (2323718489/50000000000000 : ℝ)*(sp7) + (341242898764683/50000000000000 : ℝ)*(f.failure) + (1328554822118451/100000000000000 : ℝ)*(f.sum) + (1347902107503/1307500000000000000000000000 : ℝ)*base66 + (25402902281129/5230000000000000000000000000 : ℝ)*base67 + (9599185413119/5230000000000000000000000000 : ℝ)*base69 + (3091384538189/5230000000000000000000000000 : ℝ)*base71 + (1170032099371/653750000000000000000000000 : ℝ)*base73 + (4172536879659/5230000000000000000000000000 : ℝ)*base75 + (17520773679559/5230000000000000000000000000 : ℝ)*base77 + (9935394028019/5230000000000000000000000000 : ℝ)*base79 + (82617214221/163437500000000000000000000 : ℝ)*base82 + (9480873/5000000000000000000000 : ℝ)*base90 + (9480873/5000000000000000000000 : ℝ)*base92 + (9480873/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23434810745381264707259/11767500000000000000000000000 : ℝ) := by norm_num
    linear_combination (975371219/50000000000000 : ℝ)*(base19) + (898546683/50000000000000 : ℝ)*(base23) + (161130059/100000000000000 : ℝ)*(upper2) + (56361791/20000000000000 : ℝ)*(upper3) + (87970713/20000000000000 : ℝ)*(upper5) + (1035251499679241/100000000000000 : ℝ)*(major0) + (1035251499679241/100000000000000 : ℝ)*(major1) + (1035251499679241/100000000000000 : ℝ)*(major2) + (9282149037/100000000000000 : ℝ)*(sp1) + (4873215707/50000000000000 : ℝ)*(sp2) + (1367837514166321/100000000000000 : ℝ)*(sp4) + (273565256254969/20000000000000 : ℝ)*(sp5) + (1367825970641541/100000000000000 : ℝ)*(sp6) + (702665418809289/100000000000000 : ℝ)*(sp7) + (702665418809289/100000000000000 : ℝ)*(f.failure) + (1367837514166321/100000000000000 : ℝ)*(f.sum) + (481630518414841/141210000000000000000000000000 : ℝ)*base65 + (1347856094752051/282420000000000000000000000000 : ℝ)*base67 + (386912005850731/282420000000000000000000000000 : ℝ)*base69 + (2109947976691591/282420000000000000000000000000 : ℝ)*base71 + (245578612034011/141210000000000000000000000000 : ℝ)*base73 + (3726244744638151/282420000000000000000000000000 : ℝ)*base75 + (3031635093358171/282420000000000000000000000000 : ℝ)*base77 + (374102140135891/282420000000000000000000000000 : ℝ)*base79 + (455939962313819/141210000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (35211059/10000000000000000000000 : ℝ)*base90 + (35211059/10000000000000000000000 : ℝ)*base92 + (35211059/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1032_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (251/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20947/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1032_s2_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199076779/10000000000 : ℝ)*x 0 + (1106572673/2000000000 : ℝ)*x 1 + (2569923347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199076779/10000000000 : ℝ)^8225 ≤ (1330940155811/10000000000000 : ℝ)^6177 := by
    have hnat : (2199076779 : ℕ)^8225*10000000000000^6177 ≤ 1330940155811^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199076779 10000000000 1330940155811 10000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106572673/2000000000 : ℝ)^8225 ≤ (22734968291707/50000000000000 : ℝ)^6177 := by
    have hnat : (1106572673 : ℕ)^8225*50000000000000^6177 ≤ 22734968291707^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106572673 2000000000 22734968291707 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569923347/5000000000 : ℝ)^8225 ≤ (10305165460013/25000000000000 : ℝ)^6177 := by
    have hnat : (2569923347 : ℕ)^8225*25000000000000^6177 ≤ 10305165460013^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569923347 5000000000 10305165460013 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199076779/10000000000 : ℝ), (1106572673/2000000000 : ℝ), (2569923347/5000000000 : ℝ)] ![(1330940155811/10000000000000 : ℝ), (22734968291707/50000000000000 : ℝ), (10305165460013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199076779/10000000000 : ℝ)|^8225 ≤ (1330940155811/10000000000000 : ℝ)^6177
        have hw : |(-2199076779/10000000000 : ℝ)|=(2199076779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106572673/2000000000 : ℝ)|^8225 ≤ (22734968291707/50000000000000 : ℝ)^6177
        have hw : |(1106572673/2000000000 : ℝ)|=(1106572673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569923347/5000000000 : ℝ)|^8225 ≤ (10305165460013/25000000000000 : ℝ)^6177
        have hw : |(2569923347/5000000000 : ℝ)|=(2569923347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s2_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5378692657/10000000000 : ℝ)*x 0 + (-2404332357/10000000000 : ℝ)*x 1 + (642481011/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378692657/10000000000 : ℝ)^8225 ≤ (43790702893637/100000000000000 : ℝ)^6177 := by
    have hnat : (5378692657 : ℕ)^8225*100000000000000^6177 ≤ 43790702893637^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378692657 10000000000 43790702893637 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2404332357/10000000000 : ℝ)^8225 ≤ (14988620358643/100000000000000 : ℝ)^6177 := by
    have hnat : (2404332357 : ℕ)^8225*100000000000000^6177 ≤ 14988620358643^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404332357 10000000000 14988620358643 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642481011/1250000000 : ℝ)^8225 ≤ (20610338363161/50000000000000 : ℝ)^6177 := by
    have hnat : (642481011 : ℕ)^8225*50000000000000^6177 ≤ 20610338363161^6177*1250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642481011 1250000000 20610338363161 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378692657/10000000000 : ℝ), (-2404332357/10000000000 : ℝ), (642481011/1250000000 : ℝ)] ![(43790702893637/100000000000000 : ℝ), (14988620358643/100000000000000 : ℝ), (20610338363161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378692657/10000000000 : ℝ)|^8225 ≤ (43790702893637/100000000000000 : ℝ)^6177
        have hw : |(5378692657/10000000000 : ℝ)|=(5378692657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2404332357/10000000000 : ℝ)|^8225 ≤ (14988620358643/100000000000000 : ℝ)^6177
        have hw : |(-2404332357/10000000000 : ℝ)|=(2404332357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642481011/1250000000 : ℝ)|^8225 ≤ (20610338363161/50000000000000 : ℝ)^6177
        have hw : |(642481011/1250000000 : ℝ)|=(642481011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s2_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5378693501/10000000000 : ℝ)*x 0 + (5139846871/10000000000 : ℝ)*x 1 + (-1202166411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378693501/10000000000 : ℝ)^8225 ≤ (21895356021659/50000000000000 : ℝ)^6177 := by
    have hnat : (5378693501 : ℕ)^8225*50000000000000^6177 ≤ 21895356021659^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378693501 10000000000 21895356021659 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139846871/10000000000 : ℝ)^8225 ≤ (20610331865101/50000000000000 : ℝ)^6177 := by
    have hnat : (5139846871 : ℕ)^8225*50000000000000^6177 ≤ 20610331865101^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139846871 10000000000 20610331865101 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1202166411/5000000000 : ℝ)^8225 ≤ (3747156054641/25000000000000 : ℝ)^6177 := by
    have hnat : (1202166411 : ℕ)^8225*25000000000000^6177 ≤ 3747156054641^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202166411 5000000000 3747156054641 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378693501/10000000000 : ℝ), (5139846871/10000000000 : ℝ), (-1202166411/5000000000 : ℝ)] ![(21895356021659/50000000000000 : ℝ), (20610331865101/50000000000000 : ℝ), (3747156054641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378693501/10000000000 : ℝ)|^8225 ≤ (21895356021659/50000000000000 : ℝ)^6177
        have hw : |(5378693501/10000000000 : ℝ)|=(5378693501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139846871/10000000000 : ℝ)|^8225 ≤ (20610331865101/50000000000000 : ℝ)^6177
        have hw : |(5139846871/10000000000 : ℝ)|=(5139846871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1202166411/5000000000 : ℝ)|^8225 ≤ (3747156054641/25000000000000 : ℝ)^6177
        have hw : |(-1202166411/5000000000 : ℝ)|=(1202166411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s2_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109175803/250000000 : ℝ)*x 0 + (2000765849/5000000000 : ℝ)*x 1 + (2383298433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109175803/250000000 : ℝ)^8225 ≤ (6636196950191/20000000000000 : ℝ)^6177 := by
    have hnat : (109175803 : ℕ)^8225*20000000000000^6177 ≤ 6636196950191^6177*250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109175803 250000000 6636196950191 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000765849/5000000000 : ℝ)^8225 ≤ (29535434941053/100000000000000 : ℝ)^6177 := by
    have hnat : (2000765849 : ℕ)^8225*100000000000000^6177 ≤ 29535434941053^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000765849 5000000000 29535434941053 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2383298433/5000000000 : ℝ)^8225 ≤ (18641790150447/50000000000000 : ℝ)^6177 := by
    have hnat : (2383298433 : ℕ)^8225*50000000000000^6177 ≤ 18641790150447^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383298433 5000000000 18641790150447 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109175803/250000000 : ℝ), (2000765849/5000000000 : ℝ), (2383298433/5000000000 : ℝ)] ![(6636196950191/20000000000000 : ℝ), (29535434941053/100000000000000 : ℝ), (18641790150447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109175803/250000000 : ℝ)|^8225 ≤ (6636196950191/20000000000000 : ℝ)^6177
        have hw : |(109175803/250000000 : ℝ)|=(109175803/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000765849/5000000000 : ℝ)|^8225 ≤ (29535434941053/100000000000000 : ℝ)^6177
        have hw : |(2000765849/5000000000 : ℝ)|=(2000765849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2383298433/5000000000 : ℝ)|^8225 ≤ (18641790150447/50000000000000 : ℝ)^6177
        have hw : |(2383298433/5000000000 : ℝ)|=(2383298433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s2_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-274901833/1250000000 : ℝ)*x 0 + (642846497/1250000000 : ℝ)*x 1 + (2764953301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274901833/1250000000 : ℝ)^8225 ≤ (13310512772811/100000000000000 : ℝ)^6177 := by
    have hnat : (274901833 : ℕ)^8225*100000000000000^6177 ≤ 13310512772811^6177*1250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274901833 1250000000 13310512772811 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642846497/1250000000 : ℝ)^8225 ≤ (20625951667509/50000000000000 : ℝ)^6177 := by
    have hnat : (642846497 : ℕ)^8225*50000000000000^6177 ≤ 20625951667509^6177*1250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642846497 1250000000 20625951667509 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2764953301/5000000000 : ℝ)^8225 ≤ (45437583867627/100000000000000 : ℝ)^6177 := by
    have hnat : (2764953301 : ℕ)^8225*100000000000000^6177 ≤ 45437583867627^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764953301 5000000000 45437583867627 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-274901833/1250000000 : ℝ), (642846497/1250000000 : ℝ), (2764953301/5000000000 : ℝ)] ![(13310512772811/100000000000000 : ℝ), (20625951667509/50000000000000 : ℝ), (45437583867627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-274901833/1250000000 : ℝ)|^8225 ≤ (13310512772811/100000000000000 : ℝ)^6177
        have hw : |(-274901833/1250000000 : ℝ)|=(274901833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642846497/1250000000 : ℝ)|^8225 ≤ (20625951667509/50000000000000 : ℝ)^6177
        have hw : |(642846497/1250000000 : ℝ)|=(642846497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2764953301/5000000000 : ℝ)|^8225 ≤ (45437583867627/100000000000000 : ℝ)^6177
        have hw : |(2764953301/5000000000 : ℝ)|=(2764953301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s2_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (164991639/312500000 : ℝ)*x 0 + (-100713683/500000000 : ℝ)*x 1 + (5529906653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164991639/312500000 : ℝ)^8225 ≤ (42721175370121/100000000000000 : ℝ)^6177 := by
    have hnat : (164991639 : ℕ)^8225*100000000000000^6177 ≤ 42721175370121^6177*312500000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164991639 312500000 42721175370121 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100713683/500000000 : ℝ)^8225 ≤ (11841240189489/100000000000000 : ℝ)^6177 := by
    have hnat : (100713683 : ℕ)^8225*100000000000000^6177 ≤ 11841240189489^6177*500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100713683 500000000 11841240189489 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5529906653/10000000000 : ℝ)^8225 ≤ (2839849026601/6250000000000 : ℝ)^6177 := by
    have hnat : (5529906653 : ℕ)^8225*6250000000000^6177 ≤ 2839849026601^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529906653 10000000000 2839849026601 6250000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164991639/312500000 : ℝ), (-100713683/500000000 : ℝ), (5529906653/10000000000 : ℝ)] ![(42721175370121/100000000000000 : ℝ), (11841240189489/100000000000000 : ℝ), (2839849026601/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164991639/312500000 : ℝ)|^8225 ≤ (42721175370121/100000000000000 : ℝ)^6177
        have hw : |(164991639/312500000 : ℝ)|=(164991639/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100713683/500000000 : ℝ)|^8225 ≤ (11841240189489/100000000000000 : ℝ)^6177
        have hw : |(-100713683/500000000 : ℝ)|=(100713683/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5529906653/10000000000 : ℝ)|^8225 ≤ (2839849026601/6250000000000 : ℝ)^6177
        have hw : |(5529906653/10000000000 : ℝ)|=(5529906653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s2_6 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2639866321/5000000000 : ℝ)*x 0 + (5529906507/10000000000 : ℝ)*x 1 + (-503568399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639866321/5000000000 : ℝ)^8225 ≤ (21360588730169/50000000000000 : ℝ)^6177 := by
    have hnat : (2639866321 : ℕ)^8225*50000000000000^6177 ≤ 21360588730169^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639866321 5000000000 21360588730169 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529906507/10000000000 : ℝ)^8225 ≤ (9087516565647/20000000000000 : ℝ)^6177 := by
    have hnat : (5529906507 : ℕ)^8225*20000000000000^6177 ≤ 9087516565647^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529906507 10000000000 9087516565647 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503568399/2500000000 : ℝ)^8225 ≤ (11841239688513/100000000000000 : ℝ)^6177 := by
    have hnat : (503568399 : ℕ)^8225*100000000000000^6177 ≤ 11841239688513^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503568399 2500000000 11841239688513 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639866321/5000000000 : ℝ), (5529906507/10000000000 : ℝ), (-503568399/2500000000 : ℝ)] ![(21360588730169/50000000000000 : ℝ), (9087516565647/20000000000000 : ℝ), (11841239688513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639866321/5000000000 : ℝ)|^8225 ≤ (21360588730169/50000000000000 : ℝ)^6177
        have hw : |(2639866321/5000000000 : ℝ)|=(2639866321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529906507/10000000000 : ℝ)|^8225 ≤ (9087516565647/20000000000000 : ℝ)^6177
        have hw : |(5529906507/10000000000 : ℝ)|=(5529906507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-503568399/2500000000 : ℝ)|^8225 ≤ (11841239688513/100000000000000 : ℝ)^6177
        have hw : |(-503568399/2500000000 : ℝ)|=(503568399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s2_7 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367302073/10000000000 : ℝ)*x 0 + (4760900307/10000000000 : ℝ)*x 1 + (801457601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367302073/10000000000 : ℝ)^8225 ≤ (3318371595281/10000000000000 : ℝ)^6177 := by
    have hnat : (4367302073 : ℕ)^8225*10000000000000^6177 ≤ 3318371595281^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367302073 10000000000 3318371595281 10000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4760900307/10000000000 : ℝ)^8225 ≤ (9306065318467/25000000000000 : ℝ)^6177 := by
    have hnat : (4760900307 : ℕ)^8225*25000000000000^6177 ≤ 9306065318467^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4760900307 10000000000 9306065318467 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801457601/2000000000 : ℝ)^8225 ≤ (7398005687699/25000000000000 : ℝ)^6177 := by
    have hnat : (801457601 : ℕ)^8225*25000000000000^6177 ≤ 7398005687699^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801457601 2000000000 7398005687699 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367302073/10000000000 : ℝ), (4760900307/10000000000 : ℝ), (801457601/2000000000 : ℝ)] ![(3318371595281/10000000000000 : ℝ), (9306065318467/25000000000000 : ℝ), (7398005687699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367302073/10000000000 : ℝ)|^8225 ≤ (3318371595281/10000000000000 : ℝ)^6177
        have hw : |(4367302073/10000000000 : ℝ)|=(4367302073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4760900307/10000000000 : ℝ)|^8225 ≤ (9306065318467/25000000000000 : ℝ)^6177
        have hw : |(4760900307/10000000000 : ℝ)|=(4760900307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801457601/2000000000 : ℝ)|^8225 ≤ (7398005687699/25000000000000 : ℝ)^6177
        have hw : |(801457601/2000000000 : ℝ)|=(801457601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (251/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (4273/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16851/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (251/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (251/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (251/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (251/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (251/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (251/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (251/5000 : ℝ) ^ (257/64 : ℝ) ≤ (606056849892221/100000000000000000000 : ℝ) := by
    have hpowers : (251/5000 : ℝ)^257 ≤ (606056849892221/100000000000000000000 : ℝ)^64 := by
      have hnat : (251 : ℕ)^257*100000000000000000000^64 ≤ 606056849892221^64*5000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251 5000 606056849892221 100000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (251/5000 : ℝ)) (X := (606056849892221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (20947/100000 : ℝ) ^ (257/64 : ℝ) ≤ (5871240644268279/3125000000000000000 : ℝ) := by
    have hpowers : (20947/100000 : ℝ)^257 ≤ (5871240644268279/3125000000000000000 : ℝ)^64 := by
      have hnat : (20947 : ℕ)^257*3125000000000000000^64 ≤ 5871240644268279^64*100000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20947 100000 5871240644268279 3125000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20947/100000 : ℝ)) (X := (5871240644268279/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000606056849892221/50000000000000000000 : ℝ) ≤ (5000015092397611/5000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (50000606056849892221/50000000000000000000 : ℝ)^64 ≤ (5000015092397611/5000000000000000 : ℝ)^257 := by
      have hnat : (50000606056849892221 : ℕ)^64*5000000000000000^257 ≤ 5000015092397611^257*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000606056849892221 50000000000000000000 5000015092397611 5000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015092397611/5000000000000000 : ℝ)) (X := (50000606056849892221/50000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100188485757466477149/100000000000000000000 : ℝ) ≤ (10004690490407617/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (100188485757466477149/100000000000000000000 : ℝ)^64 ≤ (10004690490407617/10000000000000000 : ℝ)^257 := by
      have hnat : (100188485757466477149 : ℕ)^64*10000000000000000^257 ≤ 10004690490407617^257*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100188485757466477149 100000000000000000000 10004690490407617 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004690490407617/10000000000000000 : ℝ)) (X := (100188485757466477149/100000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (1568371240644268279/1562500000000000000 : ℝ) ≤ (2502337699005003/2500000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (1568371240644268279/1562500000000000000 : ℝ)^64 ≤ (2502337699005003/2500000000000000 : ℝ)^257 := by
      have hnat : (1568371240644268279 : ℕ)^64*2500000000000000^257 ≤ 2502337699005003^257*1562500000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1568371240644268279 1562500000000000000 2502337699005003 2500000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502337699005003/2500000000000000 : ℝ)) (X := (1568371240644268279/1562500000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(606056849892221/100000000000000000000 : ℝ) ≤ ((79611845642442527497/79635000000000000000 : ℝ)+2*(932061122479/318540000000000 : ℝ)*(251/5000 : ℝ))^(257/64 : ℝ) := by
    rw [show (79611845642442527497/79635000000000000000 : ℝ)+2*(932061122479/318540000000000 : ℝ)*(251/5000 : ℝ)=(5000015092397611/5000000000000000 : ℝ) by norm_num, show 1+2*(606056849892221/100000000000000000000 : ℝ)=(50000606056849892221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5871240644268279/3125000000000000000 : ℝ)+(606056849892221/100000000000000000000 : ℝ) ≤ ((79611845642442527497/79635000000000000000 : ℝ)+(932061122479/318540000000000 : ℝ)*((20947/100000 : ℝ)+(251/5000 : ℝ)))^(257/64 : ℝ) := by
    rw [show (79611845642442527497/79635000000000000000 : ℝ)+(932061122479/318540000000000 : ℝ)*((20947/100000 : ℝ)+(251/5000 : ℝ))=(10004690490407617/10000000000000000 : ℝ) by norm_num, show 1+(5871240644268279/3125000000000000000 : ℝ)+(606056849892221/100000000000000000000 : ℝ)=(100188485757466477149/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5871240644268279/3125000000000000000 : ℝ) ≤ ((79611845642442527497/79635000000000000000 : ℝ)+2*(932061122479/318540000000000 : ℝ)*(20947/100000 : ℝ))^(257/64 : ℝ) := by
    rw [show (79611845642442527497/79635000000000000000 : ℝ)+2*(932061122479/318540000000000 : ℝ)*(20947/100000 : ℝ)=(2502337699005003/2500000000000000 : ℝ) by norm_num, show 1+2*(5871240644268279/3125000000000000000 : ℝ)=(1568371240644268279/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (79611845642442527497/79635000000000000000 : ℝ)*(X 1 0+X 2 0)+(932061122479/318540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (251/5000 : ℝ)) (hi := (20947/100000 : ℝ)) (c := (79611845642442527497/79635000000000000000 : ℝ)) (alpha := (932061122479/318540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (79611845642442527497/79635000000000000000 : ℝ)*(X 0 1+X 2 1)+(932061122479/318540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (251/5000 : ℝ)) (hi := (20947/100000 : ℝ)) (c := (79611845642442527497/79635000000000000000 : ℝ)) (alpha := (932061122479/318540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (79611845642442527497/79635000000000000000 : ℝ)*(X 0 2+X 1 2)+(932061122479/318540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (251/5000 : ℝ)) (hi := (20947/100000 : ℝ)) (c := (79611845642442527497/79635000000000000000 : ℝ)) (alpha := (932061122479/318540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2199076779/10000000000 : ℝ)*X 0 0+(1106572673/2000000000 : ℝ)*X 0 1+(2569923347/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378692657/10000000000 : ℝ)*X 1 0+(-2404332357/10000000000 : ℝ)*X 1 1+(642481011/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378693501/10000000000 : ℝ)*X 2 0+(5139846871/10000000000 : ℝ)*X 2 1+(-1202166411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((109175803/250000000 : ℝ)*X 0 0+(2000765849/5000000000 : ℝ)*X 0 1+(2383298433/5000000000 : ℝ)*X 0 2+(109175803/250000000 : ℝ)*X 1 0+(2000765849/5000000000 : ℝ)*X 1 1+(2383298433/5000000000 : ℝ)*X 1 2+(109175803/250000000 : ℝ)*X 2 0+(2000765849/5000000000 : ℝ)*X 2 1+(2383298433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-274901833/1250000000 : ℝ)*X 0 0+(642846497/1250000000 : ℝ)*X 0 1+(2764953301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((164991639/312500000 : ℝ)*X 1 0+(-100713683/500000000 : ℝ)*X 1 1+(5529906653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639866321/5000000000 : ℝ)*X 2 0+(5529906507/10000000000 : ℝ)*X 2 1+(-503568399/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367302073/10000000000 : ℝ)*X 0 0+(4760900307/10000000000 : ℝ)*X 0 1+(801457601/2000000000 : ℝ)*X 0 2+(4367302073/10000000000 : ℝ)*X 1 0+(4760900307/10000000000 : ℝ)*X 1 1+(801457601/2000000000 : ℝ)*X 1 2+(4367302073/10000000000 : ℝ)*X 2 0+(4760900307/10000000000 : ℝ)*X 2 1+(801457601/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (162778246599305927796236087/26545000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175679971/25000000000000 : ℝ)*(base19) + (18917793/1562500000000 : ℝ)*(base23) + (58026759/50000000000000 : ℝ)*(upper2) + (5627587/6250000000000 : ℝ)*(upper3) + (57557503/100000000000000 : ℝ)*(upper4) + (38515521144529/2000000000000 : ℝ)*(major0) + (38515521144529/2000000000000 : ℝ)*(major1) + (38515521144529/2000000000000 : ℝ)*(major2) + (2544437330706531/100000000000000 : ℝ)*(sp0) + (636113042219577/25000000000000 : ℝ)*(sp1) + (31805645760743/1250000000000 : ℝ)*(sp2) + (653543960396561/50000000000000 : ℝ)*(sp3) + (7770445831/50000000000000 : ℝ)*(sp4) + (2779414043/25000000000000 : ℝ)*(sp7) + (653549519224647/50000000000000 : ℝ)*(f.failure) + (2544452871598193/100000000000000 : ℝ)*(f.sum) + (16361235408017/15927000000000000000000000000 : ℝ)*base65 + (810697401451126087/159270000000000000000000000000000 : ℝ)*base68 + (934443289167136087/159270000000000000000000000000000 : ℝ)*base70 + (149910829034323913/159270000000000000000000000000000 : ℝ)*base71 + (17496621136079/7963500000000000000000000000 : ℝ)*base74 + (57273016041043913/159270000000000000000000000000000 : ℝ)*base75 + (653790925605643913/159270000000000000000000000000000 : ℝ)*base77 + (856379886727363913/159270000000000000000000000000000 : ℝ)*base79 + (17098596072857/7963500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (18304643/5000000000000000000000 : ℝ)*base89 + (18304643/5000000000000000000000 : ℝ)*base91 + (18304643/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9559924631158318735697/1327250000000000000000000000 : ℝ) := by norm_num
    linear_combination (274998809/20000000000000 : ℝ)*(base19) + (390453989/25000000000000 : ℝ)*(base23) + (88090121/50000000000000 : ℝ)*(upper3) + (35231227/100000000000000 : ℝ)*(lower4) + (83914659/50000000000000 : ℝ)*(upper5) + (977505831012983/50000000000000 : ℝ)*(major0) + (977505831012983/50000000000000 : ℝ)*(major1) + (977505831012983/50000000000000 : ℝ)*(major2) + (1447310363/12500000000000 : ℝ)*(sp1) + (258435341/2000000000000 : ℝ)*(sp2) + (322885088068261/12500000000000 : ℝ)*(sp4) + (129153387553457/5000000000000 : ℝ)*(sp5) + (1291533110481541/50000000000000 : ℝ)*(sp6) + (165867797426537/12500000000000 : ℝ)*(sp7) + (165867797426537/12500000000000 : ℝ)*(f.failure) + (322885088068261/12500000000000 : ℝ)*(f.sum) + (10336851250781/7963500000000000000000000000 : ℝ)*base65 + (22366488799425743551/3981750000000000000000000000000000 : ℝ)*base67 + (2701510708377743551/3981750000000000000000000000000000 : ℝ)*base69 + (10209703081772256449/3981750000000000000000000000000000 : ℝ)*base72 + (16249411010513/7963500000000000000000000000 : ℝ)*base73 + (28235106020945256449/3981750000000000000000000000000000 : ℝ)*base76 + (22086374510567243551/3981750000000000000000000000000000 : ℝ)*base77 + (15560258244017256449/3981750000000000000000000000000000 : ℝ)*base80 + (19484515799101/7963500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3284947/1250000000000000000000 : ℝ)*base90 + (3284947/1250000000000000000000 : ℝ)*base92 + (3284947/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1032_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (251/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4273/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16851/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1032_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4273/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16851/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1032_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1032_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1032_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4273/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16851/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1032_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

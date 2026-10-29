-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1501_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:52:24.481046+00:00
-- url     : https://prove2.me/submissions/2982e27e-fa52-4156-93f9-82ad9a84dd93

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
theorem support_rectangle_w1501_s6_0 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-376878217/2000000000 : ℝ)*x 0 + (5434666091/10000000000 : ℝ)*x 1 + (326066447/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376878217/2000000000 : ℝ)^4499 ≤ (5761706865617/50000000000000 : ℝ)^3475 := by
    have hnat : (376878217 : ℕ)^4499*50000000000000^3475 ≤ 5761706865617^3475*2000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376878217 2000000000 5761706865617 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434666091/10000000000 : ℝ)^4499 ≤ (45408232429999/100000000000000 : ℝ)^3475 := by
    have hnat : (5434666091 : ℕ)^4499*100000000000000^3475 ≤ 45408232429999^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434666091 10000000000 45408232429999 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326066447/625000000 : ℝ)^4499 ≤ (4306835382271/10000000000000 : ℝ)^3475 := by
    have hnat : (326066447 : ℕ)^4499*10000000000000^3475 ≤ 4306835382271^3475*625000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326066447 625000000 4306835382271 10000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-376878217/2000000000 : ℝ), (5434666091/10000000000 : ℝ), (326066447/625000000 : ℝ)] ![(5761706865617/50000000000000 : ℝ), (45408232429999/100000000000000 : ℝ), (4306835382271/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-376878217/2000000000 : ℝ)|^4499 ≤ (5761706865617/50000000000000 : ℝ)^3475
        have hw : |(-376878217/2000000000 : ℝ)|=(376878217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434666091/10000000000 : ℝ)|^4499 ≤ (45408232429999/100000000000000 : ℝ)^3475
        have hw : |(5434666091/10000000000 : ℝ)|=(5434666091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326066447/625000000 : ℝ)|^4499 ≤ (4306835382271/10000000000000 : ℝ)^3475
        have hw : |(326066447/625000000 : ℝ)|=(326066447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s6_1 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338048731/2500000000 : ℝ)*x 0 + (-997930931/5000000000 : ℝ)*x 1 + (2608531503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338048731/2500000000 : ℝ)^4499 ≤ (44518110600403/100000000000000 : ℝ)^3475 := by
    have hnat : (1338048731 : ℕ)^4499*100000000000000^3475 ≤ 44518110600403^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338048731 2500000000 44518110600403 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997930931/5000000000 : ℝ)^4499 ≤ (12413537125571/100000000000000 : ℝ)^3475 := by
    have hnat : (997930931 : ℕ)^4499*100000000000000^3475 ≤ 12413537125571^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997930931 5000000000 12413537125571 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608531503/5000000000 : ℝ)^4499 ≤ (43068352262273/100000000000000 : ℝ)^3475 := by
    have hnat : (2608531503 : ℕ)^4499*100000000000000^3475 ≤ 43068352262273^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608531503 5000000000 43068352262273 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338048731/2500000000 : ℝ), (-997930931/5000000000 : ℝ), (2608531503/5000000000 : ℝ)] ![(44518110600403/100000000000000 : ℝ), (12413537125571/100000000000000 : ℝ), (43068352262273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338048731/2500000000 : ℝ)|^4499 ≤ (44518110600403/100000000000000 : ℝ)^3475
        have hw : |(1338048731/2500000000 : ℝ)|=(1338048731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-997930931/5000000000 : ℝ)|^4499 ≤ (12413537125571/100000000000000 : ℝ)^3475
        have hw : |(-997930931/5000000000 : ℝ)|=(997930931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608531503/5000000000 : ℝ)|^4499 ≤ (43068352262273/100000000000000 : ℝ)^3475
        have hw : |(2608531503/5000000000 : ℝ)|=(2608531503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s6_2 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676097381/5000000000 : ℝ)*x 0 + (5217063143/10000000000 : ℝ)*x 1 + (-249482737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676097381/5000000000 : ℝ)^4499 ≤ (44518108855863/100000000000000 : ℝ)^3475 := by
    have hnat : (2676097381 : ℕ)^4499*100000000000000^3475 ≤ 44518108855863^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676097381 5000000000 44518108855863 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217063143/10000000000 : ℝ)^4499 ≤ (43068353726519/100000000000000 : ℝ)^3475 := by
    have hnat : (5217063143 : ℕ)^4499*100000000000000^3475 ≤ 43068353726519^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217063143 10000000000 43068353726519 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249482737/1250000000 : ℝ)^4499 ≤ (6206768699677/50000000000000 : ℝ)^3475 := by
    have hnat : (249482737 : ℕ)^4499*50000000000000^3475 ≤ 6206768699677^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249482737 1250000000 6206768699677 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676097381/5000000000 : ℝ), (5217063143/10000000000 : ℝ), (-249482737/1250000000 : ℝ)] ![(44518108855863/100000000000000 : ℝ), (43068353726519/100000000000000 : ℝ), (6206768699677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676097381/5000000000 : ℝ)|^4499 ≤ (44518108855863/100000000000000 : ℝ)^3475
        have hw : |(2676097381/5000000000 : ℝ)|=(2676097381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217063143/10000000000 : ℝ)|^4499 ≤ (43068353726519/100000000000000 : ℝ)^3475
        have hw : |(5217063143/10000000000 : ℝ)|=(5217063143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249482737/1250000000 : ℝ)|^4499 ≤ (6206768699677/50000000000000 : ℝ)^3475
        have hw : |(-249482737/1250000000 : ℝ)|=(249482737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s6_3 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274922441/10000000000 : ℝ)*x 0 + (50451541/125000000 : ℝ)*x 1 + (452573419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274922441/10000000000 : ℝ)^4499 ≤ (8319774645947/25000000000000 : ℝ)^3475 := by
    have hnat : (4274922441 : ℕ)^4499*25000000000000^3475 ≤ 8319774645947^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274922441 10000000000 8319774645947 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50451541/125000000 : ℝ)^4499 ≤ (6178477775629/20000000000000 : ℝ)^3475 := by
    have hnat : (50451541 : ℕ)^4499*20000000000000^3475 ≤ 6178477775629^3475*125000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50451541 125000000 6178477775629 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452573419/1000000000 : ℝ)^4499 ≤ (35828512528529/100000000000000 : ℝ)^3475 := by
    have hnat : (452573419 : ℕ)^4499*100000000000000^3475 ≤ 35828512528529^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452573419 1000000000 35828512528529 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274922441/10000000000 : ℝ), (50451541/125000000 : ℝ), (452573419/1000000000 : ℝ)] ![(8319774645947/25000000000000 : ℝ), (6178477775629/20000000000000 : ℝ), (35828512528529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274922441/10000000000 : ℝ)|^4499 ≤ (8319774645947/25000000000000 : ℝ)^3475
        have hw : |(4274922441/10000000000 : ℝ)|=(4274922441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50451541/125000000 : ℝ)|^4499 ≤ (6178477775629/20000000000000 : ℝ)^3475
        have hw : |(50451541/125000000 : ℝ)|=(50451541/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452573419/1000000000 : ℝ)|^4499 ≤ (35828512528529/100000000000000 : ℝ)^3475
        have hw : |(452573419/1000000000 : ℝ)|=(452573419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s6_4 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2944407/15625000 : ℝ)*x 0 + (5218180799/10000000000 : ℝ)*x 1 + (2716770119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2944407/15625000 : ℝ)^4499 ≤ (11523646457693/100000000000000 : ℝ)^3475 := by
    have hnat : (2944407 : ℕ)^4499*100000000000000^3475 ≤ 11523646457693^3475*15625000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2944407 15625000 11523646457693 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218180799/10000000000 : ℝ)^4499 ≤ (43080299526087/100000000000000 : ℝ)^3475 := by
    have hnat : (5218180799 : ℕ)^4499*100000000000000^3475 ≤ 43080299526087^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218180799 10000000000 43080299526087 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716770119/5000000000 : ℝ)^4499 ≤ (45396053998777/100000000000000 : ℝ)^3475 := by
    have hnat : (2716770119 : ℕ)^4499*100000000000000^3475 ≤ 45396053998777^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716770119 5000000000 45396053998777 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2944407/15625000 : ℝ), (5218180799/10000000000 : ℝ), (2716770119/5000000000 : ℝ)] ![(11523646457693/100000000000000 : ℝ), (43080299526087/100000000000000 : ℝ), (45396053998777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2944407/15625000 : ℝ)|^4499 ≤ (11523646457693/100000000000000 : ℝ)^3475
        have hw : |(-2944407/15625000 : ℝ)|=(2944407/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218180799/10000000000 : ℝ)|^4499 ≤ (43080299526087/100000000000000 : ℝ)^3475
        have hw : |(5218180799/10000000000 : ℝ)|=(5218180799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716770119/5000000000 : ℝ)|^4499 ≤ (45396053998777/100000000000000 : ℝ)^3475
        have hw : |(2716770119/5000000000 : ℝ)|=(2716770119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s6_5 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295168281/10000000000 : ℝ)*x 0 + (-1779384759/10000000000 : ℝ)*x 1 + (1358385059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295168281/10000000000 : ℝ)^4499 ≤ (8780994089641/20000000000000 : ℝ)^3475 := by
    have hnat : (5295168281 : ℕ)^4499*20000000000000^3475 ≤ 8780994089641^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295168281 10000000000 8780994089641 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1779384759/10000000000 : ℝ)^4499 ≤ (5349487778753/50000000000000 : ℝ)^3475 := by
    have hnat : (1779384759 : ℕ)^4499*50000000000000^3475 ≤ 5349487778753^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779384759 10000000000 5349487778753 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358385059/2500000000 : ℝ)^4499 ≤ (45396053977143/100000000000000 : ℝ)^3475 := by
    have hnat : (1358385059 : ℕ)^4499*100000000000000^3475 ≤ 45396053977143^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358385059 2500000000 45396053977143 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295168281/10000000000 : ℝ), (-1779384759/10000000000 : ℝ), (1358385059/2500000000 : ℝ)] ![(8780994089641/20000000000000 : ℝ), (5349487778753/50000000000000 : ℝ), (45396053977143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295168281/10000000000 : ℝ)|^4499 ≤ (8780994089641/20000000000000 : ℝ)^3475
        have hw : |(5295168281/10000000000 : ℝ)|=(5295168281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1779384759/10000000000 : ℝ)|^4499 ≤ (5349487778753/50000000000000 : ℝ)^3475
        have hw : |(-1779384759/10000000000 : ℝ)|=(1779384759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358385059/2500000000 : ℝ)|^4499 ≤ (45396053977143/100000000000000 : ℝ)^3475
        have hw : |(1358385059/2500000000 : ℝ)|=(1358385059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s6_6 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295168279/10000000000 : ℝ)*x 0 + (1358385059/2500000000 : ℝ)*x 1 + (-889692381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295168279/10000000000 : ℝ)^4499 ≤ (2744060651671/6250000000000 : ℝ)^3475 := by
    have hnat : (5295168279 : ℕ)^4499*6250000000000^3475 ≤ 2744060651671^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295168279 10000000000 2744060651671 6250000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358385059/2500000000 : ℝ)^4499 ≤ (45396053977143/100000000000000 : ℝ)^3475 := by
    have hnat : (1358385059 : ℕ)^4499*100000000000000^3475 ≤ 45396053977143^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358385059 2500000000 45396053977143 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889692381/5000000000 : ℝ)^4499 ≤ (534948779043/5000000000000 : ℝ)^3475 := by
    have hnat : (889692381 : ℕ)^4499*5000000000000^3475 ≤ 534948779043^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889692381 5000000000 534948779043 5000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295168279/10000000000 : ℝ), (1358385059/2500000000 : ℝ), (-889692381/5000000000 : ℝ)] ![(2744060651671/6250000000000 : ℝ), (45396053977143/100000000000000 : ℝ), (534948779043/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295168279/10000000000 : ℝ)|^4499 ≤ (2744060651671/6250000000000 : ℝ)^3475
        have hw : |(5295168279/10000000000 : ℝ)|=(5295168279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358385059/2500000000 : ℝ)|^4499 ≤ (45396053977143/100000000000000 : ℝ)^3475
        have hw : |(1358385059/2500000000 : ℝ)|=(1358385059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-889692381/5000000000 : ℝ)|^4499 ≤ (534948779043/5000000000000 : ℝ)^3475
        have hw : |(-889692381/5000000000 : ℝ)|=(889692381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s6_7 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274988841/10000000000 : ℝ)*x 0 + (4523219391/10000000000 : ℝ)*x 1 + (4038656391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274988841/10000000000 : ℝ)^4499 ≤ (33279767810969/100000000000000 : ℝ)^3475 := by
    have hnat : (4274988841 : ℕ)^4499*100000000000000^3475 ≤ 33279767810969^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274988841 10000000000 33279767810969 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523219391/10000000000 : ℝ)^4499 ≤ (4475342413897/12500000000000 : ℝ)^3475 := by
    have hnat : (4523219391 : ℕ)^4499*12500000000000^3475 ≤ 4475342413897^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523219391 10000000000 4475342413897 12500000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038656391/10000000000 : ℝ)^4499 ≤ (15458746430427/50000000000000 : ℝ)^3475 := by
    have hnat : (4038656391 : ℕ)^4499*50000000000000^3475 ≤ 15458746430427^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038656391 10000000000 15458746430427 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274988841/10000000000 : ℝ), (4523219391/10000000000 : ℝ), (4038656391/10000000000 : ℝ)] ![(33279767810969/100000000000000 : ℝ), (4475342413897/12500000000000 : ℝ), (15458746430427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274988841/10000000000 : ℝ)|^4499 ≤ (33279767810969/100000000000000 : ℝ)^3475
        have hw : |(4274988841/10000000000 : ℝ)|=(4274988841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523219391/10000000000 : ℝ)|^4499 ≤ (4475342413897/12500000000000 : ℝ)^3475
        have hw : |(4523219391/10000000000 : ℝ)|=(4523219391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4038656391/10000000000 : ℝ)|^4499 ≤ (15458746430427/50000000000000 : ℝ)^3475
        have hw : |(4038656391/10000000000 : ℝ)|=(4038656391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1501_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10873/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1359/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1359/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1359/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1359/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1359/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1359/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1359/12500 : ℝ) ^ (4497/1024 : ℝ) ≤ (5859425642024011/100000000000000000000 : ℝ) := by
    have hpowers : (1359/12500 : ℝ)^4497 ≤ (5859425642024011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1359 : ℕ)^4497*100000000000000000000^1024 ≤ 5859425642024011^1024*12500^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1359 12500 5859425642024011 100000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1359/12500 : ℝ)) (X := (5859425642024011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4497/1024 : ℝ) ≤ (27664324435821481/100000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4497 ≤ (27664324435821481/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4497*100000000000000000000^1024 ≤ 27664324435821481^1024*100000^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 27664324435821481 100000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (27664324435821481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005859425642024011/50000000000000000000 : ℝ) ≤ (10000266834794859/10000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (50005859425642024011/50000000000000000000 : ℝ)^1024 ≤ (10000266834794859/10000000000000000 : ℝ)^4497 := by
      have hnat : (50005859425642024011 : ℕ)^1024*10000000000000000^4497 ≤ 10000266834794859^4497*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005859425642024011 50000000000000000000 10000266834794859 10000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000266834794859/10000000000000000 : ℝ)) (X := (50005859425642024011/50000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008380937519461373/25000000000000000000 : ℝ) ≤ (5000381630833151/5000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (25008380937519461373/25000000000000000000 : ℝ)^1024 ≤ (5000381630833151/5000000000000000 : ℝ)^4497 := by
      have hnat : (25008380937519461373 : ℕ)^1024*5000000000000000^4497 ≤ 5000381630833151^4497*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008380937519461373 25000000000000000000 5000381630833151 5000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000381630833151/5000000000000000 : ℝ)) (X := (25008380937519461373/25000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027664324435821481/50000000000000000000 : ℝ) ≤ (2000251937707549/2000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (50027664324435821481/50000000000000000000 : ℝ)^1024 ≤ (2000251937707549/2000000000000000 : ℝ)^4497 := by
      have hnat : (50027664324435821481 : ℕ)^1024*2000000000000000^4497 ≤ 2000251937707549^4497*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027664324435821481 50000000000000000000 2000251937707549 2000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000251937707549/2000000000000000 : ℝ)) (X := (50027664324435821481/50000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5859425642024011/100000000000000000000 : ℝ) ≤ ((46080435535676848539/46090000000000000000 : ℝ)+2*(496426871443/460900000000000 : ℝ)*(1359/12500 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (46080435535676848539/46090000000000000000 : ℝ)+2*(496426871443/460900000000000 : ℝ)*(1359/12500 : ℝ)=(10000266834794859/10000000000000000 : ℝ) by norm_num, show 1+2*(5859425642024011/100000000000000000000 : ℝ)=(50005859425642024011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27664324435821481/100000000000000000000 : ℝ)+(5859425642024011/100000000000000000000 : ℝ) ≤ ((46080435535676848539/46090000000000000000 : ℝ)+(496426871443/460900000000000 : ℝ)*((15481/100000 : ℝ)+(1359/12500 : ℝ)))^(4497/1024 : ℝ) := by
    rw [show (46080435535676848539/46090000000000000000 : ℝ)+(496426871443/460900000000000 : ℝ)*((15481/100000 : ℝ)+(1359/12500 : ℝ))=(5000381630833151/5000000000000000 : ℝ) by norm_num, show 1+(27664324435821481/100000000000000000000 : ℝ)+(5859425642024011/100000000000000000000 : ℝ)=(25008380937519461373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27664324435821481/100000000000000000000 : ℝ) ≤ ((46080435535676848539/46090000000000000000 : ℝ)+2*(496426871443/460900000000000 : ℝ)*(15481/100000 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (46080435535676848539/46090000000000000000 : ℝ)+2*(496426871443/460900000000000 : ℝ)*(15481/100000 : ℝ)=(2000251937707549/2000000000000000 : ℝ) by norm_num, show 1+2*(27664324435821481/100000000000000000000 : ℝ)=(50027664324435821481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46080435535676848539/46090000000000000000 : ℝ)*(X 1 0+X 2 0)+(496426871443/460900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (46080435535676848539/46090000000000000000 : ℝ)) (alpha := (496426871443/460900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46080435535676848539/46090000000000000000 : ℝ)*(X 0 1+X 2 1)+(496426871443/460900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (46080435535676848539/46090000000000000000 : ℝ)) (alpha := (496426871443/460900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46080435535676848539/46090000000000000000 : ℝ)*(X 0 2+X 1 2)+(496426871443/460900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (46080435535676848539/46090000000000000000 : ℝ)) (alpha := (496426871443/460900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-376878217/2000000000 : ℝ)*X 0 0+(5434666091/10000000000 : ℝ)*X 0 1+(326066447/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338048731/2500000000 : ℝ)*X 1 0+(-997930931/5000000000 : ℝ)*X 1 1+(2608531503/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676097381/5000000000 : ℝ)*X 2 0+(5217063143/10000000000 : ℝ)*X 2 1+(-249482737/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4274922441/10000000000 : ℝ)*X 0 0+(50451541/125000000 : ℝ)*X 0 1+(452573419/1000000000 : ℝ)*X 0 2+(4274922441/10000000000 : ℝ)*X 1 0+(50451541/125000000 : ℝ)*X 1 1+(452573419/1000000000 : ℝ)*X 1 2+(4274922441/10000000000 : ℝ)*X 2 0+(50451541/125000000 : ℝ)*X 2 1+(452573419/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2944407/15625000 : ℝ)*X 0 0+(5218180799/10000000000 : ℝ)*X 0 1+(2716770119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295168281/10000000000 : ℝ)*X 1 0+(-1779384759/10000000000 : ℝ)*X 1 1+(1358385059/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295168279/10000000000 : ℝ)*X 2 0+(1358385059/2500000000 : ℝ)*X 2 1+(-889692381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4274988841/10000000000 : ℝ)*X 0 0+(4523219391/10000000000 : ℝ)*X 0 1+(4038656391/10000000000 : ℝ)*X 0 2+(4274988841/10000000000 : ℝ)*X 1 0+(4523219391/10000000000 : ℝ)*X 1 1+(4038656391/10000000000 : ℝ)*X 1 2+(4274988841/10000000000 : ℝ)*X 2 0+(4523219391/10000000000 : ℝ)*X 2 1+(4038656391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2396038080193090038786551877/576125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (404135819/50000000000000 : ℝ)*(base19) + (62275167/10000000000000 : ℝ)*(base23) + (55891837/50000000000000 : ℝ)*(upper3) + (24846033/100000000000000 : ℝ)*(upper4) + (5885879/25000000000000 : ℝ)*(upper5) + (829749519150781/25000000000000 : ℝ)*(major0) + (829749519150781/25000000000000 : ℝ)*(major1) + (829749519150781/25000000000000 : ℝ)*(major2) + (919107706594781/20000000000000 : ℝ)*(sp0) + (4595547319831177/100000000000000 : ℝ)*(sp1) + (919109501070229/20000000000000 : ℝ)*(sp2) + (510610656605633/25000000000000 : ℝ)*(sp3) + (959512891/10000000000000 : ℝ)*(sp4) + (526005137/10000000000000 : ℝ)*(sp7) + (1021223943236951/50000000000000 : ℝ)*(f.failure) + (919109625620563/20000000000000 : ℝ)*(f.sum) + (589576869367/23045000000000000000000000000 : ℝ)*base65 + (13731686971829891041/1152250000000000000000000000000000 : ℝ)*base68 + (210320466086358959/1152250000000000000000000000000000 : ℝ)*base69 + (1382255464903641041/1152250000000000000000000000000000 : ℝ)*base72 + (36961393151897/5761250000000000000000000000 : ℝ)*base74 + (6307968064288141041/1152250000000000000000000000000000 : ℝ)*base76 + (7331733501323141041/1152250000000000000000000000000000 : ℝ)*base78 + (3702783907517608959/1152250000000000000000000000000000 : ℝ)*base79 + (41496773712791/11522500000000000000000000000 : ℝ)*base81 + (223089/39062500000000000000 : ℝ)*base89 + (223089/39062500000000000000 : ℝ)*base91 + (223089/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7943133125259590549293978803/1152250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (554008071/50000000000000 : ℝ)*(base19) + (1205821361/100000000000000 : ℝ)*(base23) + (367796941/100000000000000 : ℝ)*(lower1) + (8577843/6250000000000 : ℝ)*(upper3) + (45588799/100000000000000 : ℝ)*(lower4) + (17390657/12500000000000 : ℝ)*(upper5) + (1676772404307741/50000000000000 : ℝ)*(major0) + (1676772404307741/50000000000000 : ℝ)*(major1) + (1676772404307741/50000000000000 : ℝ)*(major2) + (625094823/50000000000000 : ℝ)*(sp2) + (36276422682493/781250000000 : ℝ)*(sp4) + (2321690497671481/50000000000000 : ℝ)*(sp5) + (36276403494907/781250000000 : ℝ)*(sp6) + (515926821021419/25000000000000 : ℝ)*(sp7) + (515926821021419/25000000000000 : ℝ)*(f.failure) + (36276422682493/781250000000 : ℝ)*(f.sum) + (25991205825353/11522500000000000000000000000 : ℝ)*base65 + (87962361529874540399/2304500000000000000000000000000000 : ℝ)*base67 + (10360040454877459601/2304500000000000000000000000000000 : ℝ)*base70 + (129831111109157540399/2304500000000000000000000000000000 : ℝ)*base71 + (2047948644513/720156250000000000000000000 : ℝ)*base73 + (185729707264137459601/2304500000000000000000000000000000 : ℝ)*base76 + (18894571949744540399/2304500000000000000000000000000000 : ℝ)*base77 + (8857716734753540399/2304500000000000000000000000000000 : ℝ)*base79 + (38486650312067/11522500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (18071/4882812500000000000 : ℝ)*base90 + (18071/4882812500000000000 : ℝ)*base92 + (18071/4882812500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1501_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10873/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1501_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1501_box_0 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-417194427/2500000000 : ℝ)*x 0 + (675502797/1250000000 : ℝ)*x 1 + (5404022439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417194427/2500000000 : ℝ)^4499 ≤ (1969190723911/20000000000000 : ℝ)^3475 := by
    have hnat : (417194427 : ℕ)^4499*20000000000000^3475 ≤ 1969190723911^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417194427 2500000000 1969190723911 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675502797/1250000000 : ℝ)^4499 ≤ (45077022843397/100000000000000 : ℝ)^3475 := by
    have hnat : (675502797 : ℕ)^4499*100000000000000^3475 ≤ 45077022843397^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675502797 1250000000 45077022843397 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404022439/10000000000 : ℝ)^4499 ≤ (22538511761879/50000000000000 : ℝ)^3475 := by
    have hnat : (5404022439 : ℕ)^4499*50000000000000^3475 ≤ 22538511761879^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404022439 10000000000 22538511761879 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417194427/2500000000 : ℝ), (675502797/1250000000 : ℝ), (5404022439/10000000000 : ℝ)] ![(1969190723911/20000000000000 : ℝ), (45077022843397/100000000000000 : ℝ), (22538511761879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417194427/2500000000 : ℝ)|^4499 ≤ (1969190723911/20000000000000 : ℝ)^3475
        have hw : |(-417194427/2500000000 : ℝ)|=(417194427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675502797/1250000000 : ℝ)|^4499 ≤ (45077022843397/100000000000000 : ℝ)^3475
        have hw : |(675502797/1250000000 : ℝ)|=(675502797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404022439/10000000000 : ℝ)|^4499 ≤ (22538511761879/50000000000000 : ℝ)^3475
        have hw : |(5404022439/10000000000 : ℝ)|=(5404022439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_1 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054124091/2000000000 : ℝ)*x 0 + (-115858831/625000000 : ℝ)*x 1 + (1080804587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054124091/2000000000 : ℝ)^4499 ≤ (8728326787651/20000000000000 : ℝ)^3475 := by
    have hnat : (1054124091 : ℕ)^4499*20000000000000^3475 ≤ 8728326787651^3475*2000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054124091 2000000000 8728326787651 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115858831/625000000 : ℝ)^4499 ≤ (5640668583183/50000000000000 : ℝ)^3475 := by
    have hnat : (115858831 : ℕ)^4499*50000000000000^3475 ≤ 5640668583183^3475*625000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115858831 625000000 5640668583183 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080804587/2000000000 : ℝ)^4499 ≤ (352164288127/781250000000 : ℝ)^3475 := by
    have hnat : (1080804587 : ℕ)^4499*781250000000^3475 ≤ 352164288127^3475*2000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080804587 2000000000 352164288127 781250000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054124091/2000000000 : ℝ), (-115858831/625000000 : ℝ), (1080804587/2000000000 : ℝ)] ![(8728326787651/20000000000000 : ℝ), (5640668583183/50000000000000 : ℝ), (352164288127/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054124091/2000000000 : ℝ)|^4499 ≤ (8728326787651/20000000000000 : ℝ)^3475
        have hw : |(1054124091/2000000000 : ℝ)|=(1054124091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115858831/625000000 : ℝ)|^4499 ≤ (5640668583183/50000000000000 : ℝ)^3475
        have hw : |(-115858831/625000000 : ℝ)|=(115858831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080804587/2000000000 : ℝ)|^4499 ≤ (352164288127/781250000000 : ℝ)^3475
        have hw : |(1080804587/2000000000 : ℝ)|=(1080804587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_2 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527061953/1000000000 : ℝ)*x 0 + (5404023531/10000000000 : ℝ)*x 1 + (-926870869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527061953/1000000000 : ℝ)^4499 ≤ (21820812011063/50000000000000 : ℝ)^3475 := by
    have hnat : (527061953 : ℕ)^4499*50000000000000^3475 ≤ 21820812011063^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527061953 1000000000 21820812011063 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404023531/10000000000 : ℝ)^4499 ≤ (22538517658347/50000000000000 : ℝ)^3475 := by
    have hnat : (5404023531 : ℕ)^4499*50000000000000^3475 ≤ 22538517658347^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404023531 10000000000 22538517658347 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926870869/5000000000 : ℝ)^4499 ≤ (176270947639/1562500000000 : ℝ)^3475 := by
    have hnat : (926870869 : ℕ)^4499*1562500000000^3475 ≤ 176270947639^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926870869 5000000000 176270947639 1562500000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527061953/1000000000 : ℝ), (5404023531/10000000000 : ℝ), (-926870869/5000000000 : ℝ)] ![(21820812011063/50000000000000 : ℝ), (22538517658347/50000000000000 : ℝ), (176270947639/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527061953/1000000000 : ℝ)|^4499 ≤ (21820812011063/50000000000000 : ℝ)^3475
        have hw : |(527061953/1000000000 : ℝ)|=(527061953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404023531/10000000000 : ℝ)|^4499 ≤ (22538517658347/50000000000000 : ℝ)^3475
        have hw : |(5404023531/10000000000 : ℝ)|=(5404023531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-926870869/5000000000 : ℝ)|^4499 ≤ (176270947639/1562500000000 : ℝ)^3475
        have hw : |(-926870869/5000000000 : ℝ)|=(926870869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_3 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4478492813/10000000000 : ℝ)*x 0 + (4180192369/10000000000 : ℝ)*x 1 + (522523883/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4478492813/10000000000 : ℝ)^4499 ≤ (35345060517457/100000000000000 : ℝ)^3475 := by
    have hnat : (4478492813 : ℕ)^4499*100000000000000^3475 ≤ 35345060517457^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478492813 10000000000 35345060517457 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4180192369/10000000000 : ℝ)^4499 ≤ (4040934532961/12500000000000 : ℝ)^3475 := by
    have hnat : (4180192369 : ℕ)^4499*12500000000000^3475 ≤ 4040934532961^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180192369 10000000000 4040934532961 12500000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522523883/1250000000 : ℝ)^4499 ≤ (32327463197551/100000000000000 : ℝ)^3475 := by
    have hnat : (522523883 : ℕ)^4499*100000000000000^3475 ≤ 32327463197551^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522523883 1250000000 32327463197551 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4478492813/10000000000 : ℝ), (4180192369/10000000000 : ℝ), (522523883/1250000000 : ℝ)] ![(35345060517457/100000000000000 : ℝ), (4040934532961/12500000000000 : ℝ), (32327463197551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4478492813/10000000000 : ℝ)|^4499 ≤ (35345060517457/100000000000000 : ℝ)^3475
        have hw : |(4478492813/10000000000 : ℝ)|=(4478492813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4180192369/10000000000 : ℝ)|^4499 ≤ (4040934532961/12500000000000 : ℝ)^3475
        have hw : |(4180192369/10000000000 : ℝ)|=(4180192369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522523883/1250000000 : ℝ)|^4499 ≤ (32327463197551/100000000000000 : ℝ)^3475
        have hw : |(522523883/1250000000 : ℝ)|=(522523883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_4 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052726539/5000000000 : ℝ)*x 0 + (524325241/1000000000 : ℝ)*x 1 + (262162623/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052726539/5000000000 : ℝ)^4499 ≤ (166288257833/1250000000000 : ℝ)^3475 := by
    have hnat : (1052726539 : ℕ)^4499*1250000000000^3475 ≤ 166288257833^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052726539 5000000000 166288257833 1250000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524325241/1000000000 : ℝ)^4499 ≤ (43348469409577/100000000000000 : ℝ)^3475 := by
    have hnat : (524325241 : ℕ)^4499*100000000000000^3475 ≤ 43348469409577^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524325241 1000000000 43348469409577 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262162623/500000000 : ℝ)^4499 ≤ (21674234972381/50000000000000 : ℝ)^3475 := by
    have hnat : (262162623 : ℕ)^4499*50000000000000^3475 ≤ 21674234972381^3475*500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262162623 500000000 21674234972381 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052726539/5000000000 : ℝ), (524325241/1000000000 : ℝ), (262162623/500000000 : ℝ)] ![(166288257833/1250000000000 : ℝ), (43348469409577/100000000000000 : ℝ), (21674234972381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052726539/5000000000 : ℝ)|^4499 ≤ (166288257833/1250000000000 : ℝ)^3475
        have hw : |(-1052726539/5000000000 : ℝ)|=(1052726539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524325241/1000000000 : ℝ)|^4499 ≤ (43348469409577/100000000000000 : ℝ)^3475
        have hw : |(524325241/1000000000 : ℝ)|=(524325241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262162623/500000000 : ℝ)|^4499 ≤ (21674234972381/50000000000000 : ℝ)^3475
        have hw : |(262162623/500000000 : ℝ)|=(262162623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_5 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345661929/2500000000 : ℝ)*x 0 + (-1919885439/10000000000 : ℝ)*x 1 + (2621626229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345661929/2500000000 : ℝ)^4499 ≤ (8969264835577/20000000000000 : ℝ)^3475 := by
    have hnat : (1345661929 : ℕ)^4499*20000000000000^3475 ≤ 8969264835577^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345661929 2500000000 8969264835577 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1919885439/10000000000 : ℝ)^4499 ≤ (11805205889889/100000000000000 : ℝ)^3475 := by
    have hnat : (1919885439 : ℕ)^4499*100000000000000^3475 ≤ 11805205889889^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919885439 10000000000 11805205889889 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621626229/5000000000 : ℝ)^4499 ≤ (8669693984671/20000000000000 : ℝ)^3475 := by
    have hnat : (2621626229 : ℕ)^4499*20000000000000^3475 ≤ 8669693984671^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621626229 5000000000 8669693984671 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345661929/2500000000 : ℝ), (-1919885439/10000000000 : ℝ), (2621626229/5000000000 : ℝ)] ![(8969264835577/20000000000000 : ℝ), (11805205889889/100000000000000 : ℝ), (8669693984671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345661929/2500000000 : ℝ)|^4499 ≤ (8969264835577/20000000000000 : ℝ)^3475
        have hw : |(1345661929/2500000000 : ℝ)|=(1345661929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1919885439/10000000000 : ℝ)|^4499 ≤ (11805205889889/100000000000000 : ℝ)^3475
        have hw : |(-1919885439/10000000000 : ℝ)|=(1919885439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621626229/5000000000 : ℝ)|^4499 ≤ (8669693984671/20000000000000 : ℝ)^3475
        have hw : |(2621626229/5000000000 : ℝ)|=(2621626229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_6 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691323983/5000000000 : ℝ)*x 0 + (655406527/1250000000 : ℝ)*x 1 + (-119992839/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691323983/5000000000 : ℝ)^4499 ≤ (22423163437291/50000000000000 : ℝ)^3475 := by
    have hnat : (2691323983 : ℕ)^4499*50000000000000^3475 ≤ 22423163437291^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691323983 5000000000 22423163437291 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655406527/1250000000 : ℝ)^4499 ≤ (21674233666529/50000000000000 : ℝ)^3475 := by
    have hnat : (655406527 : ℕ)^4499*50000000000000^3475 ≤ 21674233666529^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655406527 1250000000 21674233666529 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119992839/625000000 : ℝ)^4499 ≤ (2951301442619/25000000000000 : ℝ)^3475 := by
    have hnat : (119992839 : ℕ)^4499*25000000000000^3475 ≤ 2951301442619^3475*625000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119992839 625000000 2951301442619 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691323983/5000000000 : ℝ), (655406527/1250000000 : ℝ), (-119992839/625000000 : ℝ)] ![(22423163437291/50000000000000 : ℝ), (21674233666529/50000000000000 : ℝ), (2951301442619/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691323983/5000000000 : ℝ)|^4499 ≤ (22423163437291/50000000000000 : ℝ)^3475
        have hw : |(2691323983/5000000000 : ℝ)|=(2691323983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655406527/1250000000 : ℝ)|^4499 ≤ (21674233666529/50000000000000 : ℝ)^3475
        have hw : |(655406527/1250000000 : ℝ)|=(655406527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-119992839/625000000 : ℝ)|^4499 ≤ (2951301442619/25000000000000 : ℝ)^3475
        have hw : |(-119992839/625000000 : ℝ)|=(119992839/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_7 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (508623351/1250000000 : ℝ)*x 0 + (4384809031/10000000000 : ℝ)*x 1 + (438480891/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508623351/1250000000 : ℝ)^4499 ≤ (15609218666973/50000000000000 : ℝ)^3475 := by
    have hnat : (508623351 : ℕ)^4499*50000000000000^3475 ≤ 15609218666973^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508623351 1250000000 15609218666973 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4384809031/10000000000 : ℝ)^4499 ≤ (8597695484737/25000000000000 : ℝ)^3475 := by
    have hnat : (4384809031 : ℕ)^4499*25000000000000^3475 ≤ 8597695484737^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384809031 10000000000 8597695484737 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438480891/1000000000 : ℝ)^4499 ≤ (3439078071027/10000000000000 : ℝ)^3475 := by
    have hnat : (438480891 : ℕ)^4499*10000000000000^3475 ≤ 3439078071027^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438480891 1000000000 3439078071027 10000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(508623351/1250000000 : ℝ), (4384809031/10000000000 : ℝ), (438480891/1000000000 : ℝ)] ![(15609218666973/50000000000000 : ℝ), (8597695484737/25000000000000 : ℝ), (3439078071027/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(508623351/1250000000 : ℝ)|^4499 ≤ (15609218666973/50000000000000 : ℝ)^3475
        have hw : |(508623351/1250000000 : ℝ)|=(508623351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4384809031/10000000000 : ℝ)|^4499 ≤ (8597695484737/25000000000000 : ℝ)^3475
        have hw : |(4384809031/10000000000 : ℝ)|=(4384809031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(438480891/1000000000 : ℝ)|^4499 ≤ (3439078071027/10000000000000 : ℝ)^3475
        have hw : |(438480891/1000000000 : ℝ)|=(438480891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_8 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2013232593/10000000000 : ℝ)*x 0 + (1026148679/2000000000 : ℝ)*x 1 + (1356126913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013232593/10000000000 : ℝ)^4499 ≤ (12553592496819/100000000000000 : ℝ)^3475 := by
    have hnat : (2013232593 : ℕ)^4499*100000000000000^3475 ≤ 12553592496819^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013232593 10000000000 12553592496819 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026148679/2000000000 : ℝ)^4499 ≤ (42148032688507/100000000000000 : ℝ)^3475 := by
    have hnat : (1026148679 : ℕ)^4499*100000000000000^3475 ≤ 42148032688507^3475*2000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026148679 2000000000 42148032688507 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356126913/2500000000 : ℝ)^4499 ≤ (11324593700549/25000000000000 : ℝ)^3475 := by
    have hnat : (1356126913 : ℕ)^4499*25000000000000^3475 ≤ 11324593700549^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356126913 2500000000 11324593700549 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2013232593/10000000000 : ℝ), (1026148679/2000000000 : ℝ), (1356126913/2500000000 : ℝ)] ![(12553592496819/100000000000000 : ℝ), (42148032688507/100000000000000 : ℝ), (11324593700549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2013232593/10000000000 : ℝ)|^4499 ≤ (12553592496819/100000000000000 : ℝ)^3475
        have hw : |(-2013232593/10000000000 : ℝ)|=(2013232593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026148679/2000000000 : ℝ)|^4499 ≤ (42148032688507/100000000000000 : ℝ)^3475
        have hw : |(1026148679/2000000000 : ℝ)|=(1026148679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356126913/2500000000 : ℝ)|^4499 ≤ (11324593700549/25000000000000 : ℝ)^3475
        have hw : |(1356126913/2500000000 : ℝ)|=(1356126913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_9 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628169899/5000000000 : ℝ)*x 0 + (-1845065263/10000000000 : ℝ)*x 1 + (1356126799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628169899/5000000000 : ℝ)^4499 ≤ (43488604455119/100000000000000 : ℝ)^3475 := by
    have hnat : (2628169899 : ℕ)^4499*100000000000000^3475 ≤ 43488604455119^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628169899 5000000000 43488604455119 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1845065263/10000000000 : ℝ)^4499 ≤ (11213025651307/100000000000000 : ℝ)^3475 := by
    have hnat : (1845065263 : ℕ)^4499*100000000000000^3475 ≤ 11213025651307^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845065263 10000000000 11213025651307 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356126799/2500000000 : ℝ)^4499 ≤ (2264918493609/5000000000000 : ℝ)^3475 := by
    have hnat : (1356126799 : ℕ)^4499*5000000000000^3475 ≤ 2264918493609^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356126799 2500000000 2264918493609 5000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628169899/5000000000 : ℝ), (-1845065263/10000000000 : ℝ), (1356126799/2500000000 : ℝ)] ![(43488604455119/100000000000000 : ℝ), (11213025651307/100000000000000 : ℝ), (2264918493609/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628169899/5000000000 : ℝ)|^4499 ≤ (43488604455119/100000000000000 : ℝ)^3475
        have hw : |(2628169899/5000000000 : ℝ)|=(2628169899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1845065263/10000000000 : ℝ)|^4499 ≤ (11213025651307/100000000000000 : ℝ)^3475
        have hw : |(-1845065263/10000000000 : ℝ)|=(1845065263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356126799/2500000000 : ℝ)|^4499 ≤ (2264918493609/5000000000000 : ℝ)^3475
        have hw : |(1356126799/2500000000 : ℝ)|=(1356126799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_10 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105126779/200000000 : ℝ)*x 0 + (108490181/200000000 : ℝ)*x 1 + (-1845063871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105126779/200000000 : ℝ)^4499 ≤ (21744297685853/50000000000000 : ℝ)^3475 := by
    have hnat : (105126779 : ℕ)^4499*50000000000000^3475 ≤ 21744297685853^3475*200000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105126779 200000000 21744297685853 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108490181/200000000 : ℝ)^4499 ≤ (11324597479147/25000000000000 : ℝ)^3475 := by
    have hnat : (108490181 : ℕ)^4499*25000000000000^3475 ≤ 11324597479147^3475*200000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108490181 200000000 11324597479147 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1845063871/10000000000 : ℝ)^4499 ≤ (11213014698853/100000000000000 : ℝ)^3475 := by
    have hnat : (1845063871 : ℕ)^4499*100000000000000^3475 ≤ 11213014698853^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845063871 10000000000 11213014698853 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105126779/200000000 : ℝ), (108490181/200000000 : ℝ), (-1845063871/10000000000 : ℝ)] ![(21744297685853/50000000000000 : ℝ), (11324597479147/25000000000000 : ℝ), (11213014698853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105126779/200000000 : ℝ)|^4499 ≤ (21744297685853/50000000000000 : ℝ)^3475
        have hw : |(105126779/200000000 : ℝ)|=(105126779/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108490181/200000000 : ℝ)|^4499 ≤ (11324597479147/25000000000000 : ℝ)^3475
        have hw : |(108490181/200000000 : ℝ)|=(108490181/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1845063871/10000000000 : ℝ)|^4499 ≤ (11213014698853/100000000000000 : ℝ)^3475
        have hw : |(-1845063871/10000000000 : ℝ)|=(1845063871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_11 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4529520741/10000000000 : ℝ)*x 0 + (415408697/1000000000 : ℝ)*x 1 + (830817233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4529520741/10000000000 : ℝ)^4499 ≤ (7173465481803/20000000000000 : ℝ)^3475 := by
    have hnat : (4529520741 : ℕ)^4499*20000000000000^3475 ≤ 7173465481803^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529520741 10000000000 7173465481803 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415408697/1000000000 : ℝ)^4499 ≤ (16033170154263/50000000000000 : ℝ)^3475 := by
    have hnat : (415408697 : ℕ)^4499*50000000000000^3475 ≤ 16033170154263^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415408697 1000000000 16033170154263 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830817233/2000000000 : ℝ)^4499 ≤ (8016583065859/25000000000000 : ℝ)^3475 := by
    have hnat : (830817233 : ℕ)^4499*25000000000000^3475 ≤ 8016583065859^3475*2000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830817233 2000000000 8016583065859 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4529520741/10000000000 : ℝ), (415408697/1000000000 : ℝ), (830817233/2000000000 : ℝ)] ![(7173465481803/20000000000000 : ℝ), (16033170154263/50000000000000 : ℝ), (8016583065859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4529520741/10000000000 : ℝ)|^4499 ≤ (7173465481803/20000000000000 : ℝ)^3475
        have hw : |(4529520741/10000000000 : ℝ)|=(4529520741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(415408697/1000000000 : ℝ)|^4499 ≤ (16033170154263/50000000000000 : ℝ)^3475
        have hw : |(415408697/1000000000 : ℝ)|=(415408697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830817233/2000000000 : ℝ)|^4499 ≤ (8016583065859/25000000000000 : ℝ)^3475
        have hw : |(830817233/2000000000 : ℝ)|=(830817233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_12 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-880503979/5000000000 : ℝ)*x 0 + (2756438409/5000000000 : ℝ)*x 1 + (1307058959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880503979/5000000000 : ℝ)^4499 ≤ (1055613864197/10000000000000 : ℝ)^3475 := by
    have hnat : (880503979 : ℕ)^4499*10000000000000^3475 ≤ 1055613864197^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880503979 5000000000 1055613864197 10000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756438409/5000000000 : ℝ)^4499 ≤ (9251211412931/20000000000000 : ℝ)^3475 := by
    have hnat : (2756438409 : ℕ)^4499*20000000000000^3475 ≤ 9251211412931^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756438409 5000000000 9251211412931 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307058959/2500000000 : ℝ)^4499 ≤ (8637560856327/20000000000000 : ℝ)^3475 := by
    have hnat : (1307058959 : ℕ)^4499*20000000000000^3475 ≤ 8637560856327^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307058959 2500000000 8637560856327 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-880503979/5000000000 : ℝ), (2756438409/5000000000 : ℝ), (1307058959/2500000000 : ℝ)] ![(1055613864197/10000000000000 : ℝ), (9251211412931/20000000000000 : ℝ), (8637560856327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-880503979/5000000000 : ℝ)|^4499 ≤ (1055613864197/10000000000000 : ℝ)^3475
        have hw : |(-880503979/5000000000 : ℝ)|=(880503979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756438409/5000000000 : ℝ)|^4499 ≤ (9251211412931/20000000000000 : ℝ)^3475
        have hw : |(2756438409/5000000000 : ℝ)|=(2756438409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307058959/2500000000 : ℝ)|^4499 ≤ (8637560856327/20000000000000 : ℝ)^3475
        have hw : |(1307058959/2500000000 : ℝ)|=(1307058959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_13 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215724453/400000000 : ℝ)*x 0 + (-1925883709/10000000000 : ℝ)*x 1 + (326764689/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215724453/400000000 : ℝ)^4499 ≤ (1404975787691/3125000000000 : ℝ)^3475 := by
    have hnat : (215724453 : ℕ)^4499*3125000000000^3475 ≤ 1404975787691^3475*400000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215724453 400000000 1404975787691 3125000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1925883709/10000000000 : ℝ)^4499 ≤ (11852979182067/100000000000000 : ℝ)^3475 := by
    have hnat : (1925883709 : ℕ)^4499*100000000000000^3475 ≤ 11852979182067^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925883709 10000000000 11852979182067 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326764689/625000000 : ℝ)^4499 ≤ (168702326553/390625000000 : ℝ)^3475 := by
    have hnat : (326764689 : ℕ)^4499*390625000000^3475 ≤ 168702326553^3475*625000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326764689 625000000 168702326553 390625000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215724453/400000000 : ℝ), (-1925883709/10000000000 : ℝ), (326764689/625000000 : ℝ)] ![(1404975787691/3125000000000 : ℝ), (11852979182067/100000000000000 : ℝ), (168702326553/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215724453/400000000 : ℝ)|^4499 ≤ (1404975787691/3125000000000 : ℝ)^3475
        have hw : |(215724453/400000000 : ℝ)|=(215724453/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1925883709/10000000000 : ℝ)|^4499 ≤ (11852979182067/100000000000000 : ℝ)^3475
        have hw : |(-1925883709/10000000000 : ℝ)|=(1925883709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326764689/625000000 : ℝ)|^4499 ≤ (168702326553/390625000000 : ℝ)^3475
        have hw : |(326764689/625000000 : ℝ)|=(326764689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_14 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696555483/5000000000 : ℝ)*x 0 + (261411789/500000000 : ℝ)*x 1 + (-1925883181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696555483/5000000000 : ℝ)^4499 ≤ (44959221331439/100000000000000 : ℝ)^3475 := by
    have hnat : (2696555483 : ℕ)^4499*100000000000000^3475 ≤ 44959221331439^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696555483 5000000000 44959221331439 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261411789/500000000 : ℝ)^4499 ≤ (21593901841367/50000000000000 : ℝ)^3475 := by
    have hnat : (261411789 : ℕ)^4499*50000000000000^3475 ≤ 21593901841367^3475*500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261411789 500000000 21593901841367 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925883181/10000000000 : ℝ)^4499 ≤ (11852974974873/100000000000000 : ℝ)^3475 := by
    have hnat : (1925883181 : ℕ)^4499*100000000000000^3475 ≤ 11852974974873^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925883181 10000000000 11852974974873 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696555483/5000000000 : ℝ), (261411789/500000000 : ℝ), (-1925883181/10000000000 : ℝ)] ![(44959221331439/100000000000000 : ℝ), (21593901841367/50000000000000 : ℝ), (11852974974873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696555483/5000000000 : ℝ)|^4499 ≤ (44959221331439/100000000000000 : ℝ)^3475
        have hw : |(2696555483/5000000000 : ℝ)|=(2696555483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261411789/500000000 : ℝ)|^4499 ≤ (21593901841367/50000000000000 : ℝ)^3475
        have hw : |(261411789/500000000 : ℝ)|=(261411789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1925883181/10000000000 : ℝ)|^4499 ≤ (11852974974873/100000000000000 : ℝ)^3475
        have hw : |(-1925883181/10000000000 : ℝ)|=(1925883181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_box_15 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1007469197/2500000000 : ℝ)*x 0 + (1100974811/2500000000 : ℝ)*x 1 + (4403897867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007469197/2500000000 : ℝ)^4499 ≤ (7707625970643/25000000000000 : ℝ)^3475 := by
    have hnat : (1007469197 : ℕ)^4499*25000000000000^3475 ≤ 7707625970643^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007469197 2500000000 7707625970643 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100974811/2500000000 : ℝ)^4499 ≤ (2161547190801/6250000000000 : ℝ)^3475 := by
    have hnat : (1100974811 : ℕ)^4499*6250000000000^3475 ≤ 2161547190801^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100974811 2500000000 2161547190801 6250000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4403897867/10000000000 : ℝ)^4499 ≤ (540386578943/1562500000000 : ℝ)^3475 := by
    have hnat : (4403897867 : ℕ)^4499*1562500000000^3475 ≤ 540386578943^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403897867 10000000000 540386578943 1562500000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1007469197/2500000000 : ℝ), (1100974811/2500000000 : ℝ), (4403897867/10000000000 : ℝ)] ![(7707625970643/25000000000000 : ℝ), (2161547190801/6250000000000 : ℝ), (540386578943/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1007469197/2500000000 : ℝ)|^4499 ≤ (7707625970643/25000000000000 : ℝ)^3475
        have hw : |(1007469197/2500000000 : ℝ)|=(1007469197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100974811/2500000000 : ℝ)|^4499 ≤ (2161547190801/6250000000000 : ℝ)^3475
        have hw : |(1100974811/2500000000 : ℝ)|=(1100974811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4403897867/10000000000 : ℝ)|^4499 ≤ (540386578943/1562500000000 : ℝ)^3475
        have hw : |(4403897867/10000000000 : ℝ)|=(4403897867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1501_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10873/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2549/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3661/6250 : ℝ) ∧ (401/500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85931/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10873/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10873/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10873/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10873/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10873/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10873/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10873/100000 : ℝ) ^ (4497/1024 : ℝ) ≤ (5861792849233809/100000000000000000000 : ℝ) := by
    have hpowers : (10873/100000 : ℝ)^4497 ≤ (5861792849233809/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10873 : ℕ)^4497*100000000000000000000^1024 ≤ 5861792849233809^1024*100000^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10873 100000 5861792849233809 100000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10873/100000 : ℝ)) (X := (5861792849233809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4497/1024 : ℝ) ≤ (13828238783283829/50000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4497 ≤ (13828238783283829/50000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4497*50000000000000000000^1024 ≤ 13828238783283829^1024*2500^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 13828238783283829 50000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (13828238783283829/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005861792849233809/50000000000000000000 : ℝ) ≤ (10000266942591203/10000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (50005861792849233809/50000000000000000000 : ℝ)^1024 ≤ (10000266942591203/10000000000000000 : ℝ)^4497 := by
      have hnat : (50005861792849233809 : ℕ)^1024*10000000000000000^4497 ≤ 10000266942591203^4497*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005861792849233809 50000000000000000000 10000266942591203 10000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000266942591203/10000000000000000 : ℝ)) (X := (50005861792849233809/50000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033518270415801467/100000000000000000000 : ℝ) ≤ (10000763136922657/10000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (100033518270415801467/100000000000000000000 : ℝ)^1024 ≤ (10000763136922657/10000000000000000 : ℝ)^4497 := by
      have hnat : (100033518270415801467 : ℕ)^1024*10000000000000000^4497 ≤ 10000763136922657^4497*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033518270415801467 100000000000000000000 10000763136922657 10000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000763136922657/10000000000000000 : ℝ)) (X := (100033518270415801467/100000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013828238783283829/25000000000000000000 : ℝ) ≤ (10001259331254111/10000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (25013828238783283829/25000000000000000000 : ℝ)^1024 ≤ (10001259331254111/10000000000000000 : ℝ)^4497 := by
      have hnat : (25013828238783283829 : ℕ)^1024*10000000000000000^4497 ≤ 10001259331254111^4497*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013828238783283829 25000000000000000000 10001259331254111 10000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001259331254111/10000000000000000 : ℝ)) (X := (25013828238783283829/25000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5861792849233809/100000000000000000000 : ℝ) ≤ ((46060439562585873537/46070000000000000000 : ℝ)+2*(248097165727/230350000000000 : ℝ)*(10873/100000 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (46060439562585873537/46070000000000000000 : ℝ)+2*(248097165727/230350000000000 : ℝ)*(10873/100000 : ℝ)=(10000266942591203/10000000000000000 : ℝ) by norm_num, show 1+2*(5861792849233809/100000000000000000000 : ℝ)=(50005861792849233809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13828238783283829/50000000000000000000 : ℝ)+(5861792849233809/100000000000000000000 : ℝ) ≤ ((46060439562585873537/46070000000000000000 : ℝ)+(248097165727/230350000000000 : ℝ)*((387/2500 : ℝ)+(10873/100000 : ℝ)))^(4497/1024 : ℝ) := by
    rw [show (46060439562585873537/46070000000000000000 : ℝ)+(248097165727/230350000000000 : ℝ)*((387/2500 : ℝ)+(10873/100000 : ℝ))=(10000763136922657/10000000000000000 : ℝ) by norm_num, show 1+(13828238783283829/50000000000000000000 : ℝ)+(5861792849233809/100000000000000000000 : ℝ)=(100033518270415801467/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13828238783283829/50000000000000000000 : ℝ) ≤ ((46060439562585873537/46070000000000000000 : ℝ)+2*(248097165727/230350000000000 : ℝ)*(387/2500 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (46060439562585873537/46070000000000000000 : ℝ)+2*(248097165727/230350000000000 : ℝ)*(387/2500 : ℝ)=(10001259331254111/10000000000000000 : ℝ) by norm_num, show 1+2*(13828238783283829/50000000000000000000 : ℝ)=(25013828238783283829/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46060439562585873537/46070000000000000000 : ℝ)*(X 1 0+X 2 0)+(248097165727/230350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (10873/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46060439562585873537/46070000000000000000 : ℝ)) (alpha := (248097165727/230350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46060439562585873537/46070000000000000000 : ℝ)*(X 0 1+X 2 1)+(248097165727/230350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (10873/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46060439562585873537/46070000000000000000 : ℝ)) (alpha := (248097165727/230350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46060439562585873537/46070000000000000000 : ℝ)*(X 0 2+X 1 2)+(248097165727/230350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (10873/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46060439562585873537/46070000000000000000 : ℝ)) (alpha := (248097165727/230350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-417194427/2500000000 : ℝ)*X 0 0+(675502797/1250000000 : ℝ)*X 0 1+(5404022439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054124091/2000000000 : ℝ)*X 1 0+(-115858831/625000000 : ℝ)*X 1 1+(1080804587/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((527061953/1000000000 : ℝ)*X 2 0+(5404023531/10000000000 : ℝ)*X 2 1+(-926870869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4478492813/10000000000 : ℝ)*X 0 0+(4180192369/10000000000 : ℝ)*X 0 1+(522523883/1250000000 : ℝ)*X 0 2+(4478492813/10000000000 : ℝ)*X 1 0+(4180192369/10000000000 : ℝ)*X 1 1+(522523883/1250000000 : ℝ)*X 1 2+(4478492813/10000000000 : ℝ)*X 2 0+(4180192369/10000000000 : ℝ)*X 2 1+(522523883/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1052726539/5000000000 : ℝ)*X 0 0+(524325241/1000000000 : ℝ)*X 0 1+(262162623/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345661929/2500000000 : ℝ)*X 1 0+(-1919885439/10000000000 : ℝ)*X 1 1+(2621626229/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2691323983/5000000000 : ℝ)*X 2 0+(655406527/1250000000 : ℝ)*X 2 1+(-119992839/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((508623351/1250000000 : ℝ)*X 0 0+(4384809031/10000000000 : ℝ)*X 0 1+(438480891/1000000000 : ℝ)*X 0 2+(508623351/1250000000 : ℝ)*X 1 0+(4384809031/10000000000 : ℝ)*X 1 1+(438480891/1000000000 : ℝ)*X 1 2+(508623351/1250000000 : ℝ)*X 2 0+(4384809031/10000000000 : ℝ)*X 2 1+(438480891/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2013232593/10000000000 : ℝ)*X 0 0+(1026148679/2000000000 : ℝ)*X 0 1+(1356126913/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628169899/5000000000 : ℝ)*X 1 0+(-1845065263/10000000000 : ℝ)*X 1 1+(1356126799/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((105126779/200000000 : ℝ)*X 2 0+(108490181/200000000 : ℝ)*X 2 1+(-1845063871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4529520741/10000000000 : ℝ)*X 0 0+(415408697/1000000000 : ℝ)*X 0 1+(830817233/2000000000 : ℝ)*X 0 2+(4529520741/10000000000 : ℝ)*X 1 0+(415408697/1000000000 : ℝ)*X 1 1+(830817233/2000000000 : ℝ)*X 1 2+(4529520741/10000000000 : ℝ)*X 2 0+(415408697/1000000000 : ℝ)*X 2 1+(830817233/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-880503979/5000000000 : ℝ)*X 0 0+(2756438409/5000000000 : ℝ)*X 0 1+(1307058959/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((215724453/400000000 : ℝ)*X 1 0+(-1925883709/10000000000 : ℝ)*X 1 1+(326764689/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2696555483/5000000000 : ℝ)*X 2 0+(261411789/500000000 : ℝ)*X 2 1+(-1925883181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1007469197/2500000000 : ℝ)*X 0 0+(1100974811/2500000000 : ℝ)*X 0 1+(4403897867/10000000000 : ℝ)*X 0 2+(1007469197/2500000000 : ℝ)*X 1 0+(1100974811/2500000000 : ℝ)*X 1 1+(4403897867/10000000000 : ℝ)*X 1 2+(1007469197/2500000000 : ℝ)*X 2 0+(1100974811/2500000000 : ℝ)*X 2 1+(4403897867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2549/4000 : ℝ) ≤ (-14678571532693732691734445379/23035000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267713/50000000000000 : ℝ)*(upper1) + (21252869/100000000000000 : ℝ)*(lower2) + (983699/5000000000000 : ℝ)*(upper4) + (2493689/25000000000000 : ℝ)*(upper5) + (2207128554639661/100000000000000 : ℝ)*(major0) + (2207128554639661/100000000000000 : ℝ)*(major1) + (2207128554639661/100000000000000 : ℝ)*(major2) + (173211267/25000000000000 : ℝ)*(sp1) + (1953376379/50000000000000 : ℝ)*(sp2) + (12020596885753/390625000000 : ℝ)*(sp4) + (769318180008747/25000000000000 : ℝ)*(sp5) + (1538634753063649/50000000000000 : ℝ)*(sp6) + (1358224665262143/100000000000000 : ℝ)*(sp7) + (76265911/12500000000000 : ℝ)*(sp8) + (1358224665262143/100000000000000 : ℝ)*(f.failure) + (384659176610007/12500000000000 : ℝ)*(f.sum) + (29508195352933/11517500000000000000000000000 : ℝ)*base66 + (11109756427651049043/4607000000000000000000000000000000 : ℝ)*base68 + (1403020903757950957/4607000000000000000000000000000000 : ℝ)*base69 + (10592923905784049043/4607000000000000000000000000000000 : ℝ)*base72 + (148983124076961/23035000000000000000000000000 : ℝ)*base74 + (28601531751238049043/4607000000000000000000000000000000 : ℝ)*base76 + (2454163394395950957/4607000000000000000000000000000000 : ℝ)*base77 + (5556954182166950957/4607000000000000000000000000000000 : ℝ)*base79 + (43848941144499/5758750000000000000000000000 : ℝ)*base82 + (605827/78125000000000000000 : ℝ)*base89 + (605827/78125000000000000000 : ℝ)*base91 + (605827/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (3661/6250 : ℝ) ≤ (168669366126402612642907988549601/287937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43857623/25000000000000 : ℝ)*(lower0) + (67471179/100000000000000 : ℝ)*(upper1) + (119621473/50000000000000 : ℝ)*(upper2) + (54765549/50000000000000 : ℝ)*(upper3) + (285327549317803/12500000000000 : ℝ)*(major0) + (285327549317803/12500000000000 : ℝ)*(major1) + (285327549317803/12500000000000 : ℝ)*(major2) + (1570516867867177/50000000000000 : ℝ)*(sp0) + (1570513330670637/50000000000000 : ℝ)*(sp1) + (785255520495571/25000000000000 : ℝ)*(sp2) + (702330208319283/50000000000000 : ℝ)*(sp3) + (7074393079/100000000000000 : ℝ)*(sp5) + (1165375207/10000000000000 : ℝ)*(sp6) + (10240944689/50000000000000 : ℝ)*(sp11) + (175585112315993/12500000000000 : ℝ)*(f.failure) + (1570516867867177/50000000000000 : ℝ)*(f.sum) + (9312963190041/1439687500000000000000000000 : ℝ)*base65 + (982873915346129211/575875000000000000000000000000000 : ℝ)*base67 + (4536606382611879211/575875000000000000000000000000000 : ℝ)*base69 + (6728885634058129211/575875000000000000000000000000000 : ℝ)*base71 + (54961642453019/23035000000000000000000000000 : ℝ)*base74 + (11606112400191629211/575875000000000000000000000000000 : ℝ)*base75 + (8011659344065379211/575875000000000000000000000000000 : ℝ)*base77 + (1100751600378629211/575875000000000000000000000000000 : ℝ)*base79 + (28574245533613/11517500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (156523/9765625000000000000 : ℝ)*base90 + (156523/9765625000000000000 : ℝ)*base92 + (156523/9765625000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (401/500 : ℝ) ≤ (1847469396109591690110882951/2303500000000000000000000000 : ℝ) := by norm_num
    linear_combination (38133181/100000000000000 : ℝ)*(upper1) + (114704381/100000000000000 : ℝ)*(lower3) + (241416569/100000000000000 : ℝ)*(upper4) + (47587387/100000000000000 : ℝ)*(lower5) + (19822539715933/800000000000 : ℝ)*(major0) + (19822539715933/800000000000 : ℝ)*(major1) + (19822539715933/800000000000 : ℝ)*(major2) + (1166384359/100000000000000 : ℝ)*(sp0) + (371192336387/100000000000000 : ℝ)*(sp2) + (90279394351/100000000000000 : ℝ)*(sp3) + (1662157269187/48828125000 : ℝ)*(sp8) + (1702049626839667/50000000000000 : ℝ)*(sp9) + (850932015335737/25000000000000 : ℝ)*(sp10) + (1524711159658787/100000000000000 : ℝ)*(sp11) + (762400719526569/50000000000000 : ℝ)*(f.failure) + (1702049626839667/50000000000000 : ℝ)*(f.sum) + (181244902479/230350000000000000000000000 : ℝ)*base66 + (10537241950637021/36856000000000000000000000000000 : ℝ)*base67 + (310977395668666979/36856000000000000000000000000000 : ℝ)*base70 + (105072084055093021/36856000000000000000000000000000 : ℝ)*base71 + (7376804639881/4607000000000000000000000000 : ℝ)*base73 + (170667887153917021/36856000000000000000000000000000 : ℝ)*base75 + (16468985673274979/36856000000000000000000000000000 : ℝ)*base78 + (71065678989770979/36856000000000000000000000000000 : ℝ)*base80 + (2722510694297/921400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (66967/19531250000000000000 : ℝ)*base90 + (66967/19531250000000000000 : ℝ)*base92 + (66967/19531250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-85931/100000 : ℝ) ≤ (-494839772238206461275028600113249/575875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8825459/25000000000000 : ℝ)*(upper1) + (178422283/100000000000000 : ℝ)*(lower2) + (94518907/50000000000000 : ℝ)*(upper3) + (22008409/100000000000000 : ℝ)*(upper5) + (629153763366753/25000000000000 : ℝ)*(major0) + (629153763366753/25000000000000 : ℝ)*(major1) + (629153763366753/25000000000000 : ℝ)*(major2) + (146165951623/50000000000000 : ℝ)*(sp5) + (1279412503/100000000000000 : ℝ)*(sp6) + (4775040867/10000000000000 : ℝ)*(sp7) + (3513196151034681/100000000000000 : ℝ)*(sp12) + (702580763826287/20000000000000 : ℝ)*(sp13) + (1756597435811089/50000000000000 : ℝ)*(sp14) + (1548628982264451/100000000000000 : ℝ)*(sp15) + (774338366336561/50000000000000 : ℝ)*(f.failure) + (3513196151034681/100000000000000 : ℝ)*(f.sum) + (87852211769099/11517500000000000000000000000 : ℝ)*base65 + (16249449725668515361/1151750000000000000000000000000000 : ℝ)*base67 + (13553657731486765361/1151750000000000000000000000000000 : ℝ)*base69 + (10382806795191265361/1151750000000000000000000000000000 : ℝ)*base71 + (209131685556273/23035000000000000000000000000 : ℝ)*base73 + (3820184168550765361/1151750000000000000000000000000000 : ℝ)*base75 + (18961460798105015361/1151750000000000000000000000000000 : ℝ)*base77 + (5198338875416015361/1151750000000000000000000000000000 : ℝ)*base79 + (53031603318497/23035000000000000000000000000 : ℝ)*base82 + (247121/39062500000000000000 : ℝ)*base90 + (247121/39062500000000000000 : ℝ)*base92 + (247121/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1501_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10873/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2549/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(3661/6250 : ℝ) else (401/500 : ℝ) ≤ X j i ∧ X j i ≤ (85931/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1501_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1501_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2549/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(3661/6250 : ℝ) else (401/500 : ℝ) ≤ X j i ∧ X j i ≤ (85931/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1501_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1501_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2549/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(3661/6250 : ℝ) else (401/500 : ℝ) ≤ X j i ∧ X j i ≤ (85931/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1501_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

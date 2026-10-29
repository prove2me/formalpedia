-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1620_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:50.27688+00:00
-- url     : https://prove2.me/submissions/1d03dd2e-3991-4e70-ae46-1ccbd7612f3a

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
theorem support_rectangle_w1620_s0_0 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-193348829/1250000000 : ℝ)*x 0 + (2911865057/5000000000 : ℝ)*x 1 + (153137853/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193348829/1250000000 : ℝ)^4799 ≤ (1165381553581/12500000000000 : ℝ)^3775 := by
    have hnat : (193348829 : ℕ)^4799*12500000000000^3775 ≤ 1165381553581^3775*1250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193348829 1250000000 1165381553581 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2911865057/5000000000 : ℝ)^4799 ≤ (50293300051953/100000000000000 : ℝ)^3775 := by
    have hnat : (2911865057 : ℕ)^4799*100000000000000^3775 ≤ 50293300051953^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2911865057 5000000000 50293300051953 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153137853/312500000 : ℝ)^4799 ≤ (2019182374961/5000000000000 : ℝ)^3775 := by
    have hnat : (153137853 : ℕ)^4799*5000000000000^3775 ≤ 2019182374961^3775*312500000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153137853 312500000 2019182374961 5000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-193348829/1250000000 : ℝ), (2911865057/5000000000 : ℝ), (153137853/312500000 : ℝ)] ![(1165381553581/12500000000000 : ℝ), (50293300051953/100000000000000 : ℝ), (2019182374961/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-193348829/1250000000 : ℝ)|^4799 ≤ (1165381553581/12500000000000 : ℝ)^3775
        have hw : |(-193348829/1250000000 : ℝ)|=(193348829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2911865057/5000000000 : ℝ)|^4799 ≤ (50293300051953/100000000000000 : ℝ)^3775
        have hw : |(2911865057/5000000000 : ℝ)|=(2911865057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153137853/312500000 : ℝ)|^4799 ≤ (2019182374961/5000000000000 : ℝ)^3775
        have hw : |(153137853/312500000 : ℝ)|=(153137853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s0_1 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544961409/1000000000 : ℝ)*x 0 + (-514216753/2500000000 : ℝ)*x 1 + (1225102867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544961409/1000000000 : ℝ)^4799 ≤ (23111215148431/50000000000000 : ℝ)^3775 := by
    have hnat : (544961409 : ℕ)^4799*50000000000000^3775 ≤ 23111215148431^3775*1000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544961409 1000000000 23111215148431 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514216753/2500000000 : ℝ)^4799 ≤ (13393920379407/100000000000000 : ℝ)^3775 := by
    have hnat : (514216753 : ℕ)^4799*100000000000000^3775 ≤ 13393920379407^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514216753 2500000000 13393920379407 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1225102867/2500000000 : ℝ)^4799 ≤ (40383649301139/100000000000000 : ℝ)^3775 := by
    have hnat : (1225102867 : ℕ)^4799*100000000000000^3775 ≤ 40383649301139^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225102867 2500000000 40383649301139 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544961409/1000000000 : ℝ), (-514216753/2500000000 : ℝ), (1225102867/2500000000 : ℝ)] ![(23111215148431/50000000000000 : ℝ), (13393920379407/100000000000000 : ℝ), (40383649301139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544961409/1000000000 : ℝ)|^4799 ≤ (23111215148431/50000000000000 : ℝ)^3775
        have hw : |(544961409/1000000000 : ℝ)|=(544961409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514216753/2500000000 : ℝ)|^4799 ≤ (13393920379407/100000000000000 : ℝ)^3775
        have hw : |(-514216753/2500000000 : ℝ)|=(514216753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1225102867/2500000000 : ℝ)|^4799 ≤ (40383649301139/100000000000000 : ℝ)^3775
        have hw : |(1225102867/2500000000 : ℝ)|=(1225102867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s0_2 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5449613857/10000000000 : ℝ)*x 0 + (4900411447/10000000000 : ℝ)*x 1 + (-2056867343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5449613857/10000000000 : ℝ)^4799 ≤ (11555606946133/25000000000000 : ℝ)^3775 := by
    have hnat : (5449613857 : ℕ)^4799*25000000000000^3775 ≤ 11555606946133^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449613857 10000000000 11555606946133 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4900411447/10000000000 : ℝ)^4799 ≤ (20191824540569/50000000000000 : ℝ)^3775 := by
    have hnat : (4900411447 : ℕ)^4799*50000000000000^3775 ≤ 20191824540569^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4900411447 10000000000 20191824540569 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056867343/10000000000 : ℝ)^4799 ≤ (13393923119487/100000000000000 : ℝ)^3775 := by
    have hnat : (2056867343 : ℕ)^4799*100000000000000^3775 ≤ 13393923119487^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056867343 10000000000 13393923119487 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5449613857/10000000000 : ℝ), (4900411447/10000000000 : ℝ), (-2056867343/10000000000 : ℝ)] ![(11555606946133/25000000000000 : ℝ), (20191824540569/50000000000000 : ℝ), (13393923119487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5449613857/10000000000 : ℝ)|^4799 ≤ (11555606946133/25000000000000 : ℝ)^3775
        have hw : |(5449613857/10000000000 : ℝ)|=(5449613857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4900411447/10000000000 : ℝ)|^4799 ≤ (20191824540569/50000000000000 : ℝ)^3775
        have hw : |(4900411447/10000000000 : ℝ)|=(4900411447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056867343/10000000000 : ℝ)|^4799 ≤ (13393923119487/100000000000000 : ℝ)^3775
        have hw : |(-2056867343/10000000000 : ℝ)|=(2056867343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s0_3 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1026225651/2500000000 : ℝ)*x 0 + (3076041541/10000000000 : ℝ)*x 1 + (5374857253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026225651/2500000000 : ℝ)^4799 ≤ (6448193355129/20000000000000 : ℝ)^3775 := by
    have hnat : (1026225651 : ℕ)^4799*20000000000000^3775 ≤ 6448193355129^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026225651 2500000000 6448193355129 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3076041541/10000000000 : ℝ)^4799 ≤ (22341166279833/100000000000000 : ℝ)^3775 := by
    have hnat : (3076041541 : ℕ)^4799*100000000000000^3775 ≤ 22341166279833^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3076041541 10000000000 22341166279833 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374857253/10000000000 : ℝ)^4799 ≤ (45417866934811/100000000000000 : ℝ)^3775 := by
    have hnat : (5374857253 : ℕ)^4799*100000000000000^3775 ≤ 45417866934811^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374857253 10000000000 45417866934811 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026225651/2500000000 : ℝ), (3076041541/10000000000 : ℝ), (5374857253/10000000000 : ℝ)] ![(6448193355129/20000000000000 : ℝ), (22341166279833/100000000000000 : ℝ), (45417866934811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026225651/2500000000 : ℝ)|^4799 ≤ (6448193355129/20000000000000 : ℝ)^3775
        have hw : |(1026225651/2500000000 : ℝ)|=(1026225651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3076041541/10000000000 : ℝ)|^4799 ≤ (22341166279833/100000000000000 : ℝ)^3775
        have hw : |(3076041541/10000000000 : ℝ)|=(3076041541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374857253/10000000000 : ℝ)|^4799 ≤ (45417866934811/100000000000000 : ℝ)^3775
        have hw : |(5374857253/10000000000 : ℝ)|=(5374857253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s0_4 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-48420359/312500000 : ℝ)*x 0 + (4923670163/10000000000 : ℝ)*x 1 + (2899824951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48420359/312500000 : ℝ)^4799 ≤ (18686891037/200000000000 : ℝ)^3775 := by
    have hnat : (48420359 : ℕ)^4799*200000000000^3775 ≤ 18686891037^3775*312500000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48420359 312500000 18686891037 200000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4923670163/10000000000 : ℝ)^4799 ≤ (5078433801819/12500000000000 : ℝ)^3775 := by
    have hnat : (4923670163 : ℕ)^4799*12500000000000^3775 ≤ 5078433801819^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4923670163 10000000000 5078433801819 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2899824951/5000000000 : ℝ)^4799 ≤ (25014542022551/50000000000000 : ℝ)^3775 := by
    have hnat : (2899824951 : ℕ)^4799*50000000000000^3775 ≤ 25014542022551^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899824951 5000000000 25014542022551 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48420359/312500000 : ℝ), (4923670163/10000000000 : ℝ), (2899824951/5000000000 : ℝ)] ![(18686891037/200000000000 : ℝ), (5078433801819/12500000000000 : ℝ), (25014542022551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48420359/312500000 : ℝ)|^4799 ≤ (18686891037/200000000000 : ℝ)^3775
        have hw : |(-48420359/312500000 : ℝ)|=(48420359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4923670163/10000000000 : ℝ)|^4799 ≤ (5078433801819/12500000000000 : ℝ)^3775
        have hw : |(4923670163/10000000000 : ℝ)|=(4923670163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2899824951/5000000000 : ℝ)|^4799 ≤ (25014542022551/50000000000000 : ℝ)^3775
        have hw : |(2899824951/5000000000 : ℝ)|=(2899824951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s0_5 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197475177/10000000000 : ℝ)*x 0 + (-289407181/2500000000 : ℝ)*x 1 + (5799649921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197475177/10000000000 : ℝ)^4799 ≤ (43520990010329/100000000000000 : ℝ)^3775 := by
    have hnat : (5197475177 : ℕ)^4799*100000000000000^3775 ≤ 43520990010329^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197475177 10000000000 43520990010329 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289407181/2500000000 : ℝ)^4799 ≤ (1612481431199/25000000000000 : ℝ)^3775 := by
    have hnat : (289407181 : ℕ)^4799*25000000000000^3775 ≤ 1612481431199^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289407181 2500000000 1612481431199 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5799649921/10000000000 : ℝ)^4799 ≤ (50029084253459/100000000000000 : ℝ)^3775 := by
    have hnat : (5799649921 : ℕ)^4799*100000000000000^3775 ≤ 50029084253459^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5799649921 10000000000 50029084253459 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197475177/10000000000 : ℝ), (-289407181/2500000000 : ℝ), (5799649921/10000000000 : ℝ)] ![(43520990010329/100000000000000 : ℝ), (1612481431199/25000000000000 : ℝ), (50029084253459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197475177/10000000000 : ℝ)|^4799 ≤ (43520990010329/100000000000000 : ℝ)^3775
        have hw : |(5197475177/10000000000 : ℝ)|=(5197475177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-289407181/2500000000 : ℝ)|^4799 ≤ (1612481431199/25000000000000 : ℝ)^3775
        have hw : |(-289407181/2500000000 : ℝ)|=(289407181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5799649921/10000000000 : ℝ)|^4799 ≤ (50029084253459/100000000000000 : ℝ)^3775
        have hw : |(5799649921/10000000000 : ℝ)|=(5799649921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s0_6 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197475153/10000000000 : ℝ)*x 0 + (5799650399/10000000000 : ℝ)*x 1 + (-1157628019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197475153/10000000000 : ℝ)^4799 ≤ (10880247438713/25000000000000 : ℝ)^3775 := by
    have hnat : (5197475153 : ℕ)^4799*25000000000000^3775 ≤ 10880247438713^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197475153 10000000000 10880247438713 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5799650399/10000000000 : ℝ)^4799 ≤ (12507272373821/25000000000000 : ℝ)^3775 := by
    have hnat : (5799650399 : ℕ)^4799*25000000000000^3775 ≤ 12507272373821^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5799650399 10000000000 12507272373821 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1157628019/10000000000 : ℝ)^4799 ≤ (6449920731259/100000000000000 : ℝ)^3775 := by
    have hnat : (1157628019 : ℕ)^4799*100000000000000^3775 ≤ 6449920731259^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157628019 10000000000 6449920731259 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197475153/10000000000 : ℝ), (5799650399/10000000000 : ℝ), (-1157628019/10000000000 : ℝ)] ![(10880247438713/25000000000000 : ℝ), (12507272373821/25000000000000 : ℝ), (6449920731259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197475153/10000000000 : ℝ)|^4799 ≤ (10880247438713/25000000000000 : ℝ)^3775
        have hw : |(5197475153/10000000000 : ℝ)|=(5197475153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5799650399/10000000000 : ℝ)|^4799 ≤ (12507272373821/25000000000000 : ℝ)^3775
        have hw : |(5799650399/10000000000 : ℝ)|=(5799650399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1157628019/10000000000 : ℝ)|^4799 ≤ (6449920731259/100000000000000 : ℝ)^3775
        have hw : |(-1157628019/10000000000 : ℝ)|=(1157628019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s0_7 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4111526683/10000000000 : ℝ)*x 0 + (664618401/1250000000 : ℝ)*x 1 + (3135995349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111526683/10000000000 : ℝ)^4799 ≤ (32307121292227/100000000000000 : ℝ)^3775 := by
    have hnat : (4111526683 : ℕ)^4799*100000000000000^3775 ≤ 32307121292227^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111526683 10000000000 32307121292227 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (664618401/1250000000 : ℝ)^4799 ≤ (5599587071851/12500000000000 : ℝ)^3775 := by
    have hnat : (664618401 : ℕ)^4799*12500000000000^3775 ≤ 5599587071851^3775*1250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664618401 1250000000 5599587071851 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3135995349/10000000000 : ℝ)^4799 ≤ (11448091057131/50000000000000 : ℝ)^3775 := by
    have hnat : (3135995349 : ℕ)^4799*50000000000000^3775 ≤ 11448091057131^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3135995349 10000000000 11448091057131 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111526683/10000000000 : ℝ), (664618401/1250000000 : ℝ), (3135995349/10000000000 : ℝ)] ![(32307121292227/100000000000000 : ℝ), (5599587071851/12500000000000 : ℝ), (11448091057131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111526683/10000000000 : ℝ)|^4799 ≤ (32307121292227/100000000000000 : ℝ)^3775
        have hw : |(4111526683/10000000000 : ℝ)|=(4111526683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(664618401/1250000000 : ℝ)|^4799 ≤ (5599587071851/12500000000000 : ℝ)^3775
        have hw : |(664618401/1250000000 : ℝ)|=(664618401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3135995349/10000000000 : ℝ)|^4799 ≤ (11448091057131/50000000000000 : ℝ)^3775
        have hw : |(3135995349/10000000000 : ℝ)|=(3135995349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1620_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4237/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12007/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4795/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4795 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4795*1^1024 ≤ 0^1024*1^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4795/1024 : ℝ) ≤ (1369617434792838487/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4795 ≤ (1369617434792838487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4795*100000000000000000000^1024 ≤ 1369617434792838487^1024*5^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1369617434792838487 100000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1369617434792838487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4795 := by
      have hnat : (1 : ℕ)^1024*1^4795 ≤ 1^4795*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101369617434792838487/100000000000000000000 : ℝ) ≤ (5014546360584241/5000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (101369617434792838487/100000000000000000000 : ℝ)^1024 ≤ (5014546360584241/5000000000000000 : ℝ)^4795 := by
      have hnat : (101369617434792838487 : ℕ)^1024*5000000000000000^4795 ≤ 5014546360584241^4795*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101369617434792838487 100000000000000000000 5014546360584241 5000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014546360584241/5000000000000000 : ℝ)) (X := (101369617434792838487/100000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51369617434792838487/50000000000000000000 : ℝ) ≤ (2514546360584241/2500000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (51369617434792838487/50000000000000000000 : ℝ)^1024 ≤ (2514546360584241/2500000000000000 : ℝ)^4795 := by
      have hnat : (51369617434792838487 : ℕ)^1024*2500000000000000^4795 ≤ 2514546360584241^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51369617434792838487 50000000000000000000 2514546360584241 2500000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514546360584241/2500000000000000 : ℝ)) (X := (51369617434792838487/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14546360584241/2000000000000000 : ℝ)*(0 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14546360584241/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1369617434792838487/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14546360584241/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4795/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14546360584241/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5014546360584241/5000000000000000 : ℝ) by norm_num, show 1+(1369617434792838487/100000000000000000000 : ℝ)+(0 : ℝ)=(101369617434792838487/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1369617434792838487/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14546360584241/2000000000000000 : ℝ)*(2/5 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14546360584241/2000000000000000 : ℝ)*(2/5 : ℝ)=(2514546360584241/2500000000000000 : ℝ) by norm_num, show 1+2*(1369617434792838487/100000000000000000000 : ℝ)=(51369617434792838487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14546360584241/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14546360584241/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14546360584241/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14546360584241/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14546360584241/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14546360584241/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-193348829/1250000000 : ℝ)*X 0 0+(2911865057/5000000000 : ℝ)*X 0 1+(153137853/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((544961409/1000000000 : ℝ)*X 1 0+(-514216753/2500000000 : ℝ)*X 1 1+(1225102867/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5449613857/10000000000 : ℝ)*X 2 0+(4900411447/10000000000 : ℝ)*X 2 1+(-2056867343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1026225651/2500000000 : ℝ)*X 0 0+(3076041541/10000000000 : ℝ)*X 0 1+(5374857253/10000000000 : ℝ)*X 0 2+(1026225651/2500000000 : ℝ)*X 1 0+(3076041541/10000000000 : ℝ)*X 1 1+(5374857253/10000000000 : ℝ)*X 1 2+(1026225651/2500000000 : ℝ)*X 2 0+(3076041541/10000000000 : ℝ)*X 2 1+(5374857253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-48420359/312500000 : ℝ)*X 0 0+(4923670163/10000000000 : ℝ)*X 0 1+(2899824951/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197475177/10000000000 : ℝ)*X 1 0+(-289407181/2500000000 : ℝ)*X 1 1+(5799649921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5197475153/10000000000 : ℝ)*X 2 0+(5799650399/10000000000 : ℝ)*X 2 1+(-1157628019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4111526683/10000000000 : ℝ)*X 0 0+(664618401/1250000000 : ℝ)*X 0 1+(3135995349/10000000000 : ℝ)*X 0 2+(4111526683/10000000000 : ℝ)*X 1 0+(664618401/1250000000 : ℝ)*X 1 1+(3135995349/10000000000 : ℝ)*X 1 2+(4111526683/10000000000 : ℝ)*X 2 0+(664618401/1250000000 : ℝ)*X 2 1+(3135995349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44762013510475349885799/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (917688153/100000000000000 : ℝ)*(base19) + (815934109/100000000000000 : ℝ)*(base23) + (21092843/10000000000000 : ℝ)*(upper3) + (1208673/4000000000000 : ℝ)*(upper4) + (1154183/2500000000000 : ℝ)*(upper5) + (151806676165187/20000000000000 : ℝ)*(major0) + (151806676165187/20000000000000 : ℝ)*(major1) + (151806676165187/20000000000000 : ℝ)*(major2) + (541526811755567/50000000000000 : ℝ)*(sp0) + (216611154312967/20000000000000 : ℝ)*(sp1) + (541527936659439/50000000000000 : ℝ)*(sp2) + (217503987646543/50000000000000 : ℝ)*(sp3) + (1532870927/50000000000000 : ℝ)*(sp4) + (48697477/2500000000000 : ℝ)*(sp7) + (217504961596083/50000000000000 : ℝ)*(f.failure) + (270764172313247/25000000000000 : ℝ)*(f.sum) + (12405302138067/20000000000000000000000000000 : ℝ)*base65 + (211936919258067/40000000000000000000000000000 : ℝ)*base67 + (31461240981933/40000000000000000000000000000 : ℝ)*base70 + (83447835658067/40000000000000000000000000000 : ℝ)*base71 + (67316122098067/20000000000000000000000000000 : ℝ)*base73 + (47291633301933/40000000000000000000000000000 : ℝ)*base76 + (164889143818067/40000000000000000000000000000 : ℝ)*base77 + (286248719738067/40000000000000000000000000000 : ℝ)*base79 + (48253865461933/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7441879/1250000000000000000000 : ℝ)*base89 + (7441879/1250000000000000000000 : ℝ)*base91 + (7441879/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (240511064159030108693973/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (820091647/100000000000000 : ℝ)*(base19) + (18789081/1562500000000 : ℝ)*(base23) + (201488127/50000000000000 : ℝ)*(base39) + (63298167/100000000000000 : ℝ)*(upper3) + (324790661/100000000000000 : ℝ)*(upper5) + (50002868415599/6250000000000 : ℝ)*(major0) + (50002868415599/6250000000000 : ℝ)*(major1) + (80004549167333/10000000000000 : ℝ)*(major2) + (393858309/12500000000000 : ℝ)*(sp1) + (2951819951/100000000000000 : ℝ)*(sp2) + (35674268895567/3125000000000 : ℝ)*(sp4) + (45662905348001/4000000000000 : ℝ)*(sp5) + (1141572853313263/100000000000000 : ℝ)*(sp6) + (229257310662029/50000000000000 : ℝ)*(sp7) + (229257310662029/50000000000000 : ℝ)*(f.failure) + (570788503817199/50000000000000 : ℝ)*(f.sum) + (43007271400863/100000000000000000000000000000 : ℝ)*base66 + (66386201079253/20000000000000000000000000000 : ℝ)*base67 + (87229286350359/12500000000000000000000000000 : ℝ)*base69 + (56299761419253/20000000000000000000000000000 : ℝ)*base71 + (324145832799137/100000000000000000000000000000 : ℝ)*base73 + (11037551562141/12500000000000000000000000000 : ℝ)*base76 + (11473702225359/12500000000000000000000000000 : ℝ)*base77 + (20519999250359/12500000000000000000000000000 : ℝ)*base79 + (19459825150359/6250000000000000000000000000 : ℝ)*base81 + (2832777/1250000000000000000000 : ℝ)*base89 + (2832777/1250000000000000000000 : ℝ)*base91 + (2832777/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1620_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4237/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12007/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1620_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1620_s1_0 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-333125373/2000000000 : ℝ)*x 0 + (5520775749/10000000000 : ℝ)*x 1 + (5126415951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333125373/2000000000 : ℝ)^4799 ≤ (1024293056743/10000000000000 : ℝ)^3775 := by
    have hnat : (333125373 : ℕ)^4799*10000000000000^3775 ≤ 1024293056743^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333125373 2000000000 1024293056743 10000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520775749/10000000000 : ℝ)^4799 ≤ (46991087930971/100000000000000 : ℝ)^3775 := by
    have hnat : (5520775749 : ℕ)^4799*100000000000000^3775 ≤ 46991087930971^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520775749 10000000000 46991087930971 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5126415951/10000000000 : ℝ)^4799 ≤ (5345747686471/12500000000000 : ℝ)^3775 := by
    have hnat : (5126415951 : ℕ)^4799*12500000000000^3775 ≤ 5345747686471^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126415951 10000000000 5345747686471 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-333125373/2000000000 : ℝ), (5520775749/10000000000 : ℝ), (5126415951/10000000000 : ℝ)] ![(1024293056743/10000000000000 : ℝ), (46991087930971/100000000000000 : ℝ), (5345747686471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-333125373/2000000000 : ℝ)|^4799 ≤ (1024293056743/10000000000000 : ℝ)^3775
        have hw : |(-333125373/2000000000 : ℝ)|=(333125373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520775749/10000000000 : ℝ)|^4799 ≤ (46991087930971/100000000000000 : ℝ)^3775
        have hw : |(5520775749/10000000000 : ℝ)|=(5520775749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5126415951/10000000000 : ℝ)|^4799 ≤ (5345747686471/12500000000000 : ℝ)^3775
        have hw : |(5126415951/10000000000 : ℝ)|=(5126415951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s1_1 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369017217/10000000000 : ℝ)*x 0 + (-1871534471/10000000000 : ℝ)*x 1 + (5126415759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369017217/10000000000 : ℝ)^4799 ≤ (45355141295749/100000000000000 : ℝ)^3775 := by
    have hnat : (5369017217 : ℕ)^4799*100000000000000^3775 ≤ 45355141295749^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369017217 10000000000 45355141295749 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1871534471/10000000000 : ℝ)^4799 ≤ (11878879239149/100000000000000 : ℝ)^3775 := by
    have hnat : (1871534471 : ℕ)^4799*100000000000000^3775 ≤ 11878879239149^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871534471 10000000000 11878879239149 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5126415759/10000000000 : ℝ)^4799 ≤ (10691494863893/25000000000000 : ℝ)^3775 := by
    have hnat : (5126415759 : ℕ)^4799*25000000000000^3775 ≤ 10691494863893^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126415759 10000000000 10691494863893 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369017217/10000000000 : ℝ), (-1871534471/10000000000 : ℝ), (5126415759/10000000000 : ℝ)] ![(45355141295749/100000000000000 : ℝ), (11878879239149/100000000000000 : ℝ), (10691494863893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369017217/10000000000 : ℝ)|^4799 ≤ (45355141295749/100000000000000 : ℝ)^3775
        have hw : |(5369017217/10000000000 : ℝ)|=(5369017217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1871534471/10000000000 : ℝ)|^4799 ≤ (11878879239149/100000000000000 : ℝ)^3775
        have hw : |(-1871534471/10000000000 : ℝ)|=(1871534471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5126415759/10000000000 : ℝ)|^4799 ≤ (10691494863893/25000000000000 : ℝ)^3775
        have hw : |(5126415759/10000000000 : ℝ)|=(5126415759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s1_2 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536901739/1000000000 : ℝ)*x 0 + (205056619/400000000 : ℝ)*x 1 + (-1871534613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536901739/1000000000 : ℝ)^4799 ≤ (11338785788401/25000000000000 : ℝ)^3775 := by
    have hnat : (536901739 : ℕ)^4799*25000000000000^3775 ≤ 11338785788401^3775*1000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536901739 1000000000 11338785788401 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205056619/400000000 : ℝ)^4799 ≤ (21382988221849/50000000000000 : ℝ)^3775 := by
    have hnat : (205056619 : ℕ)^4799*50000000000000^3775 ≤ 21382988221849^3775*400000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205056619 400000000 21382988221849 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871534613/10000000000 : ℝ)^4799 ≤ (475155215397/4000000000000 : ℝ)^3775 := by
    have hnat : (1871534613 : ℕ)^4799*4000000000000^3775 ≤ 475155215397^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871534613 10000000000 475155215397 4000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536901739/1000000000 : ℝ), (205056619/400000000 : ℝ), (-1871534613/10000000000 : ℝ)] ![(11338785788401/25000000000000 : ℝ), (21382988221849/50000000000000 : ℝ), (475155215397/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536901739/1000000000 : ℝ)|^4799 ≤ (11338785788401/25000000000000 : ℝ)^3775
        have hw : |(536901739/1000000000 : ℝ)|=(536901739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205056619/400000000 : ℝ)|^4799 ≤ (21382988221849/50000000000000 : ℝ)^3775
        have hw : |(205056619/400000000 : ℝ)|=(205056619/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1871534613/10000000000 : ℝ)|^4799 ≤ (475155215397/4000000000000 : ℝ)^3775
        have hw : |(-1871534613/10000000000 : ℝ)|=(1871534613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s1_3 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524281109/1250000000 : ℝ)*x 0 + (1862525963/5000000000 : ℝ)*x 1 + (4706902179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524281109/1250000000 : ℝ)^4799 ≤ (6627138075009/20000000000000 : ℝ)^3775 := by
    have hnat : (524281109 : ℕ)^4799*20000000000000^3775 ≤ 6627138075009^3775*1250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524281109 1250000000 6627138075009 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862525963/5000000000 : ℝ)^4799 ≤ (28496952967463/100000000000000 : ℝ)^3775 := by
    have hnat : (1862525963 : ℕ)^4799*100000000000000^3775 ≤ 28496952967463^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862525963 5000000000 28496952967463 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4706902179/10000000000 : ℝ)^4799 ≤ (38367356648253/100000000000000 : ℝ)^3775 := by
    have hnat : (4706902179 : ℕ)^4799*100000000000000^3775 ≤ 38367356648253^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706902179 10000000000 38367356648253 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524281109/1250000000 : ℝ), (1862525963/5000000000 : ℝ), (4706902179/10000000000 : ℝ)] ![(6627138075009/20000000000000 : ℝ), (28496952967463/100000000000000 : ℝ), (38367356648253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524281109/1250000000 : ℝ)|^4799 ≤ (6627138075009/20000000000000 : ℝ)^3775
        have hw : |(524281109/1250000000 : ℝ)|=(524281109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1862525963/5000000000 : ℝ)|^4799 ≤ (28496952967463/100000000000000 : ℝ)^3775
        have hw : |(1862525963/5000000000 : ℝ)|=(1862525963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4706902179/10000000000 : ℝ)|^4799 ≤ (38367356648253/100000000000000 : ℝ)^3775
        have hw : |(4706902179/10000000000 : ℝ)|=(4706902179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s1_4 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1665830013/10000000000 : ℝ)*x 0 + (1026125569/2000000000 : ℝ)*x 1 + (5516499999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1665830013/10000000000 : ℝ)^4799 ≤ (10244518748593/100000000000000 : ℝ)^3775 := by
    have hnat : (1665830013 : ℕ)^4799*100000000000000^3775 ≤ 10244518748593^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665830013 10000000000 10244518748593 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026125569/2000000000 : ℝ)^4799 ≤ (8562130879703/20000000000000 : ℝ)^3775 := by
    have hnat : (1026125569 : ℕ)^4799*20000000000000^3775 ≤ 8562130879703^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026125569 2000000000 8562130879703 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5516499999/10000000000 : ℝ)^4799 ≤ (1467025838781/3125000000000 : ℝ)^3775 := by
    have hnat : (5516499999 : ℕ)^4799*3125000000000^3775 ≤ 1467025838781^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516499999 10000000000 1467025838781 3125000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1665830013/10000000000 : ℝ), (1026125569/2000000000 : ℝ), (5516499999/10000000000 : ℝ)] ![(10244518748593/100000000000000 : ℝ), (8562130879703/20000000000000 : ℝ), (1467025838781/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1665830013/10000000000 : ℝ)|^4799 ≤ (10244518748593/100000000000000 : ℝ)^3775
        have hw : |(-1665830013/10000000000 : ℝ)|=(1665830013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026125569/2000000000 : ℝ)|^4799 ≤ (8562130879703/20000000000000 : ℝ)^3775
        have hw : |(1026125569/2000000000 : ℝ)|=(1026125569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5516499999/10000000000 : ℝ)|^4799 ≤ (1467025838781/3125000000000 : ℝ)^3775
        have hw : |(5516499999/10000000000 : ℝ)|=(5516499999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s1_5 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315988743/2500000000 : ℝ)*x 0 + (-37036241/250000000 : ℝ)*x 1 + (5516500337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315988743/2500000000 : ℝ)^4799 ≤ (691091910779/1562500000000 : ℝ)^3775 := by
    have hnat : (1315988743 : ℕ)^4799*1562500000000^3775 ≤ 691091910779^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315988743 2500000000 691091910779 1562500000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37036241/250000000 : ℝ)^4799 ≤ (8825287195903/100000000000000 : ℝ)^3775 := by
    have hnat : (37036241 : ℕ)^4799*100000000000000^3775 ≤ 8825287195903^3775*250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37036241 250000000 8825287195903 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5516500337/10000000000 : ℝ)^4799 ≤ (1467025953049/3125000000000 : ℝ)^3775 := by
    have hnat : (5516500337 : ℕ)^4799*3125000000000^3775 ≤ 1467025953049^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516500337 10000000000 1467025953049 3125000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315988743/2500000000 : ℝ), (-37036241/250000000 : ℝ), (5516500337/10000000000 : ℝ)] ![(691091910779/1562500000000 : ℝ), (8825287195903/100000000000000 : ℝ), (1467025953049/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315988743/2500000000 : ℝ)|^4799 ≤ (691091910779/1562500000000 : ℝ)^3775
        have hw : |(1315988743/2500000000 : ℝ)|=(1315988743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37036241/250000000 : ℝ)|^4799 ≤ (8825287195903/100000000000000 : ℝ)^3775
        have hw : |(-37036241/250000000 : ℝ)|=(37036241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5516500337/10000000000 : ℝ)|^4799 ≤ (1467025953049/3125000000000 : ℝ)^3775
        have hw : |(5516500337/10000000000 : ℝ)|=(5516500337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s1_6 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263954323/10000000000 : ℝ)*x 0 + (5516500581/10000000000 : ℝ)*x 1 + (-740725103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263954323/10000000000 : ℝ)^4799 ≤ (1105746883937/2500000000000 : ℝ)^3775 := by
    have hnat : (5263954323 : ℕ)^4799*2500000000000^3775 ≤ 1105746883937^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263954323 10000000000 1105746883937 2500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516500581/10000000000 : ℝ)^4799 ≤ (46944833137227/100000000000000 : ℝ)^3775 := by
    have hnat : (5516500581 : ℕ)^4799*100000000000000^3775 ≤ 46944833137227^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516500581 10000000000 46944833137227 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (740725103/5000000000 : ℝ)^4799 ≤ (4412645741149/50000000000000 : ℝ)^3775 := by
    have hnat : (740725103 : ℕ)^4799*50000000000000^3775 ≤ 4412645741149^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740725103 5000000000 4412645741149 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263954323/10000000000 : ℝ), (5516500581/10000000000 : ℝ), (-740725103/5000000000 : ℝ)] ![(1105746883937/2500000000000 : ℝ), (46944833137227/100000000000000 : ℝ), (4412645741149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263954323/10000000000 : ℝ)|^4799 ≤ (1105746883937/2500000000000 : ℝ)^3775
        have hw : |(5263954323/10000000000 : ℝ)|=(5263954323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516500581/10000000000 : ℝ)|^4799 ≤ (46944833137227/100000000000000 : ℝ)^3775
        have hw : |(5516500581/10000000000 : ℝ)|=(5516500581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-740725103/5000000000 : ℝ)|^4799 ≤ (4412645741149/50000000000000 : ℝ)^3775
        have hw : |(-740725103/5000000000 : ℝ)|=(740725103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s1_7 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097376329/5000000000 : ℝ)*x 0 + (4696416783/10000000000 : ℝ)*x 1 + (3735696529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097376329/5000000000 : ℝ)^4799 ≤ (33140750121913/100000000000000 : ℝ)^3775 := by
    have hnat : (2097376329 : ℕ)^4799*100000000000000^3775 ≤ 33140750121913^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097376329 5000000000 33140750121913 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4696416783/10000000000 : ℝ)^4799 ≤ (19129367794897/50000000000000 : ℝ)^3775 := by
    have hnat : (4696416783 : ℕ)^4799*50000000000000^3775 ≤ 19129367794897^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696416783 10000000000 19129367794897 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3735696529/10000000000 : ℝ)^4799 ≤ (1787532142223/6250000000000 : ℝ)^3775 := by
    have hnat : (3735696529 : ℕ)^4799*6250000000000^3775 ≤ 1787532142223^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3735696529 10000000000 1787532142223 6250000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097376329/5000000000 : ℝ), (4696416783/10000000000 : ℝ), (3735696529/10000000000 : ℝ)] ![(33140750121913/100000000000000 : ℝ), (19129367794897/50000000000000 : ℝ), (1787532142223/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097376329/5000000000 : ℝ)|^4799 ≤ (33140750121913/100000000000000 : ℝ)^3775
        have hw : |(2097376329/5000000000 : ℝ)|=(2097376329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4696416783/10000000000 : ℝ)|^4799 ≤ (19129367794897/50000000000000 : ℝ)^3775
        have hw : |(4696416783/10000000000 : ℝ)|=(4696416783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3735696529/10000000000 : ℝ)|^4799 ≤ (1787532142223/6250000000000 : ℝ)^3775
        have hw : |(3735696529/10000000000 : ℝ)|=(3735696529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1620_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1163/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8833/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4237/100000 : ℝ) ^ (4795/1024 : ℝ) ≤ (37242632032287/100000000000000000000 : ℝ) := by
    have hpowers : (4237/100000 : ℝ)^4795 ≤ (37242632032287/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4237 : ℕ)^4795*100000000000000000000^1024 ≤ 37242632032287^1024*100000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4237 100000 37242632032287 100000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4237/100000 : ℝ)) (X := (37242632032287/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12007/50000 : ℝ) ^ (4795/1024 : ℝ) ≤ (15698655600001409/12500000000000000000 : ℝ) := by
    have hpowers : (12007/50000 : ℝ)^4795 ≤ (15698655600001409/12500000000000000000 : ℝ)^1024 := by
      have hnat : (12007 : ℕ)^4795*12500000000000000000^1024 ≤ 15698655600001409^1024*50000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12007 50000 15698655600001409 12500000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12007/50000 : ℝ)) (X := (15698655600001409/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000037242632032287/50000000000000000000 : ℝ) ≤ (2000000318135091/2000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50000037242632032287/50000000000000000000 : ℝ)^1024 ≤ (2000000318135091/2000000000000000 : ℝ)^4795 := by
      have hnat : (50000037242632032287 : ℕ)^1024*2000000000000000^4795 ≤ 2000000318135091^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000037242632032287 50000000000000000000 2000000318135091 2000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000318135091/2000000000000000 : ℝ)) (X := (50000037242632032287/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100125626487432043559/100000000000000000000 : ℝ) ≤ (10002681502040829/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (100125626487432043559/100000000000000000000 : ℝ)^1024 ≤ (10002681502040829/10000000000000000 : ℝ)^4795 := by
      have hnat : (100125626487432043559 : ℕ)^1024*10000000000000000^4795 ≤ 10002681502040829^4795*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100125626487432043559 100000000000000000000 10002681502040829 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002681502040829/10000000000000000 : ℝ)) (X := (100125626487432043559/100000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6265698655600001409/6250000000000000000 : ℝ) ≤ (10005361413406203/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (6265698655600001409/6250000000000000000 : ℝ)^1024 ≤ (10005361413406203/10000000000000000 : ℝ)^4795 := by
      have hnat : (6265698655600001409 : ℕ)^1024*10000000000000000^4795 ≤ 10005361413406203^4795*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6265698655600001409 6250000000000000000 10005361413406203 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005361413406203/10000000000000000 : ℝ)) (X := (6265698655600001409/6250000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(37242632032287/100000000000000000000 : ℝ) ≤ ((197747321889878294259/197770000000000000000 : ℝ)+2*(1339955682687/988850000000000 : ℝ)*(4237/100000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (197747321889878294259/197770000000000000000 : ℝ)+2*(1339955682687/988850000000000 : ℝ)*(4237/100000 : ℝ)=(2000000318135091/2000000000000000 : ℝ) by norm_num, show 1+2*(37242632032287/100000000000000000000 : ℝ)=(50000037242632032287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15698655600001409/12500000000000000000 : ℝ)+(37242632032287/100000000000000000000 : ℝ) ≤ ((197747321889878294259/197770000000000000000 : ℝ)+(1339955682687/988850000000000 : ℝ)*((12007/50000 : ℝ)+(4237/100000 : ℝ)))^(4795/1024 : ℝ) := by
    rw [show (197747321889878294259/197770000000000000000 : ℝ)+(1339955682687/988850000000000 : ℝ)*((12007/50000 : ℝ)+(4237/100000 : ℝ))=(10002681502040829/10000000000000000 : ℝ) by norm_num, show 1+(15698655600001409/12500000000000000000 : ℝ)+(37242632032287/100000000000000000000 : ℝ)=(100125626487432043559/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15698655600001409/12500000000000000000 : ℝ) ≤ ((197747321889878294259/197770000000000000000 : ℝ)+2*(1339955682687/988850000000000 : ℝ)*(12007/50000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (197747321889878294259/197770000000000000000 : ℝ)+2*(1339955682687/988850000000000 : ℝ)*(12007/50000 : ℝ)=(10005361413406203/10000000000000000 : ℝ) by norm_num, show 1+2*(15698655600001409/12500000000000000000 : ℝ)=(6265698655600001409/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (197747321889878294259/197770000000000000000 : ℝ)*(X 1 0+X 2 0)+(1339955682687/988850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (4237/100000 : ℝ)) (hi := (12007/50000 : ℝ)) (c := (197747321889878294259/197770000000000000000 : ℝ)) (alpha := (1339955682687/988850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (197747321889878294259/197770000000000000000 : ℝ)*(X 0 1+X 2 1)+(1339955682687/988850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (4237/100000 : ℝ)) (hi := (12007/50000 : ℝ)) (c := (197747321889878294259/197770000000000000000 : ℝ)) (alpha := (1339955682687/988850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (197747321889878294259/197770000000000000000 : ℝ)*(X 0 2+X 1 2)+(1339955682687/988850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (4237/100000 : ℝ)) (hi := (12007/50000 : ℝ)) (c := (197747321889878294259/197770000000000000000 : ℝ)) (alpha := (1339955682687/988850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-333125373/2000000000 : ℝ)*X 0 0+(5520775749/10000000000 : ℝ)*X 0 1+(5126415951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369017217/10000000000 : ℝ)*X 1 0+(-1871534471/10000000000 : ℝ)*X 1 1+(5126415759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536901739/1000000000 : ℝ)*X 2 0+(205056619/400000000 : ℝ)*X 2 1+(-1871534613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((524281109/1250000000 : ℝ)*X 0 0+(1862525963/5000000000 : ℝ)*X 0 1+(4706902179/10000000000 : ℝ)*X 0 2+(524281109/1250000000 : ℝ)*X 1 0+(1862525963/5000000000 : ℝ)*X 1 1+(4706902179/10000000000 : ℝ)*X 1 2+(524281109/1250000000 : ℝ)*X 2 0+(1862525963/5000000000 : ℝ)*X 2 1+(4706902179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1665830013/10000000000 : ℝ)*X 0 0+(1026125569/2000000000 : ℝ)*X 0 1+(5516499999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1315988743/2500000000 : ℝ)*X 1 0+(-37036241/250000000 : ℝ)*X 1 1+(5516500337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5263954323/10000000000 : ℝ)*X 2 0+(5516500581/10000000000 : ℝ)*X 2 1+(-740725103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2097376329/5000000000 : ℝ)*X 0 0+(4696416783/10000000000 : ℝ)*X 0 1+(3735696529/10000000000 : ℝ)*X 0 2+(2097376329/5000000000 : ℝ)*X 1 0+(4696416783/10000000000 : ℝ)*X 1 1+(3735696529/10000000000 : ℝ)*X 1 2+(2097376329/5000000000 : ℝ)*X 2 0+(4696416783/10000000000 : ℝ)*X 2 1+(3735696529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (543948672412171840052199/98885000000000000000000000000 : ℝ) := by norm_num
    linear_combination (262797237/100000000000000 : ℝ)*(base1) + (1066467687/100000000000000 : ℝ)*(base19) + (574087433/50000000000000 : ℝ)*(base23) + (29931973/20000000000000 : ℝ)*(upper3) + (40013583/50000000000000 : ℝ)*(upper5) + (888564107373783/50000000000000 : ℝ)*(major0) + (888564107373783/50000000000000 : ℝ)*(major1) + (888564107373783/50000000000000 : ℝ)*(major2) + (2535761064230357/100000000000000 : ℝ)*(sp0) + (158485282545001/6250000000000 : ℝ)*(sp1) + (1267882219506419/50000000000000 : ℝ)*(sp2) + (1989233482563/195312500000 : ℝ)*(sp3) + (598219323/12500000000000 : ℝ)*(sp4) + (570615447/20000000000000 : ℝ)*(sp7) + (127311332368341/12500000000000 : ℝ)*(f.failure) + (316970698398463/12500000000000 : ℝ)*(f.sum) + (32136460173159/98885000000000000000000000000 : ℝ)*base65 + (48902195502198788203/9888500000000000000000000000000000 : ℝ)*base68 + (33467732615573211797/9888500000000000000000000000000000 : ℝ)*base69 + (9232968767098788203/9888500000000000000000000000000000 : ℝ)*base72 + (126595064985059/98885000000000000000000000000 : ℝ)*base73 + (67724836743214711797/9888500000000000000000000000000000 : ℝ)*base75 + (34099949032796788203/9888500000000000000000000000000000 : ℝ)*base78 + (28575545083536711797/9888500000000000000000000000000000 : ℝ)*base79 + (435573813790859/98885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (804033/312500000000000000000 : ℝ)*base89 + (804033/312500000000000000000 : ℝ)*base91 + (804033/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14766478984621515083746619343/2472125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (634362539/50000000000000 : ℝ)*(base19) + (128976261/12500000000000 : ℝ)*(base23) + (24312371/50000000000000 : ℝ)*(upper2) + (143794413/50000000000000 : ℝ)*(upper3) + (13358757/50000000000000 : ℝ)*(upper5) + (454051589478853/25000000000000 : ℝ)*(major0) + (454051589478853/25000000000000 : ℝ)*(major1) + (454051589478853/25000000000000 : ℝ)*(major2) + (9455323547/100000000000000 : ℝ)*(sp1) + (8965470333/100000000000000 : ℝ)*(sp2) + (129576288379137/5000000000000 : ℝ)*(sp4) + (647878760883529/25000000000000 : ℝ)*(sp5) + (32393947128779/1250000000000 : ℝ)*(sp6) + (520443374570827/50000000000000 : ℝ)*(sp7) + (520443374570827/50000000000000 : ℝ)*(f.failure) + (129576288379137/5000000000000 : ℝ)*(f.sum) + (13340340308623/6180312500000000000000000000 : ℝ)*base65 + (25099476826209495073/4944250000000000000000000000000000 : ℝ)*base68 + (1464784323406495073/4944250000000000000000000000000000 : ℝ)*base70 + (16067199302603745073/4944250000000000000000000000000000 : ℝ)*base72 + (217071410252663/98885000000000000000000000000 : ℝ)*base73 + (95045380345377745073/4944250000000000000000000000000000 : ℝ)*base76 + (2562903909674495073/4944250000000000000000000000000000 : ℝ)*base78 + (36890800090638245073/4944250000000000000000000000000000 : ℝ)*base80 + (380119652026543/98885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6483951/1250000000000000000000 : ℝ)*base89 + (6483951/1250000000000000000000 : ℝ)*base91 + (6483951/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1620_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1163/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8833/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1620_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1620_s2_0 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-839107807/5000000000 : ℝ)*x 0 + (5462526267/10000000000 : ℝ)*x 1 + (5176407641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839107807/5000000000 : ℝ)^4799 ≤ (5170723312643/50000000000000 : ℝ)^3775 := by
    have hnat : (839107807 : ℕ)^4799*50000000000000^3775 ≤ 5170723312643^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839107807 5000000000 5170723312643 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462526267/10000000000 : ℝ)^4799 ≤ (46361700994907/100000000000000 : ℝ)^3775 := by
    have hnat : (5462526267 : ℕ)^4799*100000000000000^3775 ≤ 46361700994907^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462526267 10000000000 46361700994907 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176407641/10000000000 : ℝ)^4799 ≤ (43296852356689/100000000000000 : ℝ)^3775 := by
    have hnat : (5176407641 : ℕ)^4799*100000000000000^3775 ≤ 43296852356689^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176407641 10000000000 43296852356689 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-839107807/5000000000 : ℝ), (5462526267/10000000000 : ℝ), (5176407641/10000000000 : ℝ)] ![(5170723312643/50000000000000 : ℝ), (46361700994907/100000000000000 : ℝ), (43296852356689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-839107807/5000000000 : ℝ)|^4799 ≤ (5170723312643/50000000000000 : ℝ)^3775
        have hw : |(-839107807/5000000000 : ℝ)|=(839107807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462526267/10000000000 : ℝ)|^4799 ≤ (46361700994907/100000000000000 : ℝ)^3775
        have hw : |(5462526267/10000000000 : ℝ)|=(5462526267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176407641/10000000000 : ℝ)|^4799 ≤ (43296852356689/100000000000000 : ℝ)^3775
        have hw : |(5176407641/10000000000 : ℝ)|=(5176407641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s2_1 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353773097/10000000000 : ℝ)*x 0 + (-456467599/2500000000 : ℝ)*x 1 + (5176407737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353773097/10000000000 : ℝ)^4799 ≤ (9038299428681/20000000000000 : ℝ)^3775 := by
    have hnat : (5353773097 : ℕ)^4799*20000000000000^3775 ≤ 9038299428681^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353773097 10000000000 9038299428681 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456467599/2500000000 : ℝ)^4799 ≤ (2302329893191/20000000000000 : ℝ)^3775 := by
    have hnat : (456467599 : ℕ)^4799*20000000000000^3775 ≤ 2302329893191^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456467599 2500000000 2302329893191 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176407737/10000000000 : ℝ)^4799 ≤ (43296853377471/100000000000000 : ℝ)^3775 := by
    have hnat : (5176407737 : ℕ)^4799*100000000000000^3775 ≤ 43296853377471^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176407737 10000000000 43296853377471 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353773097/10000000000 : ℝ), (-456467599/2500000000 : ℝ), (5176407737/10000000000 : ℝ)] ![(9038299428681/20000000000000 : ℝ), (2302329893191/20000000000000 : ℝ), (43296853377471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353773097/10000000000 : ℝ)|^4799 ≤ (9038299428681/20000000000000 : ℝ)^3775
        have hw : |(5353773097/10000000000 : ℝ)|=(5353773097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456467599/2500000000 : ℝ)|^4799 ≤ (2302329893191/20000000000000 : ℝ)^3775
        have hw : |(-456467599/2500000000 : ℝ)|=(456467599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176407737/10000000000 : ℝ)|^4799 ≤ (43296853377471/100000000000000 : ℝ)^3775
        have hw : |(5176407737/10000000000 : ℝ)|=(5176407737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s2_2 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353773209/10000000000 : ℝ)*x 0 + (5176407537/10000000000 : ℝ)*x 1 + (-114116907/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353773209/10000000000 : ℝ)^4799 ≤ (180765993381/400000000000 : ℝ)^3775 := by
    have hnat : (5353773209 : ℕ)^4799*400000000000^3775 ≤ 180765993381^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353773209 10000000000 180765993381 400000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176407537/10000000000 : ℝ)^4799 ≤ (21648425625421/50000000000000 : ℝ)^3775 := by
    have hnat : (5176407537 : ℕ)^4799*50000000000000^3775 ≤ 21648425625421^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176407537 10000000000 21648425625421 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114116907/625000000 : ℝ)^4799 ≤ (11511650395691/100000000000000 : ℝ)^3775 := by
    have hnat : (114116907 : ℕ)^4799*100000000000000^3775 ≤ 11511650395691^3775*625000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114116907 625000000 11511650395691 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353773209/10000000000 : ℝ), (5176407537/10000000000 : ℝ), (-114116907/625000000 : ℝ)] ![(180765993381/400000000000 : ℝ), (21648425625421/50000000000000 : ℝ), (11511650395691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353773209/10000000000 : ℝ)|^4799 ≤ (180765993381/400000000000 : ℝ)^3775
        have hw : |(5353773209/10000000000 : ℝ)|=(5353773209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176407537/10000000000 : ℝ)|^4799 ≤ (21648425625421/50000000000000 : ℝ)^3775
        have hw : |(5176407537/10000000000 : ℝ)|=(5176407537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114116907/625000000 : ℝ)|^4799 ≤ (11511650395691/100000000000000 : ℝ)^3775
        have hw : |(-114116907/625000000 : ℝ)|=(114116907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s2_3 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4203563107/10000000000 : ℝ)*x 0 + (3858825389/10000000000 : ℝ)*x 1 + (4571183421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203563107/10000000000 : ℝ)^4799 ≤ (16614632008053/50000000000000 : ℝ)^3775 := by
    have hnat : (4203563107 : ℕ)^4799*50000000000000^3775 ≤ 16614632008053^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203563107 10000000000 16614632008053 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3858825389/10000000000 : ℝ)^4799 ≤ (1490210645521/5000000000000 : ℝ)^3775 := by
    have hnat : (3858825389 : ℕ)^4799*5000000000000^3775 ≤ 1490210645521^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858825389 10000000000 1490210645521 5000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4571183421/10000000000 : ℝ)^4799 ≤ (4620815382929/12500000000000 : ℝ)^3775 := by
    have hnat : (4571183421 : ℕ)^4799*12500000000000^3775 ≤ 4620815382929^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571183421 10000000000 4620815382929 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203563107/10000000000 : ℝ), (3858825389/10000000000 : ℝ), (4571183421/10000000000 : ℝ)] ![(16614632008053/50000000000000 : ℝ), (1490210645521/5000000000000 : ℝ), (4620815382929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203563107/10000000000 : ℝ)|^4799 ≤ (16614632008053/50000000000000 : ℝ)^3775
        have hw : |(4203563107/10000000000 : ℝ)|=(4203563107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3858825389/10000000000 : ℝ)|^4799 ≤ (1490210645521/5000000000000 : ℝ)^3775
        have hw : |(3858825389/10000000000 : ℝ)|=(3858825389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4571183421/10000000000 : ℝ)|^4799 ≤ (4620815382929/12500000000000 : ℝ)^3775
        have hw : |(4571183421/10000000000 : ℝ)|=(4571183421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s2_4 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-83914679/500000000 : ℝ)*x 0 + (5178631739/10000000000 : ℝ)*x 1 + (5460277531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83914679/500000000 : ℝ)^4799 ≤ (2068411478389/20000000000000 : ℝ)^3775 := by
    have hnat : (83914679 : ℕ)^4799*20000000000000^3775 ≤ 2068411478389^3775*500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83914679 500000000 2068411478389 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178631739/10000000000 : ℝ)^4799 ≤ (10830125721617/25000000000000 : ℝ)^3775 := by
    have hnat : (5178631739 : ℕ)^4799*25000000000000^3775 ≤ 10830125721617^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178631739 10000000000 10830125721617 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460277531/10000000000 : ℝ)^4799 ≤ (9267487941547/20000000000000 : ℝ)^3775 := by
    have hnat : (5460277531 : ℕ)^4799*20000000000000^3775 ≤ 9267487941547^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460277531 10000000000 9267487941547 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83914679/500000000 : ℝ), (5178631739/10000000000 : ℝ), (5460277531/10000000000 : ℝ)] ![(2068411478389/20000000000000 : ℝ), (10830125721617/25000000000000 : ℝ), (9267487941547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83914679/500000000 : ℝ)|^4799 ≤ (2068411478389/20000000000000 : ℝ)^3775
        have hw : |(-83914679/500000000 : ℝ)|=(83914679/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178631739/10000000000 : ℝ)|^4799 ≤ (10830125721617/25000000000000 : ℝ)^3775
        have hw : |(5178631739/10000000000 : ℝ)|=(5178631739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460277531/10000000000 : ℝ)|^4799 ≤ (9267487941547/20000000000000 : ℝ)^3775
        have hw : |(5460277531/10000000000 : ℝ)|=(5460277531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s2_5 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638823911/5000000000 : ℝ)*x 0 + (-771000213/5000000000 : ℝ)*x 1 + (6825347/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638823911/5000000000 : ℝ)^4799 ≤ (44376195776647/100000000000000 : ℝ)^3775 := by
    have hnat : (2638823911 : ℕ)^4799*100000000000000^3775 ≤ 44376195776647^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638823911 5000000000 44376195776647 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771000213/5000000000 : ℝ)^4799 ≤ (1857272751413/20000000000000 : ℝ)^3775 := by
    have hnat : (771000213 : ℕ)^4799*20000000000000^3775 ≤ 1857272751413^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771000213 5000000000 1857272751413 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6825347/12500000 : ℝ)^4799 ≤ (11584360113031/25000000000000 : ℝ)^3775 := by
    have hnat : (6825347 : ℕ)^4799*25000000000000^3775 ≤ 11584360113031^3775*12500000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6825347 12500000 11584360113031 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638823911/5000000000 : ℝ), (-771000213/5000000000 : ℝ), (6825347/12500000 : ℝ)] ![(44376195776647/100000000000000 : ℝ), (1857272751413/20000000000000 : ℝ), (11584360113031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638823911/5000000000 : ℝ)|^4799 ≤ (44376195776647/100000000000000 : ℝ)^3775
        have hw : |(2638823911/5000000000 : ℝ)|=(2638823911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-771000213/5000000000 : ℝ)|^4799 ≤ (1857272751413/20000000000000 : ℝ)^3775
        have hw : |(-771000213/5000000000 : ℝ)|=(771000213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6825347/12500000 : ℝ)|^4799 ≤ (11584360113031/25000000000000 : ℝ)^3775
        have hw : |(6825347/12500000 : ℝ)|=(6825347/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s2_6 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319411811/2500000000 : ℝ)*x 0 + (5460279031/10000000000 : ℝ)*x 1 + (-1541999217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319411811/2500000000 : ℝ)^4799 ≤ (22188094799157/50000000000000 : ℝ)^3775 := by
    have hnat : (1319411811 : ℕ)^4799*50000000000000^3775 ≤ 22188094799157^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319411811 2500000000 22188094799157 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460279031/10000000000 : ℝ)^4799 ≤ (23168727945057/50000000000000 : ℝ)^3775 := by
    have hnat : (5460279031 : ℕ)^4799*50000000000000^3775 ≤ 23168727945057^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460279031 10000000000 23168727945057 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1541999217/10000000000 : ℝ)^4799 ≤ (928635450111/10000000000000 : ℝ)^3775 := by
    have hnat : (1541999217 : ℕ)^4799*10000000000000^3775 ≤ 928635450111^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541999217 10000000000 928635450111 10000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319411811/2500000000 : ℝ), (5460279031/10000000000 : ℝ), (-1541999217/10000000000 : ℝ)] ![(22188094799157/50000000000000 : ℝ), (23168727945057/50000000000000 : ℝ), (928635450111/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319411811/2500000000 : ℝ)|^4799 ≤ (22188094799157/50000000000000 : ℝ)^3775
        have hw : |(1319411811/2500000000 : ℝ)|=(1319411811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460279031/10000000000 : ℝ)|^4799 ≤ (23168727945057/50000000000000 : ℝ)^3775
        have hw : |(5460279031/10000000000 : ℝ)|=(5460279031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1541999217/10000000000 : ℝ)|^4799 ≤ (928635450111/10000000000000 : ℝ)^3775
        have hw : |(-1541999217/10000000000 : ℝ)|=(1541999217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s2_7 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (840751349/2000000000 : ℝ)*x 0 + (2282822839/5000000000 : ℝ)*x 1 + (966105827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840751349/2000000000 : ℝ)^4799 ≤ (16615604979847/50000000000000 : ℝ)^3775 := by
    have hnat : (840751349 : ℕ)^4799*50000000000000^3775 ≤ 16615604979847^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840751349 2000000000 16615604979847 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282822839/5000000000 : ℝ)^4799 ≤ (7381920343451/20000000000000 : ℝ)^3775 := by
    have hnat : (2282822839 : ℕ)^4799*20000000000000^3775 ≤ 7381920343451^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282822839 5000000000 7381920343451 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966105827/2500000000 : ℝ)^4799 ≤ (29859188303691/100000000000000 : ℝ)^3775 := by
    have hnat : (966105827 : ℕ)^4799*100000000000000^3775 ≤ 29859188303691^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966105827 2500000000 29859188303691 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840751349/2000000000 : ℝ), (2282822839/5000000000 : ℝ), (966105827/2500000000 : ℝ)] ![(16615604979847/50000000000000 : ℝ), (7381920343451/20000000000000 : ℝ), (29859188303691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840751349/2000000000 : ℝ)|^4799 ≤ (16615604979847/50000000000000 : ℝ)^3775
        have hw : |(840751349/2000000000 : ℝ)|=(840751349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282822839/5000000000 : ℝ)|^4799 ≤ (7381920343451/20000000000000 : ℝ)^3775
        have hw : |(2282822839/5000000000 : ℝ)|=(2282822839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(966105827/2500000000 : ℝ)|^4799 ≤ (29859188303691/100000000000000 : ℝ)^3775
        have hw : |(966105827/2500000000 : ℝ)|=(966105827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1620_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8833/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1163/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10383/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16453/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8833/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1163/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8833/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1163/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8833/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1163/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8833/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1163/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8833/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1163/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8833/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1163/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1163/12500 : ℝ) ^ (4795/1024 : ℝ) ≤ (1481409138130447/100000000000000000000 : ℝ) := by
    have hpowers : (1163/12500 : ℝ)^4795 ≤ (1481409138130447/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1163 : ℕ)^4795*100000000000000000000^1024 ≤ 1481409138130447^1024*12500^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1163 12500 1481409138130447 100000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1163/12500 : ℝ)) (X := (1481409138130447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8833/50000 : ℝ) ^ (4795/1024 : ℝ) ≤ (745721262912727/2500000000000000000 : ℝ) := by
    have hpowers : (8833/50000 : ℝ)^4795 ≤ (745721262912727/2500000000000000000 : ℝ)^1024 := by
      have hnat : (8833 : ℕ)^4795*2500000000000000000^1024 ≤ 745721262912727^1024*50000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8833 50000 745721262912727 2500000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8833/50000 : ℝ)) (X := (745721262912727/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001481409138130447/50000000000000000000 : ℝ) ≤ (10000063271961813/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50001481409138130447/50000000000000000000 : ℝ)^1024 ≤ (10000063271961813/10000000000000000 : ℝ)^4795 := by
      have hnat : (50001481409138130447 : ℕ)^1024*10000000000000000^4795 ≤ 10000063271961813^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001481409138130447 50000000000000000000 10000063271961813 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063271961813/10000000000000000 : ℝ)) (X := (50001481409138130447/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031310259654639527/100000000000000000000 : ℝ) ≤ (10000668566407121/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (100031310259654639527/100000000000000000000 : ℝ)^1024 ≤ (10000668566407121/10000000000000000 : ℝ)^4795 := by
      have hnat : (100031310259654639527 : ℕ)^1024*10000000000000000^4795 ≤ 10000668566407121^4795*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031310259654639527 100000000000000000000 10000668566407121 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668566407121/10000000000000000 : ℝ)) (X := (100031310259654639527/100000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250745721262912727/1250000000000000000 : ℝ) ≤ (10001273860852429/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (1250745721262912727/1250000000000000000 : ℝ)^1024 ≤ (10001273860852429/10000000000000000 : ℝ)^4795 := by
      have hnat : (1250745721262912727 : ℕ)^1024*10000000000000000^4795 ≤ 10001273860852429^4795*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250745721262912727 1250000000000000000 10001273860852429 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001273860852429/10000000000000000 : ℝ)) (X := (1250745721262912727/1250000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1481409138130447/100000000000000000000 : ℝ) ≤ ((41804632880553194521/41810000000000000000 : ℝ)+2*(151323611327/209050000000000 : ℝ)*(1163/12500 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (41804632880553194521/41810000000000000000 : ℝ)+2*(151323611327/209050000000000 : ℝ)*(1163/12500 : ℝ)=(10000063271961813/10000000000000000 : ℝ) by norm_num, show 1+2*(1481409138130447/100000000000000000000 : ℝ)=(50001481409138130447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(745721262912727/2500000000000000000 : ℝ)+(1481409138130447/100000000000000000000 : ℝ) ≤ ((41804632880553194521/41810000000000000000 : ℝ)+(151323611327/209050000000000 : ℝ)*((8833/50000 : ℝ)+(1163/12500 : ℝ)))^(4795/1024 : ℝ) := by
    rw [show (41804632880553194521/41810000000000000000 : ℝ)+(151323611327/209050000000000 : ℝ)*((8833/50000 : ℝ)+(1163/12500 : ℝ))=(10000668566407121/10000000000000000 : ℝ) by norm_num, show 1+(745721262912727/2500000000000000000 : ℝ)+(1481409138130447/100000000000000000000 : ℝ)=(100031310259654639527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(745721262912727/2500000000000000000 : ℝ) ≤ ((41804632880553194521/41810000000000000000 : ℝ)+2*(151323611327/209050000000000 : ℝ)*(8833/50000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (41804632880553194521/41810000000000000000 : ℝ)+2*(151323611327/209050000000000 : ℝ)*(8833/50000 : ℝ)=(10001273860852429/10000000000000000 : ℝ) by norm_num, show 1+2*(745721262912727/2500000000000000000 : ℝ)=(1250745721262912727/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41804632880553194521/41810000000000000000 : ℝ)*(X 1 0+X 2 0)+(151323611327/209050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (1163/12500 : ℝ)) (hi := (8833/50000 : ℝ)) (c := (41804632880553194521/41810000000000000000 : ℝ)) (alpha := (151323611327/209050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41804632880553194521/41810000000000000000 : ℝ)*(X 0 1+X 2 1)+(151323611327/209050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (1163/12500 : ℝ)) (hi := (8833/50000 : ℝ)) (c := (41804632880553194521/41810000000000000000 : ℝ)) (alpha := (151323611327/209050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41804632880553194521/41810000000000000000 : ℝ)*(X 0 2+X 1 2)+(151323611327/209050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (1163/12500 : ℝ)) (hi := (8833/50000 : ℝ)) (c := (41804632880553194521/41810000000000000000 : ℝ)) (alpha := (151323611327/209050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-839107807/5000000000 : ℝ)*X 0 0+(5462526267/10000000000 : ℝ)*X 0 1+(5176407641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353773097/10000000000 : ℝ)*X 1 0+(-456467599/2500000000 : ℝ)*X 1 1+(5176407737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353773209/10000000000 : ℝ)*X 2 0+(5176407537/10000000000 : ℝ)*X 2 1+(-114116907/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4203563107/10000000000 : ℝ)*X 0 0+(3858825389/10000000000 : ℝ)*X 0 1+(4571183421/10000000000 : ℝ)*X 0 2+(4203563107/10000000000 : ℝ)*X 1 0+(3858825389/10000000000 : ℝ)*X 1 1+(4571183421/10000000000 : ℝ)*X 1 2+(4203563107/10000000000 : ℝ)*X 2 0+(3858825389/10000000000 : ℝ)*X 2 1+(4571183421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-83914679/500000000 : ℝ)*X 0 0+(5178631739/10000000000 : ℝ)*X 0 1+(5460277531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638823911/5000000000 : ℝ)*X 1 0+(-771000213/5000000000 : ℝ)*X 1 1+(6825347/12500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319411811/2500000000 : ℝ)*X 2 0+(5460279031/10000000000 : ℝ)*X 2 1+(-1541999217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((840751349/2000000000 : ℝ)*X 0 0+(2282822839/5000000000 : ℝ)*X 0 1+(966105827/2500000000 : ℝ)*X 0 2+(840751349/2000000000 : ℝ)*X 1 0+(2282822839/5000000000 : ℝ)*X 1 1+(966105827/2500000000 : ℝ)*X 1 2+(840751349/2000000000 : ℝ)*X 2 0+(2282822839/5000000000 : ℝ)*X 2 1+(966105827/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61865926088694236891727/5226250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1833998311/100000000000000 : ℝ)*(base19) + (879675817/50000000000000 : ℝ)*(base23) + (79109201/100000000000000 : ℝ)*(lower2) + (344103823/100000000000000 : ℝ)*(upper3) + (158614583/100000000000000 : ℝ)*(upper5) + (2449451684729541/100000000000000 : ℝ)*(major0) + (2449451684729541/100000000000000 : ℝ)*(major1) + (2449451684729541/100000000000000 : ℝ)*(major2) + (349507652039227/10000000000000 : ℝ)*(sp0) + (349509491027583/10000000000000 : ℝ)*(sp1) + (3495094984922507/100000000000000 : ℝ)*(sp2) + (1403796357157009/100000000000000 : ℝ)*(sp3) + (2022388187/10000000000000 : ℝ)*(sp4) + (9873443371/100000000000000 : ℝ)*(sp7) + (70190311530019/5000000000000 : ℝ)*(f.failure) + (3495096744274141/100000000000000 : ℝ)*(f.sum) + (26245532124569/5226250000000000000000000000 : ℝ)*base66 + (5093138426950444861/4181000000000000000000000000000000 : ℝ)*base67 + (24059797401072444861/4181000000000000000000000000000000 : ℝ)*base69 + (38809743944478555139/4181000000000000000000000000000000 : ℝ)*base72 + (17443459651919/20905000000000000000000000000 : ℝ)*base73 + (6869621461802444861/4181000000000000000000000000000000 : ℝ)*base75 + (36361222627471555139/4181000000000000000000000000000000 : ℝ)*base78 + (6648394139308555139/4181000000000000000000000000000000 : ℝ)*base80 + (29406301708749/20905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (450647/125000000000000000000 : ℝ)*base89 + (450647/125000000000000000000 : ℝ)*base91 + (450647/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4148693424106379248912564053/522625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1608270727/100000000000000 : ℝ)*(base19) + (1842403/125000000000 : ℝ)*(base23) + (5221741/50000000000000 : ℝ)*(upper2) + (316506329/100000000000000 : ℝ)*(upper3) + (28928439/12500000000000 : ℝ)*(upper5) + (1244159590327769/50000000000000 : ℝ)*(major0) + (1244159590327769/50000000000000 : ℝ)*(major1) + (1244159590327769/50000000000000 : ℝ)*(major2) + (3858306501/25000000000000 : ℝ)*(sp1) + (7926340929/25000000000000 : ℝ)*(sp2) + (1775278250017151/50000000000000 : ℝ)*(sp4) + (887634864634393/25000000000000 : ℝ)*(sp5) + (1775261660374093/50000000000000 : ℝ)*(sp6) + (1426081596670633/100000000000000 : ℝ)*(sp7) + (1426081596670633/100000000000000 : ℝ)*(f.failure) + (1775278250017151/50000000000000 : ℝ)*(f.sum) + (102749667866773/20905000000000000000000000000 : ℝ)*base66 + (20482315825941553649/2090500000000000000000000000000000 : ℝ)*base67 + (5753286301794553649/2090500000000000000000000000000000 : ℝ)*base69 + (68861770089053649/2090500000000000000000000000000000 : ℝ)*base71 + (56147917008531/10452500000000000000000000000 : ℝ)*base73 + (9267607986838446351/2090500000000000000000000000000000 : ℝ)*base76 + (329335026321053649/2090500000000000000000000000000000 : ℝ)*base77 + (22259441346701553649/2090500000000000000000000000000000 : ℝ)*base79 + (40312274021901/10452500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8808971/2500000000000000000000 : ℝ)*base90 + (8808971/2500000000000000000000 : ℝ)*base92 + (8808971/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1620_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8833/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1163/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1620_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1620_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1620_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1620_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1620_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1620_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

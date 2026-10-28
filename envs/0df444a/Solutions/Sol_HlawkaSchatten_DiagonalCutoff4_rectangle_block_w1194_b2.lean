-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1194_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:00:59.061825+00:00
-- url     : https://prove2.me/submissions/03bb38fa-50b2-4e0f-b94e-d0343e0c4d44

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
theorem support_rectangle_w1194_s6_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071121419/5000000000 : ℝ)*x 0 + (674042867/1250000000 : ℝ)*x 1 + (526629831/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071121419/5000000000 : ℝ)^8387 ≤ (13022254955769/100000000000000 : ℝ)^6339 := by
    have hnat : (1071121419 : ℕ)^8387*100000000000000^6339 ≤ 13022254955769^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071121419 5000000000 13022254955769 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674042867/1250000000 : ℝ)^8387 ≤ (2760580220089/6250000000000 : ℝ)^6339 := by
    have hnat : (674042867 : ℕ)^8387*6250000000000^6339 ≤ 2760580220089^6339*1250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674042867 1250000000 2760580220089 6250000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526629831/1000000000 : ℝ)^8387 ≤ (42808461495477/100000000000000 : ℝ)^6339 := by
    have hnat : (526629831 : ℕ)^8387*100000000000000^6339 ≤ 42808461495477^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526629831 1000000000 42808461495477 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071121419/5000000000 : ℝ), (674042867/1250000000 : ℝ), (526629831/1000000000 : ℝ)] ![(13022254955769/100000000000000 : ℝ), (2760580220089/6250000000000 : ℝ), (42808461495477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071121419/5000000000 : ℝ)|^8387 ≤ (13022254955769/100000000000000 : ℝ)^6339
        have hw : |(-1071121419/5000000000 : ℝ)|=(1071121419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674042867/1250000000 : ℝ)|^8387 ≤ (2760580220089/6250000000000 : ℝ)^6339
        have hw : |(674042867/1250000000 : ℝ)|=(674042867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526629831/1000000000 : ℝ)|^8387 ≤ (42808461495477/100000000000000 : ℝ)^6339
        have hw : |(526629831/1000000000 : ℝ)|=(526629831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s6_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344608893/10000000000 : ℝ)*x 0 + (-2206165681/10000000000 : ℝ)*x 1 + (263314917/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344608893/10000000000 : ℝ)^8387 ≤ (2182635375307/5000000000000 : ℝ)^6339 := by
    have hnat : (5344608893 : ℕ)^8387*5000000000000^6339 ≤ 2182635375307^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344608893 10000000000 2182635375307 5000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206165681/10000000000 : ℝ)^8387 ≤ (13538830661539/100000000000000 : ℝ)^6339 := by
    have hnat : (2206165681 : ℕ)^8387*100000000000000^6339 ≤ 13538830661539^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206165681 10000000000 13538830661539 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263314917/500000000 : ℝ)^8387 ≤ (42808461818127/100000000000000 : ℝ)^6339 := by
    have hnat : (263314917 : ℕ)^8387*100000000000000^6339 ≤ 42808461818127^6339*500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263314917 500000000 42808461818127 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344608893/10000000000 : ℝ), (-2206165681/10000000000 : ℝ), (263314917/500000000 : ℝ)] ![(2182635375307/5000000000000 : ℝ), (13538830661539/100000000000000 : ℝ), (42808461818127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344608893/10000000000 : ℝ)|^8387 ≤ (2182635375307/5000000000000 : ℝ)^6339
        have hw : |(5344608893/10000000000 : ℝ)|=(5344608893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2206165681/10000000000 : ℝ)|^8387 ≤ (13538830661539/100000000000000 : ℝ)^6339
        have hw : |(-2206165681/10000000000 : ℝ)|=(2206165681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263314917/500000000 : ℝ)|^8387 ≤ (42808461818127/100000000000000 : ℝ)^6339
        have hw : |(263314917/500000000 : ℝ)|=(263314917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s6_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672304473/5000000000 : ℝ)*x 0 + (5266298249/10000000000 : ℝ)*x 1 + (-2206165731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672304473/5000000000 : ℝ)^8387 ≤ (272829425493/625000000000 : ℝ)^6339 := by
    have hnat : (2672304473 : ℕ)^8387*625000000000^6339 ≤ 272829425493^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672304473 5000000000 272829425493 625000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266298249/10000000000 : ℝ)^8387 ≤ (42808460839423/100000000000000 : ℝ)^6339 := by
    have hnat : (5266298249 : ℕ)^8387*100000000000000^6339 ≤ 42808460839423^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266298249 10000000000 42808460839423 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206165731/10000000000 : ℝ)^8387 ≤ (13538831067513/100000000000000 : ℝ)^6339 := by
    have hnat : (2206165731 : ℕ)^8387*100000000000000^6339 ≤ 13538831067513^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206165731 10000000000 13538831067513 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672304473/5000000000 : ℝ), (5266298249/10000000000 : ℝ), (-2206165731/10000000000 : ℝ)] ![(272829425493/625000000000 : ℝ), (42808460839423/100000000000000 : ℝ), (13538831067513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672304473/5000000000 : ℝ)|^8387 ≤ (272829425493/625000000000 : ℝ)^6339
        have hw : |(2672304473/5000000000 : ℝ)|=(2672304473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266298249/10000000000 : ℝ)|^8387 ≤ (42808460839423/100000000000000 : ℝ)^6339
        have hw : |(5266298249/10000000000 : ℝ)|=(5266298249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2206165731/10000000000 : ℝ)|^8387 ≤ (13538831067513/100000000000000 : ℝ)^6339
        have hw : |(-2206165731/10000000000 : ℝ)|=(2206165731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s6_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089346507/2500000000 : ℝ)*x 0 + (169301367/400000000 : ℝ)*x 1 + (4485857153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089346507/2500000000 : ℝ)^8387 ≤ (8329279344193/25000000000000 : ℝ)^6339 := by
    have hnat : (1089346507 : ℕ)^8387*25000000000000^6339 ≤ 8329279344193^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089346507 2500000000 8329279344193 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169301367/400000000 : ℝ)^8387 ≤ (32059946780809/100000000000000 : ℝ)^6339 := by
    have hnat : (169301367 : ℕ)^8387*100000000000000^6339 ≤ 32059946780809^6339*400000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169301367 400000000 32059946780809 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485857153/10000000000 : ℝ)^8387 ≤ (3462293583139/10000000000000 : ℝ)^6339 := by
    have hnat : (4485857153 : ℕ)^8387*10000000000000^6339 ≤ 3462293583139^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485857153 10000000000 3462293583139 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089346507/2500000000 : ℝ), (169301367/400000000 : ℝ), (4485857153/10000000000 : ℝ)] ![(8329279344193/25000000000000 : ℝ), (32059946780809/100000000000000 : ℝ), (3462293583139/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089346507/2500000000 : ℝ)|^8387 ≤ (8329279344193/25000000000000 : ℝ)^6339
        have hw : |(1089346507/2500000000 : ℝ)|=(1089346507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169301367/400000000 : ℝ)|^8387 ≤ (32059946780809/100000000000000 : ℝ)^6339
        have hw : |(169301367/400000000 : ℝ)|=(169301367/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485857153/10000000000 : ℝ)|^8387 ≤ (3462293583139/10000000000000 : ℝ)^6339
        have hw : |(4485857153/10000000000 : ℝ)|=(4485857153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s6_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85689911/400000000 : ℝ)*x 0 + (1053323351/2000000000 : ℝ)*x 1 + (2696011623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85689911/400000000 : ℝ)^8387 ≤ (13022294662733/100000000000000 : ℝ)^6339 := by
    have hnat : (85689911 : ℕ)^8387*100000000000000^6339 ≤ 13022294662733^6339*400000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85689911 400000000 13022294662733 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053323351/2000000000 : ℝ)^8387 ≤ (42811886402069/100000000000000 : ℝ)^6339 := by
    have hnat : (1053323351 : ℕ)^8387*100000000000000^6339 ≤ 42811886402069^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053323351 2000000000 42811886402069 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696011623/5000000000 : ℝ)^8387 ≤ (44165818917173/100000000000000 : ℝ)^6339 := by
    have hnat : (2696011623 : ℕ)^8387*100000000000000^6339 ≤ 44165818917173^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696011623 5000000000 44165818917173 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85689911/400000000 : ℝ), (1053323351/2000000000 : ℝ), (2696011623/5000000000 : ℝ)] ![(13022294662733/100000000000000 : ℝ), (42811886402069/100000000000000 : ℝ), (44165818917173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85689911/400000000 : ℝ)|^8387 ≤ (13022294662733/100000000000000 : ℝ)^6339
        have hw : |(-85689911/400000000 : ℝ)|=(85689911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053323351/2000000000 : ℝ)|^8387 ≤ (42811886402069/100000000000000 : ℝ)^6339
        have hw : |(1053323351/2000000000 : ℝ)|=(1053323351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696011623/5000000000 : ℝ)|^8387 ≤ (44165818917173/100000000000000 : ℝ)^6339
        have hw : |(2696011623/5000000000 : ℝ)|=(2696011623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s6_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656277339/5000000000 : ℝ)*x 0 + (-2080440629/10000000000 : ℝ)*x 1 + (5392023243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656277339/5000000000 : ℝ)^8387 ≤ (21653326400449/50000000000000 : ℝ)^6339 := by
    have hnat : (2656277339 : ℕ)^8387*50000000000000^6339 ≤ 21653326400449^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656277339 5000000000 21653326400449 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080440629/10000000000 : ℝ)^8387 ≤ (78297051893/625000000000 : ℝ)^6339 := by
    have hnat : (2080440629 : ℕ)^8387*625000000000^6339 ≤ 78297051893^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080440629 10000000000 78297051893 625000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392023243/10000000000 : ℝ)^8387 ≤ (44165818884661/100000000000000 : ℝ)^6339 := by
    have hnat : (5392023243 : ℕ)^8387*100000000000000^6339 ≤ 44165818884661^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392023243 10000000000 44165818884661 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656277339/5000000000 : ℝ), (-2080440629/10000000000 : ℝ), (5392023243/10000000000 : ℝ)] ![(21653326400449/50000000000000 : ℝ), (78297051893/625000000000 : ℝ), (44165818884661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656277339/5000000000 : ℝ)|^8387 ≤ (21653326400449/50000000000000 : ℝ)^6339
        have hw : |(2656277339/5000000000 : ℝ)|=(2656277339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080440629/10000000000 : ℝ)|^8387 ≤ (78297051893/625000000000 : ℝ)^6339
        have hw : |(-2080440629/10000000000 : ℝ)|=(2080440629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392023243/10000000000 : ℝ)|^8387 ≤ (44165818884661/100000000000000 : ℝ)^6339
        have hw : |(5392023243/10000000000 : ℝ)|=(5392023243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s6_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531255469/1000000000 : ℝ)*x 0 + (5392023211/10000000000 : ℝ)*x 1 + (-2080440657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531255469/1000000000 : ℝ)^8387 ≤ (10826663232581/25000000000000 : ℝ)^6339 := by
    have hnat : (531255469 : ℕ)^8387*25000000000000^6339 ≤ 10826663232581^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531255469 1000000000 10826663232581 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392023211/10000000000 : ℝ)^8387 ≤ (11041454634467/25000000000000 : ℝ)^6339 := by
    have hnat : (5392023211 : ℕ)^8387*25000000000000^6339 ≤ 11041454634467^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392023211 10000000000 11041454634467 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080440657/10000000000 : ℝ)^8387 ≤ (3131882131489/25000000000000 : ℝ)^6339 := by
    have hnat : (2080440657 : ℕ)^8387*25000000000000^6339 ≤ 3131882131489^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080440657 10000000000 3131882131489 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531255469/1000000000 : ℝ), (5392023211/10000000000 : ℝ), (-2080440657/10000000000 : ℝ)] ![(10826663232581/25000000000000 : ℝ), (11041454634467/25000000000000 : ℝ), (3131882131489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531255469/1000000000 : ℝ)|^8387 ≤ (10826663232581/25000000000000 : ℝ)^6339
        have hw : |(531255469/1000000000 : ℝ)|=(531255469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392023211/10000000000 : ℝ)|^8387 ≤ (11041454634467/25000000000000 : ℝ)^6339
        have hw : |(5392023211/10000000000 : ℝ)|=(5392023211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080440657/10000000000 : ℝ)|^8387 ≤ (3131882131489/25000000000000 : ℝ)^6339
        have hw : |(-2080440657/10000000000 : ℝ)|=(2080440657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s6_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357395663/10000000000 : ℝ)*x 0 + (897043381/2000000000 : ℝ)*x 1 + (4233176803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357395663/10000000000 : ℝ)^8387 ≤ (1041162964019/3125000000000 : ℝ)^6339 := by
    have hnat : (4357395663 : ℕ)^8387*3125000000000^6339 ≤ 1041162964019^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357395663 10000000000 1041162964019 3125000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897043381/2000000000 : ℝ)^8387 ≤ (34616397866873/100000000000000 : ℝ)^6339 := by
    have hnat : (897043381 : ℕ)^8387*100000000000000^6339 ≤ 34616397866873^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897043381 2000000000 34616397866873 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233176803/10000000000 : ℝ)^8387 ≤ (32066387264881/100000000000000 : ℝ)^6339 := by
    have hnat : (4233176803 : ℕ)^8387*100000000000000^6339 ≤ 32066387264881^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233176803 10000000000 32066387264881 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357395663/10000000000 : ℝ), (897043381/2000000000 : ℝ), (4233176803/10000000000 : ℝ)] ![(1041162964019/3125000000000 : ℝ), (34616397866873/100000000000000 : ℝ), (32066387264881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357395663/10000000000 : ℝ)|^8387 ≤ (1041162964019/3125000000000 : ℝ)^6339
        have hw : |(4357395663/10000000000 : ℝ)|=(4357395663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897043381/2000000000 : ℝ)|^8387 ≤ (34616397866873/100000000000000 : ℝ)^6339
        have hw : |(897043381/2000000000 : ℝ)|=(897043381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233176803/10000000000 : ℝ)|^8387 ≤ (32066387264881/100000000000000 : ℝ)^6339
        have hw : |(4233176803/10000000000 : ℝ)|=(4233176803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5707/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3521/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11389/100000 : ℝ) ^ (4193/1024 : ℝ) ≤ (13695140603000359/100000000000000000000 : ℝ) := by
    have hpowers : (11389/100000 : ℝ)^4193 ≤ (13695140603000359/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11389 : ℕ)^4193*100000000000000000000^1024 ≤ 13695140603000359^1024*100000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11389 100000 13695140603000359 100000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11389/100000 : ℝ)) (X := (13695140603000359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1411/10000 : ℝ) ^ (4193/1024 : ℝ) ≤ (1646325393191631/5000000000000000000 : ℝ) := by
    have hpowers : (1411/10000 : ℝ)^4193 ≤ (1646325393191631/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1411 : ℕ)^4193*5000000000000000000^1024 ≤ 1646325393191631^1024*10000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 10000 1646325393191631 5000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/10000 : ℝ)) (X := (1646325393191631/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013695140603000359/50000000000000000000 : ℝ) ≤ (10000668846776329/10000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (50013695140603000359/50000000000000000000 : ℝ)^1024 ≤ (10000668846776329/10000000000000000 : ℝ)^4193 := by
      have hnat : (50013695140603000359 : ℕ)^1024*10000000000000000^4193 ≤ 10000668846776329^4193*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013695140603000359 50000000000000000000 10000668846776329 10000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668846776329/10000000000000000 : ℝ)) (X := (50013695140603000359/50000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046621648466832979/100000000000000000000 : ℝ) ≤ (2500284594320427/2500000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (100046621648466832979/100000000000000000000 : ℝ)^1024 ≤ (2500284594320427/2500000000000000 : ℝ)^4193 := by
      have hnat : (100046621648466832979 : ℕ)^1024*2500000000000000^4193 ≤ 2500284594320427^4193*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046621648466832979 100000000000000000000 2500284594320427 2500000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500284594320427/2500000000000000 : ℝ)) (X := (100046621648466832979/100000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501646325393191631/2500000000000000000 : ℝ) ≤ (10001607907787087/10000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (2501646325393191631/2500000000000000000 : ℝ)^1024 ≤ (10001607907787087/10000000000000000 : ℝ)^4193 := by
      have hnat : (2501646325393191631 : ℕ)^1024*10000000000000000^4193 ≤ 10001607907787087^4193*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501646325393191631 2500000000000000000 10001607907787087 10000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001607907787087/10000000000000000 : ℝ)) (X := (2501646325393191631/2500000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13695140603000359/100000000000000000000 : ℝ) ≤ ((27201124966226868347/27210000000000000000 : ℝ)+2*(469530505379/272100000000000 : ℝ)*(11389/100000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (27201124966226868347/27210000000000000000 : ℝ)+2*(469530505379/272100000000000 : ℝ)*(11389/100000 : ℝ)=(10000668846776329/10000000000000000 : ℝ) by norm_num, show 1+2*(13695140603000359/100000000000000000000 : ℝ)=(50013695140603000359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1646325393191631/5000000000000000000 : ℝ)+(13695140603000359/100000000000000000000 : ℝ) ≤ ((27201124966226868347/27210000000000000000 : ℝ)+(469530505379/272100000000000 : ℝ)*((1411/10000 : ℝ)+(11389/100000 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (27201124966226868347/27210000000000000000 : ℝ)+(469530505379/272100000000000 : ℝ)*((1411/10000 : ℝ)+(11389/100000 : ℝ))=(2500284594320427/2500000000000000 : ℝ) by norm_num, show 1+(1646325393191631/5000000000000000000 : ℝ)+(13695140603000359/100000000000000000000 : ℝ)=(100046621648466832979/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1646325393191631/5000000000000000000 : ℝ) ≤ ((27201124966226868347/27210000000000000000 : ℝ)+2*(469530505379/272100000000000 : ℝ)*(1411/10000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (27201124966226868347/27210000000000000000 : ℝ)+2*(469530505379/272100000000000 : ℝ)*(1411/10000 : ℝ)=(10001607907787087/10000000000000000 : ℝ) by norm_num, show 1+2*(1646325393191631/5000000000000000000 : ℝ)=(2501646325393191631/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27201124966226868347/27210000000000000000 : ℝ)*(X 1 0+X 2 0)+(469530505379/272100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (27201124966226868347/27210000000000000000 : ℝ)) (alpha := (469530505379/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27201124966226868347/27210000000000000000 : ℝ)*(X 0 1+X 2 1)+(469530505379/272100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (27201124966226868347/27210000000000000000 : ℝ)) (alpha := (469530505379/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27201124966226868347/27210000000000000000 : ℝ)*(X 0 2+X 1 2)+(469530505379/272100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (27201124966226868347/27210000000000000000 : ℝ)) (alpha := (469530505379/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071121419/5000000000 : ℝ)*X 0 0+(674042867/1250000000 : ℝ)*X 0 1+(526629831/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344608893/10000000000 : ℝ)*X 1 0+(-2206165681/10000000000 : ℝ)*X 1 1+(263314917/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672304473/5000000000 : ℝ)*X 2 0+(5266298249/10000000000 : ℝ)*X 2 1+(-2206165731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089346507/2500000000 : ℝ)*X 0 0+(169301367/400000000 : ℝ)*X 0 1+(4485857153/10000000000 : ℝ)*X 0 2+(1089346507/2500000000 : ℝ)*X 1 0+(169301367/400000000 : ℝ)*X 1 1+(4485857153/10000000000 : ℝ)*X 1 2+(1089346507/2500000000 : ℝ)*X 2 0+(169301367/400000000 : ℝ)*X 2 1+(4485857153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85689911/400000000 : ℝ)*X 0 0+(1053323351/2000000000 : ℝ)*X 0 1+(2696011623/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656277339/5000000000 : ℝ)*X 1 0+(-2080440629/10000000000 : ℝ)*X 1 1+(5392023243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531255469/1000000000 : ℝ)*X 2 0+(5392023211/10000000000 : ℝ)*X 2 1+(-2080440657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357395663/10000000000 : ℝ)*X 0 0+(897043381/2000000000 : ℝ)*X 0 1+(4233176803/10000000000 : ℝ)*X 0 2+(4357395663/10000000000 : ℝ)*X 1 0+(897043381/2000000000 : ℝ)*X 1 1+(4233176803/10000000000 : ℝ)*X 1 2+(4357395663/10000000000 : ℝ)*X 2 0+(897043381/2000000000 : ℝ)*X 2 1+(4233176803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1890914722664480336841410881/226750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (318170409/20000000000000 : ℝ)*(base19) + (1436979041/100000000000000 : ℝ)*(base23) + (15536017/12500000000000 : ℝ)*(lower2) + (3733431/1250000000000 : ℝ)*(upper3) + (30291401/50000000000000 : ℝ)*(upper5) + (2970339232918723/50000000000000 : ℝ)*(major0) + (2970339232918723/50000000000000 : ℝ)*(major1) + (2970339232918723/50000000000000 : ℝ)*(major2) + (7933743246853267/100000000000000 : ℝ)*(sp0) + (198344492263031/2500000000000 : ℝ)*(sp1) + (1586755968878849/20000000000000 : ℝ)*(sp2) + (3947549264453223/100000000000000 : ℝ)*(sp3) + (38034520019/100000000000000 : ℝ)*(sp4) + (26107874879/100000000000000 : ℝ)*(sp7) + (1973787686164051/50000000000000 : ℝ)*(f.failure) + (1586756256274657/20000000000000 : ℝ)*(f.sum) + (4317450487679/3401250000000000000000000000 : ℝ)*base66 + (27872124746834439119/1360500000000000000000000000000000 : ℝ)*base68 + (984882100574060881/1360500000000000000000000000000000 : ℝ)*base69 + (966454398656439119/1360500000000000000000000000000000 : ℝ)*base72 + (19279470185683/6802500000000000000000000000 : ℝ)*base74 + (4765000622163939119/1360500000000000000000000000000000 : ℝ)*base76 + (4596987354881439119/1360500000000000000000000000000000 : ℝ)*base78 + (4882066832511560881/1360500000000000000000000000000000 : ℝ)*base79 + (3221405626871/13605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (23913099/2500000000000000000000 : ℝ)*base89 + (23913099/2500000000000000000000 : ℝ)*base91 + (23913099/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (698369434231140719582699681/226750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (274343823/25000000000000 : ℝ)*(base19) + (1155148981/100000000000000 : ℝ)*(base23) + (3367517/12500000000000 : ℝ)*(upper2) + (22653381/25000000000000 : ℝ)*(upper3) + (4018643/3125000000000 : ℝ)*(upper5) + (5970845848169123/100000000000000 : ℝ)*(major0) + (5970845848169123/100000000000000 : ℝ)*(major1) + (5970845848169123/100000000000000 : ℝ)*(major2) + (32822633387/100000000000000 : ℝ)*(sp1) + (3100803347/10000000000000 : ℝ)*(sp2) + (996758752944411/12500000000000 : ℝ)*(sp4) + (7974036103546609/100000000000000 : ℝ)*(sp5) + (7974037860372837/100000000000000 : ℝ)*(sp6) + (991905392529827/25000000000000 : ℝ)*(sp7) + (991905392529827/25000000000000 : ℝ)*(f.failure) + (996758752944411/12500000000000 : ℝ)*(f.sum) + (81418935426803/13605000000000000000000000000 : ℝ)*base66 + (2771523999393149681/2721000000000000000000000000000000 : ℝ)*base67 + (27148823263838850319/2721000000000000000000000000000000 : ℝ)*base70 + (28918620233363850319/2721000000000000000000000000000000 : ℝ)*base72 + (61572725048243/13605000000000000000000000000 : ℝ)*base74 + (989906705237850319/2721000000000000000000000000000000 : ℝ)*base76 + (29216517101060850319/2721000000000000000000000000000000 : ℝ)*base78 + (18350682559643850319/2721000000000000000000000000000000 : ℝ)*base80 + (977847084019/425156250000000000000000000 : ℝ)*base82 + (17145723/1250000000000000000000 : ℝ)*base89 + (17145723/1250000000000000000000 : ℝ)*base91 + (17145723/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1194_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1194_s7_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-13389151/62500000 : ℝ)*x 0 + (5392093657/10000000000 : ℝ)*x 1 + (2633266777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13389151/62500000 : ℝ)^8387 ≤ (13022426443093/100000000000000 : ℝ)^6339 := by
    have hnat : (13389151 : ℕ)^8387*100000000000000^6339 ≤ 13022426443093^6339*62500000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13389151 62500000 13022426443093 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392093657/10000000000 : ℝ)^8387 ≤ (4416658198273/10000000000000 : ℝ)^6339 := by
    have hnat : (5392093657 : ℕ)^8387*10000000000000^6339 ≤ 4416658198273^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392093657 10000000000 4416658198273 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633266777/5000000000 : ℝ)^8387 ≤ (21405495780429/50000000000000 : ℝ)^6339 := by
    have hnat : (2633266777 : ℕ)^8387*50000000000000^6339 ≤ 21405495780429^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633266777 5000000000 21405495780429 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13389151/62500000 : ℝ), (5392093657/10000000000 : ℝ), (2633266777/5000000000 : ℝ)] ![(13022426443093/100000000000000 : ℝ), (4416658198273/10000000000000 : ℝ), (21405495780429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13389151/62500000 : ℝ)|^8387 ≤ (13022426443093/100000000000000 : ℝ)^6339
        have hw : |(-13389151/62500000 : ℝ)|=(13389151/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392093657/10000000000 : ℝ)|^8387 ≤ (4416658198273/10000000000000 : ℝ)^6339
        have hw : |(5392093657/10000000000 : ℝ)|=(5392093657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633266777/5000000000 : ℝ)|^8387 ≤ (21405495780429/50000000000000 : ℝ)^6339
        have hw : |(2633266777/5000000000 : ℝ)|=(2633266777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s7_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068909139/2000000000 : ℝ)*x 0 + (-2205937953/10000000000 : ℝ)*x 1 + (5266533759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068909139/2000000000 : ℝ)^8387 ≤ (5456503070551/12500000000000 : ℝ)^6339 := by
    have hnat : (1068909139 : ℕ)^8387*12500000000000^6339 ≤ 5456503070551^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068909139 2000000000 5456503070551 12500000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205937953/10000000000 : ℝ)^8387 ≤ (13536981656421/100000000000000 : ℝ)^6339 := by
    have hnat : (2205937953 : ℕ)^8387*100000000000000^6339 ≤ 13536981656421^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205937953 10000000000 13536981656421 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266533759/10000000000 : ℝ)^8387 ≤ (42810993765663/100000000000000 : ℝ)^6339 := by
    have hnat : (5266533759 : ℕ)^8387*100000000000000^6339 ≤ 42810993765663^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266533759 10000000000 42810993765663 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068909139/2000000000 : ℝ), (-2205937953/10000000000 : ℝ), (5266533759/10000000000 : ℝ)] ![(5456503070551/12500000000000 : ℝ), (13536981656421/100000000000000 : ℝ), (42810993765663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068909139/2000000000 : ℝ)|^8387 ≤ (5456503070551/12500000000000 : ℝ)^6339
        have hw : |(1068909139/2000000000 : ℝ)|=(1068909139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205937953/10000000000 : ℝ)|^8387 ≤ (13536981656421/100000000000000 : ℝ)^6339
        have hw : |(-2205937953/10000000000 : ℝ)|=(2205937953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266533759/10000000000 : ℝ)|^8387 ≤ (42810993765663/100000000000000 : ℝ)^6339
        have hw : |(5266533759/10000000000 : ℝ)|=(5266533759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s7_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344545743/10000000000 : ℝ)*x 0 + (2633266991/5000000000 : ℝ)*x 1 + (-441187519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344545743/10000000000 : ℝ)^8387 ≤ (43652025083113/100000000000000 : ℝ)^6339 := by
    have hnat : (5344545743 : ℕ)^8387*100000000000000^6339 ≤ 43652025083113^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344545743 10000000000 43652025083113 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633266991/5000000000 : ℝ)^8387 ≤ (42810996164061/100000000000000 : ℝ)^6339 := by
    have hnat : (2633266991 : ℕ)^8387*100000000000000^6339 ≤ 42810996164061^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633266991 5000000000 42810996164061 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441187519/2000000000 : ℝ)^8387 ≤ (676848937487/5000000000000 : ℝ)^6339 := by
    have hnat : (441187519 : ℕ)^8387*5000000000000^6339 ≤ 676848937487^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441187519 2000000000 676848937487 5000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344545743/10000000000 : ℝ), (2633266991/5000000000 : ℝ), (-441187519/2000000000 : ℝ)] ![(43652025083113/100000000000000 : ℝ), (42810996164061/100000000000000 : ℝ), (676848937487/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344545743/10000000000 : ℝ)|^8387 ≤ (43652025083113/100000000000000 : ℝ)^6339
        have hw : |(5344545743/10000000000 : ℝ)|=(5344545743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633266991/5000000000 : ℝ)|^8387 ≤ (42810996164061/100000000000000 : ℝ)^6339
        have hw : |(2633266991/5000000000 : ℝ)|=(2633266991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441187519/2000000000 : ℝ)|^8387 ≤ (676848937487/5000000000000 : ℝ)^6339
        have hw : |(-441187519/2000000000 : ℝ)|=(441187519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s7_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357398527/10000000000 : ℝ)*x 0 + (4233019631/10000000000 : ℝ)*x 1 + (4485368329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357398527/10000000000 : ℝ)^8387 ≤ (33317243822087/100000000000000 : ℝ)^6339 := by
    have hnat : (4357398527 : ℕ)^8387*100000000000000^6339 ≤ 33317243822087^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357398527 10000000000 33317243822087 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233019631/10000000000 : ℝ)^8387 ≤ (32064812041709/100000000000000 : ℝ)^6339 := by
    have hnat : (4233019631 : ℕ)^8387*100000000000000^6339 ≤ 32064812041709^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233019631 10000000000 32064812041709 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485368329/10000000000 : ℝ)^8387 ≤ (34617944122871/100000000000000 : ℝ)^6339 := by
    have hnat : (4485368329 : ℕ)^8387*100000000000000^6339 ≤ 34617944122871^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485368329 10000000000 34617944122871 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357398527/10000000000 : ℝ), (4233019631/10000000000 : ℝ), (4485368329/10000000000 : ℝ)] ![(33317243822087/100000000000000 : ℝ), (32064812041709/100000000000000 : ℝ), (34617944122871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357398527/10000000000 : ℝ)|^8387 ≤ (33317243822087/100000000000000 : ℝ)^6339
        have hw : |(4357398527/10000000000 : ℝ)|=(4357398527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233019631/10000000000 : ℝ)|^8387 ≤ (32064812041709/100000000000000 : ℝ)^6339
        have hw : |(4233019631/10000000000 : ℝ)|=(4233019631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485368329/10000000000 : ℝ)|^8387 ≤ (34617944122871/100000000000000 : ℝ)^6339
        have hw : |(4485368329/10000000000 : ℝ)|=(4485368329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s7_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142268511/10000000000 : ℝ)*x 0 + (2633424887/5000000000 : ℝ)*x 1 + (26958883/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142268511/10000000000 : ℝ)^8387 ≤ (13022461437127/100000000000000 : ℝ)^6339 := by
    have hnat : (2142268511 : ℕ)^8387*100000000000000^6339 ≤ 13022461437127^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142268511 10000000000 13022461437127 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633424887/5000000000 : ℝ)^8387 ≤ (42814392586209/100000000000000 : ℝ)^6339 := by
    have hnat : (2633424887 : ℕ)^8387*100000000000000^6339 ≤ 42814392586209^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633424887 5000000000 42814392586209 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26958883/50000000 : ℝ)^8387 ≤ (4416314596437/10000000000000 : ℝ)^6339 := by
    have hnat : (26958883 : ℕ)^8387*10000000000000^6339 ≤ 4416314596437^6339*50000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26958883 50000000 4416314596437 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142268511/10000000000 : ℝ), (2633424887/5000000000 : ℝ), (26958883/50000000 : ℝ)] ![(13022461437127/100000000000000 : ℝ), (42814392586209/100000000000000 : ℝ), (4416314596437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142268511/10000000000 : ℝ)|^8387 ≤ (13022461437127/100000000000000 : ℝ)^6339
        have hw : |(-2142268511/10000000000 : ℝ)|=(2142268511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633424887/5000000000 : ℝ)|^8387 ≤ (42814392586209/100000000000000 : ℝ)^6339
        have hw : |(2633424887/5000000000 : ℝ)|=(2633424887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26958883/50000000 : ℝ)|^8387 ≤ (4416314596437/10000000000000 : ℝ)^6339
        have hw : |(26958883/50000000 : ℝ)|=(26958883/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s7_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106252299/200000000 : ℝ)*x 0 + (-2080694533/10000000000 : ℝ)*x 1 + (1347944149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106252299/200000000 : ℝ)^8387 ≤ (2706706428811/6250000000000 : ℝ)^6339 := by
    have hnat : (106252299 : ℕ)^8387*6250000000000^6339 ≤ 2706706428811^6339*200000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106252299 200000000 2706706428811 6250000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080694533/10000000000 : ℝ)^8387 ≤ (6264775600619/50000000000000 : ℝ)^6339 := by
    have hnat : (2080694533 : ℕ)^8387*50000000000000^6339 ≤ 6264775600619^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080694533 10000000000 6264775600619 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347944149/2500000000 : ℝ)^8387 ≤ (44163145921021/100000000000000 : ℝ)^6339 := by
    have hnat : (1347944149 : ℕ)^8387*100000000000000^6339 ≤ 44163145921021^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347944149 2500000000 44163145921021 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106252299/200000000 : ℝ), (-2080694533/10000000000 : ℝ), (1347944149/2500000000 : ℝ)] ![(2706706428811/6250000000000 : ℝ), (6264775600619/50000000000000 : ℝ), (44163145921021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106252299/200000000 : ℝ)|^8387 ≤ (2706706428811/6250000000000 : ℝ)^6339
        have hw : |(106252299/200000000 : ℝ)|=(106252299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080694533/10000000000 : ℝ)|^8387 ≤ (6264775600619/50000000000000 : ℝ)^6339
        have hw : |(-2080694533/10000000000 : ℝ)|=(2080694533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347944149/2500000000 : ℝ)|^8387 ≤ (44163145921021/100000000000000 : ℝ)^6339
        have hw : |(1347944149/2500000000 : ℝ)|=(1347944149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s7_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656307481/5000000000 : ℝ)*x 0 + (5391776593/10000000000 : ℝ)*x 1 + (-1040347261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656307481/5000000000 : ℝ)^8387 ≤ (43307302990401/100000000000000 : ℝ)^6339 := by
    have hnat : (2656307481 : ℕ)^8387*100000000000000^6339 ≤ 43307302990401^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656307481 5000000000 43307302990401 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391776593/10000000000 : ℝ)^8387 ≤ (4416314588851/10000000000000 : ℝ)^6339 := by
    have hnat : (5391776593 : ℕ)^8387*10000000000000^6339 ≤ 4416314588851^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391776593 10000000000 4416314588851 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040347261/5000000000 : ℝ)^8387 ≤ (12529551113597/100000000000000 : ℝ)^6339 := by
    have hnat : (1040347261 : ℕ)^8387*100000000000000^6339 ≤ 12529551113597^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040347261 5000000000 12529551113597 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656307481/5000000000 : ℝ), (5391776593/10000000000 : ℝ), (-1040347261/5000000000 : ℝ)] ![(43307302990401/100000000000000 : ℝ), (4416314588851/10000000000000 : ℝ), (12529551113597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656307481/5000000000 : ℝ)|^8387 ≤ (43307302990401/100000000000000 : ℝ)^6339
        have hw : |(2656307481/5000000000 : ℝ)|=(2656307481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391776593/10000000000 : ℝ)|^8387 ≤ (4416314588851/10000000000000 : ℝ)^6339
        have hw : |(5391776593/10000000000 : ℝ)|=(5391776593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040347261/5000000000 : ℝ)|^8387 ≤ (12529551113597/100000000000000 : ℝ)^6339
        have hw : |(-1040347261/5000000000 : ℝ)|=(1040347261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s7_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357407777/10000000000 : ℝ)*x 0 + (2242366691/5000000000 : ℝ)*x 1 + (4233657201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357407777/10000000000 : ℝ)^8387 ≤ (33317337399181/100000000000000 : ℝ)^6339 := by
    have hnat : (4357407777 : ℕ)^8387*100000000000000^6339 ≤ 33317337399181^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357407777 10000000000 33317337399181 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242366691/5000000000 : ℝ)^8387 ≤ (34611460517169/100000000000000 : ℝ)^6339 := by
    have hnat : (2242366691 : ℕ)^8387*100000000000000^6339 ≤ 34611460517169^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242366691 5000000000 34611460517169 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233657201/10000000000 : ℝ)^8387 ≤ (32071202069503/100000000000000 : ℝ)^6339 := by
    have hnat : (4233657201 : ℕ)^8387*100000000000000^6339 ≤ 32071202069503^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233657201 10000000000 32071202069503 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357407777/10000000000 : ℝ), (2242366691/5000000000 : ℝ), (4233657201/10000000000 : ℝ)] ![(33317337399181/100000000000000 : ℝ), (34611460517169/100000000000000 : ℝ), (32071202069503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357407777/10000000000 : ℝ)|^8387 ≤ (33317337399181/100000000000000 : ℝ)^6339
        have hw : |(4357407777/10000000000 : ℝ)|=(4357407777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242366691/5000000000 : ℝ)|^8387 ≤ (34611460517169/100000000000000 : ℝ)^6339
        have hw : |(2242366691/5000000000 : ℝ)|=(2242366691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233657201/10000000000 : ℝ)|^8387 ≤ (32071202069503/100000000000000 : ℝ)^6339
        have hw : |(4233657201/10000000000 : ℝ)|=(4233657201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11419/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14079/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5707/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5707/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5707/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5707/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5707/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5707/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5707/50000 : ℝ) ^ (4193/1024 : ℝ) ≤ (13818655887872417/100000000000000000000 : ℝ) := by
    have hpowers : (5707/50000 : ℝ)^4193 ≤ (13818655887872417/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5707 : ℕ)^4193*100000000000000000000^1024 ≤ 13818655887872417^1024*50000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5707 50000 13818655887872417 100000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5707/50000 : ℝ)) (X := (13818655887872417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3521/25000 : ℝ) ^ (4193/1024 : ℝ) ≤ (4084847243924451/12500000000000000000 : ℝ) := by
    have hpowers : (3521/25000 : ℝ)^4193 ≤ (4084847243924451/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3521 : ℕ)^4193*12500000000000000000^1024 ≤ 4084847243924451^1024*25000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 25000 4084847243924451 12500000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/25000 : ℝ)) (X := (4084847243924451/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013818655887872417/50000000000000000000 : ℝ) ≤ (5000337439208753/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (50013818655887872417/50000000000000000000 : ℝ)^1024 ≤ (5000337439208753/5000000000000000 : ℝ)^4193 := by
      have hnat : (50013818655887872417 : ℕ)^1024*5000000000000000^4193 ≤ 5000337439208753^4193*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013818655887872417 50000000000000000000 5000337439208753 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000337439208753/5000000000000000 : ℝ)) (X := (50013818655887872417/50000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001859897353570721/4000000000000000000 : ℝ) ≤ (10001135344821939/10000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (4001859897353570721/4000000000000000000 : ℝ)^1024 ≤ (10001135344821939/10000000000000000 : ℝ)^4193 := by
      have hnat : (4001859897353570721 : ℕ)^1024*10000000000000000^4193 ≤ 10001135344821939^4193*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001859897353570721 4000000000000000000 10001135344821939 10000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001135344821939/10000000000000000 : ℝ)) (X := (4001859897353570721/4000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254084847243924451/6250000000000000000 : ℝ) ≤ (2500398952806593/2500000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (6254084847243924451/6250000000000000000 : ℝ)^1024 ≤ (2500398952806593/2500000000000000 : ℝ)^4193 := by
      have hnat : (6254084847243924451 : ℕ)^1024*2500000000000000^4193 ≤ 2500398952806593^4193*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254084847243924451 6250000000000000000 2500398952806593 2500000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500398952806593/2500000000000000 : ℝ)) (X := (6254084847243924451/6250000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13818655887872417/100000000000000000000 : ℝ) ≤ ((1668205649893396531/1668750000000000000 : ℝ)+2*(460466404433/267000000000000 : ℝ)*(5707/50000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (1668205649893396531/1668750000000000000 : ℝ)+2*(460466404433/267000000000000 : ℝ)*(5707/50000 : ℝ)=(5000337439208753/5000000000000000 : ℝ) by norm_num, show 1+2*(13818655887872417/100000000000000000000 : ℝ)=(50013818655887872417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4084847243924451/12500000000000000000 : ℝ)+(13818655887872417/100000000000000000000 : ℝ) ≤ ((1668205649893396531/1668750000000000000 : ℝ)+(460466404433/267000000000000 : ℝ)*((3521/25000 : ℝ)+(5707/50000 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (1668205649893396531/1668750000000000000 : ℝ)+(460466404433/267000000000000 : ℝ)*((3521/25000 : ℝ)+(5707/50000 : ℝ))=(10001135344821939/10000000000000000 : ℝ) by norm_num, show 1+(4084847243924451/12500000000000000000 : ℝ)+(13818655887872417/100000000000000000000 : ℝ)=(4001859897353570721/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4084847243924451/12500000000000000000 : ℝ) ≤ ((1668205649893396531/1668750000000000000 : ℝ)+2*(460466404433/267000000000000 : ℝ)*(3521/25000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (1668205649893396531/1668750000000000000 : ℝ)+2*(460466404433/267000000000000 : ℝ)*(3521/25000 : ℝ)=(2500398952806593/2500000000000000 : ℝ) by norm_num, show 1+2*(4084847243924451/12500000000000000000 : ℝ)=(6254084847243924451/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1668205649893396531/1668750000000000000 : ℝ)*(X 1 0+X 2 0)+(460466404433/267000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (1668205649893396531/1668750000000000000 : ℝ)) (alpha := (460466404433/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1668205649893396531/1668750000000000000 : ℝ)*(X 0 1+X 2 1)+(460466404433/267000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (1668205649893396531/1668750000000000000 : ℝ)) (alpha := (460466404433/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1668205649893396531/1668750000000000000 : ℝ)*(X 0 2+X 1 2)+(460466404433/267000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (1668205649893396531/1668750000000000000 : ℝ)) (alpha := (460466404433/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-13389151/62500000 : ℝ)*X 0 0+(5392093657/10000000000 : ℝ)*X 0 1+(2633266777/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068909139/2000000000 : ℝ)*X 1 0+(-2205937953/10000000000 : ℝ)*X 1 1+(5266533759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344545743/10000000000 : ℝ)*X 2 0+(2633266991/5000000000 : ℝ)*X 2 1+(-441187519/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357398527/10000000000 : ℝ)*X 0 0+(4233019631/10000000000 : ℝ)*X 0 1+(4485368329/10000000000 : ℝ)*X 0 2+(4357398527/10000000000 : ℝ)*X 1 0+(4233019631/10000000000 : ℝ)*X 1 1+(4485368329/10000000000 : ℝ)*X 1 2+(4357398527/10000000000 : ℝ)*X 2 0+(4233019631/10000000000 : ℝ)*X 2 1+(4485368329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2142268511/10000000000 : ℝ)*X 0 0+(2633424887/5000000000 : ℝ)*X 0 1+(26958883/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106252299/200000000 : ℝ)*X 1 0+(-2080694533/10000000000 : ℝ)*X 1 1+(1347944149/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656307481/5000000000 : ℝ)*X 2 0+(5391776593/10000000000 : ℝ)*X 2 1+(-1040347261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357407777/10000000000 : ℝ)*X 0 0+(2242366691/5000000000 : ℝ)*X 0 1+(4233657201/10000000000 : ℝ)*X 0 2+(4357407777/10000000000 : ℝ)*X 1 0+(2242366691/5000000000 : ℝ)*X 1 1+(4233657201/10000000000 : ℝ)*X 1 2+(4357407777/10000000000 : ℝ)*X 2 0+(2242366691/5000000000 : ℝ)*X 2 1+(4233657201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (271145878731909913128751903/27812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63113373/5000000000000 : ℝ)*(base19) + (223014693/20000000000000 : ℝ)*(base23) + (98877509/50000000000000 : ℝ)*(upper3) + (116897507/100000000000000 : ℝ)*(upper4) + (127322827/20000000000000 : ℝ)*(upper5) + (5963587774283171/100000000000000 : ℝ)*(major0) + (5963587774283171/100000000000000 : ℝ)*(major1) + (5963587774283171/100000000000000 : ℝ)*(major2) + (318573267356803/4000000000000 : ℝ)*(sp0) + (7964375374627087/100000000000000 : ℝ)*(sp1) + (7964375521821083/100000000000000 : ℝ)*(sp2) + (495348531748649/12500000000000 : ℝ)*(sp3) + (44952974473/100000000000000 : ℝ)*(sp4) + (5166356873/50000000000000 : ℝ)*(sp7) + (495349823337867/12500000000000 : ℝ)*(f.failure) + (1991094159223637/25000000000000 : ℝ)*(f.sum) + (53127499795007/13350000000000000000000000000 : ℝ)*base66 + (285596366004925483/55625000000000000000000000000000 : ℝ)*base68 + (956652637071800483/55625000000000000000000000000000 : ℝ)*base70 + (433157408698675483/55625000000000000000000000000000 : ℝ)*base72 + (6400509453493/13350000000000000000000000000 : ℝ)*base73 + (97852793188675483/55625000000000000000000000000000 : ℝ)*base76 + (27042576921175483/55625000000000000000000000000000 : ℝ)*base78 + (680158905055550483/55625000000000000000000000000000 : ℝ)*base80 + (44025184185107/13350000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7926317/625000000000000000000 : ℝ)*base90 + (7926317/625000000000000000000 : ℝ)*base92 + (7926317/625000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92623383464056633026863809/13906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1075514467/100000000000000 : ℝ)*(base19) + (616839989/50000000000000 : ℝ)*(base23) + (120795241/100000000000000 : ℝ)*(upper3) + (30707983/50000000000000 : ℝ)*(lower4) + (124481481/100000000000000 : ℝ)*(upper5) + (2996884807292537/50000000000000 : ℝ)*(major0) + (2996884807292537/50000000000000 : ℝ)*(major1) + (2996884807292537/50000000000000 : ℝ)*(major2) + (5934454843/20000000000000 : ℝ)*(sp1) + (4218165021/12500000000000 : ℝ)*(sp2) + (8004684615349487/100000000000000 : ℝ)*(sp4) + (1600930773512161/20000000000000 : ℝ)*(sp5) + (400232481817467/5000000000000 : ℝ)*(sp6) + (79657087836041/2000000000000 : ℝ)*(sp7) + (79657087836041/2000000000000 : ℝ)*(f.failure) + (8004684615349487/100000000000000 : ℝ)*(f.sum) + (8438302169123/3337500000000000000000000000 : ℝ)*base65 + (152285959392706799/27812500000000000000000000000000 : ℝ)*base67 + (456942215058956799/27812500000000000000000000000000 : ℝ)*base69 + (398545260691769299/27812500000000000000000000000000 : ℝ)*base71 + (53986751917979/6675000000000000000000000000 : ℝ)*base74 + (824622359094894299/27812500000000000000000000000000 : ℝ)*base75 + (301633140416456799/27812500000000000000000000000000 : ℝ)*base77 + (733901469529581799/27812500000000000000000000000000 : ℝ)*base79 + (64394134705229/6675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (594609/100000000000000000000 : ℝ)*base89 + (594609/100000000000000000000 : ℝ)*base91 + (594609/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1194_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1194_s8_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-214226721/1000000000 : ℝ)*x 0 + (539204573/1000000000 : ℝ)*x 1 + (2633289783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214226721/1000000000 : ℝ)^8387 ≤ (6511225486749/50000000000000 : ℝ)^6339 := by
    have hnat : (214226721 : ℕ)^8387*50000000000000^6339 ≤ 6511225486749^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214226721 1000000000 6511225486749 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539204573/1000000000 : ℝ)^8387 ≤ (11041515645703/25000000000000 : ℝ)^6339 := by
    have hnat : (539204573 : ℕ)^8387*25000000000000^6339 ≤ 11041515645703^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539204573 1000000000 11041515645703 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633289783/5000000000 : ℝ)^8387 ≤ (10702871606837/25000000000000 : ℝ)^6339 := by
    have hnat : (2633289783 : ℕ)^8387*25000000000000^6339 ≤ 10702871606837^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633289783 5000000000 10702871606837 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214226721/1000000000 : ℝ), (539204573/1000000000 : ℝ), (2633289783/5000000000 : ℝ)] ![(6511225486749/50000000000000 : ℝ), (11041515645703/25000000000000 : ℝ), (10702871606837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214226721/1000000000 : ℝ)|^8387 ≤ (6511225486749/50000000000000 : ℝ)^6339
        have hw : |(-214226721/1000000000 : ℝ)|=(214226721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539204573/1000000000 : ℝ)|^8387 ≤ (11041515645703/25000000000000 : ℝ)^6339
        have hw : |(539204573/1000000000 : ℝ)|=(539204573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633289783/5000000000 : ℝ)|^8387 ≤ (10702871606837/25000000000000 : ℝ)^6339
        have hw : |(2633289783/5000000000 : ℝ)|=(2633289783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s8_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068906851/2000000000 : ℝ)*x 0 + (-2205892569/10000000000 : ℝ)*x 1 + (2633289757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068906851/2000000000 : ℝ)^8387 ≤ (10912975234919/25000000000000 : ℝ)^6339 := by
    have hnat : (1068906851 : ℕ)^8387*25000000000000^6339 ≤ 10912975234919^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068906851 2000000000 10912975234919 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205892569/10000000000 : ℝ)^8387 ≤ (2707322634971/20000000000000 : ℝ)^6339 := by
    have hnat : (2205892569 : ℕ)^8387*20000000000000^6339 ≤ 2707322634971^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205892569 10000000000 2707322634971 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633289757/5000000000 : ℝ)^8387 ≤ (42811485868079/100000000000000 : ℝ)^6339 := by
    have hnat : (2633289757 : ℕ)^8387*100000000000000^6339 ≤ 42811485868079^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633289757 5000000000 42811485868079 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068906851/2000000000 : ℝ), (-2205892569/10000000000 : ℝ), (2633289757/5000000000 : ℝ)] ![(10912975234919/25000000000000 : ℝ), (2707322634971/20000000000000 : ℝ), (42811485868079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068906851/2000000000 : ℝ)|^8387 ≤ (10912975234919/25000000000000 : ℝ)^6339
        have hw : |(1068906851/2000000000 : ℝ)|=(1068906851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205892569/10000000000 : ℝ)|^8387 ≤ (2707322634971/20000000000000 : ℝ)^6339
        have hw : |(-2205892569/10000000000 : ℝ)|=(2205892569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633289757/5000000000 : ℝ)|^8387 ≤ (42811485868079/100000000000000 : ℝ)^6339
        have hw : |(2633289757/5000000000 : ℝ)|=(2633289757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s8_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336133553/2500000000 : ℝ)*x 0 + (2633289789/5000000000 : ℝ)*x 1 + (-1102946271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336133553/2500000000 : ℝ)^8387 ≤ (43651900475003/100000000000000 : ℝ)^6339 := by
    have hnat : (1336133553 : ℕ)^8387*100000000000000^6339 ≤ 43651900475003^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336133553 2500000000 43651900475003 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633289789/5000000000 : ℝ)^8387 ≤ (4281148655641/10000000000000 : ℝ)^6339 := by
    have hnat : (2633289789 : ℕ)^8387*10000000000000^6339 ≤ 4281148655641^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633289789 5000000000 4281148655641 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102946271/5000000000 : ℝ)^8387 ≤ (6768306477819/50000000000000 : ℝ)^6339 := by
    have hnat : (1102946271 : ℕ)^8387*50000000000000^6339 ≤ 6768306477819^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102946271 5000000000 6768306477819 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336133553/2500000000 : ℝ), (2633289789/5000000000 : ℝ), (-1102946271/5000000000 : ℝ)] ![(43651900475003/100000000000000 : ℝ), (4281148655641/10000000000000 : ℝ), (6768306477819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336133553/2500000000 : ℝ)|^8387 ≤ (43651900475003/100000000000000 : ℝ)^6339
        have hw : |(1336133553/2500000000 : ℝ)|=(1336133553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633289789/5000000000 : ℝ)|^8387 ≤ (4281148655641/10000000000000 : ℝ)^6339
        have hw : |(2633289789/5000000000 : ℝ)|=(2633289789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102946271/5000000000 : ℝ)|^8387 ≤ (6768306477819/50000000000000 : ℝ)^6339
        have hw : |(-1102946271/5000000000 : ℝ)|=(1102946271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s8_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544675073/1250000000 : ℝ)*x 0 + (4233113737/10000000000 : ℝ)*x 1 + (4485273929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544675073/1250000000 : ℝ)^8387 ≤ (8329316157901/25000000000000 : ℝ)^6339 := by
    have hnat : (544675073 : ℕ)^8387*25000000000000^6339 ≤ 8329316157901^6339*1250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544675073 1250000000 8329316157901 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233113737/10000000000 : ℝ)^8387 ≤ (32065755196947/100000000000000 : ℝ)^6339 := by
    have hnat : (4233113737 : ℕ)^8387*100000000000000^6339 ≤ 32065755196947^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233113737 10000000000 32065755196947 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485273929/10000000000 : ℝ)^8387 ≤ (8654245040409/25000000000000 : ℝ)^6339 := by
    have hnat : (4485273929 : ℕ)^8387*25000000000000^6339 ≤ 8654245040409^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485273929 10000000000 8654245040409 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544675073/1250000000 : ℝ), (4233113737/10000000000 : ℝ), (4485273929/10000000000 : ℝ)] ![(8329316157901/25000000000000 : ℝ), (32065755196947/100000000000000 : ℝ), (8654245040409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544675073/1250000000 : ℝ)|^8387 ≤ (8329316157901/25000000000000 : ℝ)^6339
        have hw : |(544675073/1250000000 : ℝ)|=(544675073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233113737/10000000000 : ℝ)|^8387 ≤ (32065755196947/100000000000000 : ℝ)^6339
        have hw : |(4233113737/10000000000 : ℝ)|=(4233113737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485273929/10000000000 : ℝ)|^8387 ≤ (8654245040409/25000000000000 : ℝ)^6339
        have hw : |(4485273929/10000000000 : ℝ)|=(4485273929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s8_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142271971/10000000000 : ℝ)*x 0 + (5266895191/10000000000 : ℝ)*x 1 + (5391728957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142271971/10000000000 : ℝ)^8387 ≤ (13022489265081/100000000000000 : ℝ)^6339 := by
    have hnat : (2142271971 : ℕ)^8387*100000000000000^6339 ≤ 13022489265081^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142271971 10000000000 13022489265081 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266895191/10000000000 : ℝ)^8387 ≤ (8562976212569/20000000000000 : ℝ)^6339 := by
    have hnat : (5266895191 : ℕ)^8387*20000000000000^6339 ≤ 8562976212569^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266895191 10000000000 8562976212569 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391728957/10000000000 : ℝ)^8387 ≤ (44162629652053/100000000000000 : ℝ)^6339 := by
    have hnat : (5391728957 : ℕ)^8387*100000000000000^6339 ≤ 44162629652053^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391728957 10000000000 44162629652053 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142271971/10000000000 : ℝ), (5266895191/10000000000 : ℝ), (5391728957/10000000000 : ℝ)] ![(13022489265081/100000000000000 : ℝ), (8562976212569/20000000000000 : ℝ), (44162629652053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142271971/10000000000 : ℝ)|^8387 ≤ (13022489265081/100000000000000 : ℝ)^6339
        have hw : |(-2142271971/10000000000 : ℝ)|=(2142271971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266895191/10000000000 : ℝ)|^8387 ≤ (8562976212569/20000000000000 : ℝ)^6339
        have hw : |(5266895191/10000000000 : ℝ)|=(5266895191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391728957/10000000000 : ℝ)|^8387 ≤ (44162629652053/100000000000000 : ℝ)^6339
        have hw : |(5391728957/10000000000 : ℝ)|=(5391728957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s8_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656313449/5000000000 : ℝ)*x 0 + (-2080743157/10000000000 : ℝ)*x 1 + (5391728957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656313449/5000000000 : ℝ)^8387 ≤ (43307431725703/100000000000000 : ℝ)^6339 := by
    have hnat : (2656313449 : ℕ)^8387*100000000000000^6339 ≤ 43307431725703^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656313449 5000000000 43307431725703 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080743157/10000000000 : ℝ)^8387 ≤ (12529938606399/100000000000000 : ℝ)^6339 := by
    have hnat : (2080743157 : ℕ)^8387*100000000000000^6339 ≤ 12529938606399^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080743157 10000000000 12529938606399 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391728957/10000000000 : ℝ)^8387 ≤ (44162629652053/100000000000000 : ℝ)^6339 := by
    have hnat : (5391728957 : ℕ)^8387*100000000000000^6339 ≤ 44162629652053^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391728957 10000000000 44162629652053 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656313449/5000000000 : ℝ), (-2080743157/10000000000 : ℝ), (5391728957/10000000000 : ℝ)] ![(43307431725703/100000000000000 : ℝ), (12529938606399/100000000000000 : ℝ), (44162629652053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656313449/5000000000 : ℝ)|^8387 ≤ (43307431725703/100000000000000 : ℝ)^6339
        have hw : |(2656313449/5000000000 : ℝ)|=(2656313449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080743157/10000000000 : ℝ)|^8387 ≤ (12529938606399/100000000000000 : ℝ)^6339
        have hw : |(-2080743157/10000000000 : ℝ)|=(2080743157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391728957/10000000000 : ℝ)|^8387 ≤ (44162629652053/100000000000000 : ℝ)^6339
        have hw : |(5391728957/10000000000 : ℝ)|=(5391728957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s8_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656313449/5000000000 : ℝ)*x 0 + (5391728957/10000000000 : ℝ)*x 1 + (-2080743157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656313449/5000000000 : ℝ)^8387 ≤ (43307431725703/100000000000000 : ℝ)^6339 := by
    have hnat : (2656313449 : ℕ)^8387*100000000000000^6339 ≤ 43307431725703^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656313449 5000000000 43307431725703 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391728957/10000000000 : ℝ)^8387 ≤ (44162629652053/100000000000000 : ℝ)^6339 := by
    have hnat : (5391728957 : ℕ)^8387*100000000000000^6339 ≤ 44162629652053^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391728957 10000000000 44162629652053 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080743157/10000000000 : ℝ)^8387 ≤ (12529938606399/100000000000000 : ℝ)^6339 := by
    have hnat : (2080743157 : ℕ)^8387*100000000000000^6339 ≤ 12529938606399^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080743157 10000000000 12529938606399 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656313449/5000000000 : ℝ), (5391728957/10000000000 : ℝ), (-2080743157/10000000000 : ℝ)] ![(43307431725703/100000000000000 : ℝ), (44162629652053/100000000000000 : ℝ), (12529938606399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656313449/5000000000 : ℝ)|^8387 ≤ (43307431725703/100000000000000 : ℝ)^6339
        have hw : |(2656313449/5000000000 : ℝ)|=(2656313449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391728957/10000000000 : ℝ)|^8387 ≤ (44162629652053/100000000000000 : ℝ)^6339
        have hw : |(5391728957/10000000000 : ℝ)|=(5391728957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080743157/10000000000 : ℝ)|^8387 ≤ (12529938606399/100000000000000 : ℝ)^6339
        have hw : |(-2080743157/10000000000 : ℝ)|=(2080743157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s8_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089352537/2500000000 : ℝ)*x 0 + (4484639551/10000000000 : ℝ)*x 1 + (1323047/3125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089352537/2500000000 : ℝ)^8387 ≤ (33317361385277/100000000000000 : ℝ)^6339 := by
    have hnat : (1089352537 : ℕ)^8387*100000000000000^6339 ≤ 33317361385277^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089352537 2500000000 33317361385277 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484639551/10000000000 : ℝ)^8387 ≤ (6922100482011/20000000000000 : ℝ)^6339 := by
    have hnat : (4484639551 : ℕ)^8387*20000000000000^6339 ≤ 6922100482011^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484639551 10000000000 6922100482011 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1323047/3125000 : ℝ)^8387 ≤ (6414427235993/20000000000000 : ℝ)^6339 := by
    have hnat : (1323047 : ℕ)^8387*20000000000000^6339 ≤ 6414427235993^6339*3125000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323047 3125000 6414427235993 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089352537/2500000000 : ℝ), (4484639551/10000000000 : ℝ), (1323047/3125000 : ℝ)] ![(33317361385277/100000000000000 : ℝ), (6922100482011/20000000000000 : ℝ), (6414427235993/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089352537/2500000000 : ℝ)|^8387 ≤ (33317361385277/100000000000000 : ℝ)^6339
        have hw : |(1089352537/2500000000 : ℝ)|=(1089352537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484639551/10000000000 : ℝ)|^8387 ≤ (6922100482011/20000000000000 : ℝ)^6339
        have hw : |(4484639551/10000000000 : ℝ)|=(4484639551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1323047/3125000 : ℝ)|^8387 ≤ (6414427235993/20000000000000 : ℝ)^6339
        have hw : |(1323047/3125000 : ℝ)|=(1323047/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (571/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7039/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11419/100000 : ℝ) ^ (4193/1024 : ℝ) ≤ (3460864907600827/25000000000000000000 : ℝ) := by
    have hpowers : (11419/100000 : ℝ)^4193 ≤ (3460864907600827/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11419 : ℕ)^4193*25000000000000000000^1024 ≤ 3460864907600827^1024*100000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11419 100000 3460864907600827 25000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11419/100000 : ℝ)) (X := (3460864907600827/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14079/100000 : ℝ) ^ (4193/1024 : ℝ) ≤ (32631299546249141/100000000000000000000 : ℝ) := by
    have hpowers : (14079/100000 : ℝ)^4193 ≤ (32631299546249141/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14079 : ℕ)^4193*100000000000000000000^1024 ≤ 32631299546249141^1024*100000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14079 100000 32631299546249141 100000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14079/100000 : ℝ)) (X := (32631299546249141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503460864907600827/12500000000000000000 : ℝ) ≤ (5000338044830589/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (12503460864907600827/12500000000000000000 : ℝ)^1024 ≤ (5000338044830589/5000000000000000 : ℝ)^4193 := by
      have hnat : (12503460864907600827 : ℕ)^1024*5000000000000000^4193 ≤ 5000338044830589^4193*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503460864907600827 12500000000000000000 5000338044830589 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000338044830589/5000000000000000 : ℝ)) (X := (12503460864907600827/12500000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046474759176652449/100000000000000000000 : ℝ) ≤ (5000567395631811/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (100046474759176652449/100000000000000000000 : ℝ)^1024 ≤ (5000567395631811/5000000000000000 : ℝ)^4193 := by
      have hnat : (100046474759176652449 : ℕ)^1024*5000000000000000^4193 ≤ 5000567395631811^4193*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046474759176652449 100000000000000000000 5000567395631811 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000567395631811/5000000000000000 : ℝ)) (X := (100046474759176652449/100000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032631299546249141/50000000000000000000 : ℝ) ≤ (5000796746433033/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (50032631299546249141/50000000000000000000 : ℝ)^1024 ≤ (5000796746433033/5000000000000000 : ℝ)^4193 := by
      have hnat : (50032631299546249141 : ℕ)^1024*5000000000000000^4193 ≤ 5000796746433033^4193*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032631299546249141 50000000000000000000 5000796746433033 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000796746433033/5000000000000000 : ℝ)) (X := (50032631299546249141/50000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3460864907600827/25000000000000000000 : ℝ) ≤ ((43735727913325851/43750000000000000 : ℝ)+2*(114675400611/66500000000000 : ℝ)*(11419/100000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (43735727913325851/43750000000000000 : ℝ)+2*(114675400611/66500000000000 : ℝ)*(11419/100000 : ℝ)=(5000338044830589/5000000000000000 : ℝ) by norm_num, show 1+2*(3460864907600827/25000000000000000000 : ℝ)=(12503460864907600827/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32631299546249141/100000000000000000000 : ℝ)+(3460864907600827/25000000000000000000 : ℝ) ≤ ((43735727913325851/43750000000000000 : ℝ)+(114675400611/66500000000000 : ℝ)*((14079/100000 : ℝ)+(11419/100000 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (43735727913325851/43750000000000000 : ℝ)+(114675400611/66500000000000 : ℝ)*((14079/100000 : ℝ)+(11419/100000 : ℝ))=(5000567395631811/5000000000000000 : ℝ) by norm_num, show 1+(32631299546249141/100000000000000000000 : ℝ)+(3460864907600827/25000000000000000000 : ℝ)=(100046474759176652449/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32631299546249141/100000000000000000000 : ℝ) ≤ ((43735727913325851/43750000000000000 : ℝ)+2*(114675400611/66500000000000 : ℝ)*(14079/100000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (43735727913325851/43750000000000000 : ℝ)+2*(114675400611/66500000000000 : ℝ)*(14079/100000 : ℝ)=(5000796746433033/5000000000000000 : ℝ) by norm_num, show 1+2*(32631299546249141/100000000000000000000 : ℝ)=(50032631299546249141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43735727913325851/43750000000000000 : ℝ)*(X 1 0+X 2 0)+(114675400611/66500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (43735727913325851/43750000000000000 : ℝ)) (alpha := (114675400611/66500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43735727913325851/43750000000000000 : ℝ)*(X 0 1+X 2 1)+(114675400611/66500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (43735727913325851/43750000000000000 : ℝ)) (alpha := (114675400611/66500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43735727913325851/43750000000000000 : ℝ)*(X 0 2+X 1 2)+(114675400611/66500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (43735727913325851/43750000000000000 : ℝ)) (alpha := (114675400611/66500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-214226721/1000000000 : ℝ)*X 0 0+(539204573/1000000000 : ℝ)*X 0 1+(2633289783/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068906851/2000000000 : ℝ)*X 1 0+(-2205892569/10000000000 : ℝ)*X 1 1+(2633289757/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336133553/2500000000 : ℝ)*X 2 0+(2633289789/5000000000 : ℝ)*X 2 1+(-1102946271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544675073/1250000000 : ℝ)*X 0 0+(4233113737/10000000000 : ℝ)*X 0 1+(4485273929/10000000000 : ℝ)*X 0 2+(544675073/1250000000 : ℝ)*X 1 0+(4233113737/10000000000 : ℝ)*X 1 1+(4485273929/10000000000 : ℝ)*X 1 2+(544675073/1250000000 : ℝ)*X 2 0+(4233113737/10000000000 : ℝ)*X 2 1+(4485273929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2142271971/10000000000 : ℝ)*X 0 0+(5266895191/10000000000 : ℝ)*X 0 1+(5391728957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656313449/5000000000 : ℝ)*X 1 0+(-2080743157/10000000000 : ℝ)*X 1 1+(5391728957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656313449/5000000000 : ℝ)*X 2 0+(5391728957/10000000000 : ℝ)*X 2 1+(-2080743157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089352537/2500000000 : ℝ)*X 0 0+(4484639551/10000000000 : ℝ)*X 0 1+(1323047/3125000 : ℝ)*X 0 2+(1089352537/2500000000 : ℝ)*X 1 0+(4484639551/10000000000 : ℝ)*X 1 1+(1323047/3125000 : ℝ)*X 1 2+(1089352537/2500000000 : ℝ)*X 2 0+(4484639551/10000000000 : ℝ)*X 2 1+(1323047/3125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67408775512752355876132551/8312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (817257751/50000000000000 : ℝ)*(base19) + (364373059/25000000000000 : ℝ)*(base23) + (30169063/50000000000000 : ℝ)*(lower2) + (46102597/25000000000000 : ℝ)*(upper3) + (66936827/50000000000000 : ℝ)*(upper5) + (1193614357472793/20000000000000 : ℝ)*(major0) + (1193614357472793/20000000000000 : ℝ)*(major1) + (1193614357472793/20000000000000 : ℝ)*(major2) + (3985160660587259/50000000000000 : ℝ)*(sp0) + (7970363460633821/100000000000000 : ℝ)*(sp1) + (7970363637657087/100000000000000 : ℝ)*(sp2) + (1982877450954771/50000000000000 : ℝ)*(sp3) + (8754794961/20000000000000 : ℝ)*(sp4) + (1165367909/5000000000000 : ℝ)*(sp7) + (1982889104633861/50000000000000 : ℝ)*(f.failure) + (7970365095149323/100000000000000 : ℝ)*(f.sum) + (1419126757961/332500000000000000000000000 : ℝ)*base66 + (38779087942722483/16625000000000000000000000000000 : ℝ)*base68 + (25847215339027517/16625000000000000000000000000000 : ℝ)*base69 + (56626882782027517/16625000000000000000000000000000 : ℝ)*base71 + (864131640501/332500000000000000000000000 : ℝ)*base74 + (113944353535097483/16625000000000000000000000000000 : ℝ)*base76 + (153674746947597483/16625000000000000000000000000000 : ℝ)*base78 + (311176361193097483/16625000000000000000000000000000 : ℝ)*base80 + (498503929463/665000000000000000000000000 : ℝ)*base81 + (19459789/2500000000000000000000 : ℝ)*base89 + (19459789/2500000000000000000000 : ℝ)*base91 + (19459789/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2420411273189776116700869/371093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1180333473/100000000000000 : ℝ)*(base19) + (160510581/12500000000000 : ℝ)*(base23) + (412629327/100000000000000 : ℝ)*(lower1) + (32825083/25000000000000 : ℝ)*(upper3) + (4718691/10000000000000 : ℝ)*(lower4) + (66689621/50000000000000 : ℝ)*(upper5) + (749776639281637/12500000000000 : ℝ)*(major0) + (749776639281637/12500000000000 : ℝ)*(major1) + (749776639281637/12500000000000 : ℝ)*(major2) + (1243010803/50000000000000 : ℝ)*(sp2) + (8010618917852457/100000000000000 : ℝ)*(sp4) + (1001327217189873/12500000000000 : ℝ)*(sp5) + (8010615147746203/100000000000000 : ℝ)*(sp6) + (3985807093241339/100000000000000 : ℝ)*(sp7) + (3985807093241339/100000000000000 : ℝ)*(f.failure) + (8010618917852457/100000000000000 : ℝ)*(f.sum) + (2537344996469/3325000000000000000000000000 : ℝ)*base66 + (21151150014538653/10390625000000000000000000000000 : ℝ)*base67 + (6661041268025493/2597656250000000000000000000000 : ℝ)*base70 + (921068564481413653/10390625000000000000000000000000 : ℝ)*base71 + (12262573909169/3325000000000000000000000000 : ℝ)*base74 + (236139704374226153/10390625000000000000000000000000 : ℝ)*base75 + (3586100426555097/10390625000000000000000000000000 : ℝ)*base78 + (158230215833601153/10390625000000000000000000000000 : ℝ)*base79 + (28703149379369/3325000000000000000000000000 : ℝ)*base82 + (25345011/5000000000000000000000 : ℝ)*base89 + (25345011/5000000000000000000000 : ℝ)*base91 + (25345011/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1194_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (571/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1194_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (571/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1194_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1194_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1194_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (571/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1194_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

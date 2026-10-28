-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1098_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:59:35.435797+00:00
-- url     : https://prove2.me/submissions/f357f42a-5f95-45f3-93b1-b86e1561c92a

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
theorem support_rectangle_w1098_s3_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091893001/5000000000 : ℝ)*x 0 + (2716947979/5000000000 : ℝ)*x 1 + (1306937993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091893001/5000000000 : ℝ)^8291 ≤ (6628414483753/50000000000000 : ℝ)^6243 := by
    have hnat : (1091893001 : ℕ)^8291*50000000000000^6243 ≤ 6628414483753^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091893001 5000000000 6628414483753 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716947979/5000000000 : ℝ)^8291 ≤ (1112129295057/2500000000000 : ℝ)^6243 := by
    have hnat : (2716947979 : ℕ)^8291*2500000000000^6243 ≤ 1112129295057^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716947979 5000000000 1112129295057 2500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306937993/2500000000 : ℝ)^8291 ≤ (42257999204509/100000000000000 : ℝ)^6243 := by
    have hnat : (1306937993 : ℕ)^8291*100000000000000^6243 ≤ 42257999204509^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306937993 2500000000 42257999204509 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091893001/5000000000 : ℝ), (2716947979/5000000000 : ℝ), (1306937993/2500000000 : ℝ)] ![(6628414483753/50000000000000 : ℝ), (1112129295057/2500000000000 : ℝ), (42257999204509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091893001/5000000000 : ℝ)|^8291 ≤ (6628414483753/50000000000000 : ℝ)^6243
        have hw : |(-1091893001/5000000000 : ℝ)|=(1091893001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716947979/5000000000 : ℝ)|^8291 ≤ (1112129295057/2500000000000 : ℝ)^6243
        have hw : |(2716947979/5000000000 : ℝ)|=(2716947979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306937993/2500000000 : ℝ)|^8291 ≤ (42257999204509/100000000000000 : ℝ)^6243
        have hw : |(1306937993/2500000000 : ℝ)|=(1306937993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s3_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267743891/500000000 : ℝ)*x 0 + (-2289265641/10000000000 : ℝ)*x 1 + (5227752169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267743891/500000000 : ℝ)^8291 ≤ (4362812643361/10000000000000 : ℝ)^6243 := by
    have hnat : (267743891 : ℕ)^8291*10000000000000^6243 ≤ 4362812643361^6243*500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267743891 500000000 4362812643361 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2289265641/10000000000 : ℝ)^8291 ≤ (14113872234463/100000000000000 : ℝ)^6243 := by
    have hnat : (2289265641 : ℕ)^8291*100000000000000^6243 ≤ 14113872234463^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289265641 10000000000 14113872234463 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227752169/10000000000 : ℝ)^8291 ≤ (4225800131933/10000000000000 : ℝ)^6243 := by
    have hnat : (5227752169 : ℕ)^8291*10000000000000^6243 ≤ 4225800131933^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227752169 10000000000 4225800131933 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267743891/500000000 : ℝ), (-2289265641/10000000000 : ℝ), (5227752169/10000000000 : ℝ)] ![(4362812643361/10000000000000 : ℝ), (14113872234463/100000000000000 : ℝ), (4225800131933/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267743891/500000000 : ℝ)|^8291 ≤ (4362812643361/10000000000000 : ℝ)^6243
        have hw : |(267743891/500000000 : ℝ)|=(267743891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2289265641/10000000000 : ℝ)|^8291 ≤ (14113872234463/100000000000000 : ℝ)^6243
        have hw : |(-2289265641/10000000000 : ℝ)|=(2289265641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227752169/10000000000 : ℝ)|^8291 ≤ (4225800131933/10000000000000 : ℝ)^6243
        have hw : |(5227752169/10000000000 : ℝ)|=(5227752169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s3_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338719493/2500000000 : ℝ)*x 0 + (1045550453/2000000000 : ℝ)*x 1 + (-1144632657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338719493/2500000000 : ℝ)^8291 ≤ (21814064039131/50000000000000 : ℝ)^6243 := by
    have hnat : (1338719493 : ℕ)^8291*50000000000000^6243 ≤ 21814064039131^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338719493 2500000000 21814064039131 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045550453/2000000000 : ℝ)^8291 ≤ (42258002349903/100000000000000 : ℝ)^6243 := by
    have hnat : (1045550453 : ℕ)^8291*100000000000000^6243 ≤ 42258002349903^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045550453 2000000000 42258002349903 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144632657/5000000000 : ℝ)^8291 ≤ (564554782283/4000000000000 : ℝ)^6243 := by
    have hnat : (1144632657 : ℕ)^8291*4000000000000^6243 ≤ 564554782283^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144632657 5000000000 564554782283 4000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338719493/2500000000 : ℝ), (1045550453/2000000000 : ℝ), (-1144632657/5000000000 : ℝ)] ![(21814064039131/50000000000000 : ℝ), (42258002349903/100000000000000 : ℝ), (564554782283/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338719493/2500000000 : ℝ)|^8291 ≤ (21814064039131/50000000000000 : ℝ)^6243
        have hw : |(1338719493/2500000000 : ℝ)|=(1338719493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045550453/2000000000 : ℝ)|^8291 ≤ (42258002349903/100000000000000 : ℝ)^6243
        have hw : |(1045550453/2000000000 : ℝ)|=(1045550453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144632657/5000000000 : ℝ)|^8291 ≤ (564554782283/4000000000000 : ℝ)^6243
        have hw : |(-1144632657/5000000000 : ℝ)|=(1144632657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s3_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368350291/10000000000 : ℝ)*x 0 + (4169808651/10000000000 : ℝ)*x 1 + (1144097289/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368350291/10000000000 : ℝ)^8291 ≤ (33290822755873/100000000000000 : ℝ)^6243 := by
    have hnat : (4368350291 : ℕ)^8291*100000000000000^6243 ≤ 33290822755873^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368350291 10000000000 33290822755873 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169808651/10000000000 : ℝ)^8291 ≤ (31296531155389/100000000000000 : ℝ)^6243 := by
    have hnat : (4169808651 : ℕ)^8291*100000000000000^6243 ≤ 31296531155389^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169808651 10000000000 31296531155389 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144097289/2500000000 : ℝ)^8291 ≤ (17706323042007/50000000000000 : ℝ)^6243 := by
    have hnat : (1144097289 : ℕ)^8291*50000000000000^6243 ≤ 17706323042007^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144097289 2500000000 17706323042007 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368350291/10000000000 : ℝ), (4169808651/10000000000 : ℝ), (1144097289/2500000000 : ℝ)] ![(33290822755873/100000000000000 : ℝ), (31296531155389/100000000000000 : ℝ), (17706323042007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368350291/10000000000 : ℝ)|^8291 ≤ (33290822755873/100000000000000 : ℝ)^6243
        have hw : |(4368350291/10000000000 : ℝ)|=(4368350291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169808651/10000000000 : ℝ)|^8291 ≤ (31296531155389/100000000000000 : ℝ)^6243
        have hw : |(4169808651/10000000000 : ℝ)|=(4169808651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1144097289/2500000000 : ℝ)|^8291 ≤ (17706323042007/50000000000000 : ℝ)^6243
        have hw : |(1144097289/2500000000 : ℝ)|=(1144097289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s3_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091903401/5000000000 : ℝ)*x 0 + (1045715491/2000000000 : ℝ)*x 1 + (5433065417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091903401/5000000000 : ℝ)^8291 ≤ (3314249164377/25000000000000 : ℝ)^6243 := by
    have hnat : (1091903401 : ℕ)^8291*25000000000000^6243 ≤ 3314249164377^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091903401 5000000000 3314249164377 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045715491/2000000000 : ℝ)^8291 ≤ (21133430552997/50000000000000 : ℝ)^6243 := by
    have hnat : (1045715491 : ℕ)^8291*50000000000000^6243 ≤ 21133430552997^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045715491 2000000000 21133430552997 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433065417/10000000000 : ℝ)^8291 ≤ (5559517777339/12500000000000 : ℝ)^6243 := by
    have hnat : (5433065417 : ℕ)^8291*12500000000000^6243 ≤ 5559517777339^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433065417 10000000000 5559517777339 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091903401/5000000000 : ℝ), (1045715491/2000000000 : ℝ), (5433065417/10000000000 : ℝ)] ![(3314249164377/25000000000000 : ℝ), (21133430552997/50000000000000 : ℝ), (5559517777339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091903401/5000000000 : ℝ)|^8291 ≤ (3314249164377/25000000000000 : ℝ)^6243
        have hw : |(-1091903401/5000000000 : ℝ)|=(1091903401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045715491/2000000000 : ℝ)|^8291 ≤ (21133430552997/50000000000000 : ℝ)^6243
        have hw : |(1045715491/2000000000 : ℝ)|=(1045715491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433065417/10000000000 : ℝ)|^8291 ≤ (5559517777339/12500000000000 : ℝ)^6243
        have hw : |(5433065417/10000000000 : ℝ)|=(5433065417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s3_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302822869/10000000000 : ℝ)*x 0 + (-32561759/156250000 : ℝ)*x 1 + (1086613097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302822869/10000000000 : ℝ)^8291 ≤ (672902931241/1562500000000 : ℝ)^6243 := by
    have hnat : (5302822869 : ℕ)^8291*1562500000000^6243 ≤ 672902931241^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302822869 10000000000 672902931241 1562500000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32561759/156250000 : ℝ)^8291 ≤ (498322776997/4000000000000 : ℝ)^6243 := by
    have hnat : (32561759 : ℕ)^8291*4000000000000^6243 ≤ 498322776997^6243*156250000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32561759 156250000 498322776997 4000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086613097/2000000000 : ℝ)^8291 ≤ (8895228591597/20000000000000 : ℝ)^6243 := by
    have hnat : (1086613097 : ℕ)^8291*20000000000000^6243 ≤ 8895228591597^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086613097 2000000000 8895228591597 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302822869/10000000000 : ℝ), (-32561759/156250000 : ℝ), (1086613097/2000000000 : ℝ)] ![(672902931241/1562500000000 : ℝ), (498322776997/4000000000000 : ℝ), (8895228591597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302822869/10000000000 : ℝ)|^8291 ≤ (672902931241/1562500000000 : ℝ)^6243
        have hw : |(5302822869/10000000000 : ℝ)|=(5302822869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32561759/156250000 : ℝ)|^8291 ≤ (498322776997/4000000000000 : ℝ)^6243
        have hw : |(-32561759/156250000 : ℝ)|=(32561759/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086613097/2000000000 : ℝ)|^8291 ≤ (8895228591597/20000000000000 : ℝ)^6243
        have hw : |(1086613097/2000000000 : ℝ)|=(1086613097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s3_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302823373/10000000000 : ℝ)*x 0 + (5433065761/10000000000 : ℝ)*x 1 + (-1041975757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302823373/10000000000 : ℝ)^8291 ≤ (21532896517649/50000000000000 : ℝ)^6243 := by
    have hnat : (5302823373 : ℕ)^8291*50000000000000^6243 ≤ 21532896517649^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302823373 10000000000 21532896517649 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433065761/10000000000 : ℝ)^8291 ≤ (22238072979281/50000000000000 : ℝ)^6243 := by
    have hnat : (5433065761 : ℕ)^8291*50000000000000^6243 ≤ 22238072979281^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433065761 10000000000 22238072979281 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041975757/5000000000 : ℝ)^8291 ≤ (24916121987/200000000000 : ℝ)^6243 := by
    have hnat : (1041975757 : ℕ)^8291*200000000000^6243 ≤ 24916121987^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041975757 5000000000 24916121987 200000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302823373/10000000000 : ℝ), (5433065761/10000000000 : ℝ), (-1041975757/5000000000 : ℝ)] ![(21532896517649/50000000000000 : ℝ), (22238072979281/50000000000000 : ℝ), (24916121987/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302823373/10000000000 : ℝ)|^8291 ≤ (21532896517649/50000000000000 : ℝ)^6243
        have hw : |(5302823373/10000000000 : ℝ)|=(5302823373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433065761/10000000000 : ℝ)|^8291 ≤ (22238072979281/50000000000000 : ℝ)^6243
        have hw : |(5433065761/10000000000 : ℝ)|=(5433065761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1041975757/5000000000 : ℝ)|^8291 ≤ (24916121987/200000000000 : ℝ)^6243
        have hw : |(-1041975757/5000000000 : ℝ)|=(1041975757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s3_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184194997/5000000000 : ℝ)*x 0 + (1143690473/2500000000 : ℝ)*x 1 + (4171445829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184194997/5000000000 : ℝ)^8291 ≤ (3329122458797/10000000000000 : ℝ)^6243 := by
    have hnat : (2184194997 : ℕ)^8291*10000000000000^6243 ≤ 3329122458797^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184194997 5000000000 3329122458797 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143690473/2500000000 : ℝ)^8291 ≤ (17697962167591/50000000000000 : ℝ)^6243 := by
    have hnat : (1143690473 : ℕ)^8291*50000000000000^6243 ≤ 17697962167591^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143690473 2500000000 17697962167591 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171445829/10000000000 : ℝ)^8291 ≤ (782821276413/2500000000000 : ℝ)^6243 := by
    have hnat : (4171445829 : ℕ)^8291*2500000000000^6243 ≤ 782821276413^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171445829 10000000000 782821276413 2500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184194997/5000000000 : ℝ), (1143690473/2500000000 : ℝ), (4171445829/10000000000 : ℝ)] ![(3329122458797/10000000000000 : ℝ), (17697962167591/50000000000000 : ℝ), (782821276413/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184194997/5000000000 : ℝ)|^8291 ≤ (3329122458797/10000000000000 : ℝ)^6243
        have hw : |(2184194997/5000000000 : ℝ)|=(2184194997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1143690473/2500000000 : ℝ)|^8291 ≤ (17697962167591/50000000000000 : ℝ)^6243
        have hw : |(1143690473/2500000000 : ℝ)|=(1143690473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171445829/10000000000 : ℝ)|^8291 ≤ (782821276413/2500000000000 : ℝ)^6243
        have hw : |(4171445829/10000000000 : ℝ)|=(4171445829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8319/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4433/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (21/200 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14861/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8319/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4433/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8319/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4433/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8319/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4433/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8319/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4433/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8319/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4433/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8319/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4433/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4433/50000 : ℝ) ^ (4145/1024 : ℝ) ≤ (2751237229884097/50000000000000000000 : ℝ) := by
    have hpowers : (4433/50000 : ℝ)^4145 ≤ (2751237229884097/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4433 : ℕ)^4145*50000000000000000000^1024 ≤ 2751237229884097^1024*50000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4433 50000 2751237229884097 50000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4433/50000 : ℝ)) (X := (2751237229884097/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8319/50000 : ℝ) ^ (4145/1024 : ℝ) ≤ (35164379285810471/50000000000000000000 : ℝ) := by
    have hpowers : (8319/50000 : ℝ)^4145 ≤ (35164379285810471/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8319 : ℕ)^4145*50000000000000000000^1024 ≤ 35164379285810471^1024*50000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8319 50000 35164379285810471 50000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8319/50000 : ℝ)) (X := (35164379285810471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002751237229884097/25000000000000000000 : ℝ) ≤ (10000271860092471/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25002751237229884097/25000000000000000000 : ℝ)^1024 ≤ (10000271860092471/10000000000000000 : ℝ)^4145 := by
      have hnat : (25002751237229884097 : ℕ)^1024*10000000000000000^4145 ≤ 10000271860092471^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002751237229884097 25000000000000000000 10000271860092471 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000271860092471/10000000000000000 : ℝ)) (X := (25002751237229884097/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6254739452064461821/6250000000000000000 : ℝ) ≤ (10001872835319339/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (6254739452064461821/6250000000000000000 : ℝ)^1024 ≤ (10001872835319339/10000000000000000 : ℝ)^4145 := by
      have hnat : (6254739452064461821 : ℕ)^1024*10000000000000000^4145 ≤ 10001872835319339^4145*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254739452064461821 6250000000000000000 10001872835319339 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001872835319339/10000000000000000 : ℝ)) (X := (6254739452064461821/6250000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25035164379285810471/25000000000000000000 : ℝ) ≤ (10003473810546207/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25035164379285810471/25000000000000000000 : ℝ)^1024 ≤ (10003473810546207/10000000000000000 : ℝ)^4145 := by
      have hnat : (25035164379285810471 : ℕ)^1024*10000000000000000^4145 ≤ 10003473810546207^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25035164379285810471 25000000000000000000 10003473810546207 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003473810546207/10000000000000000 : ℝ)) (X := (25035164379285810471/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2751237229884097/50000000000000000000 : ℝ) ≤ ((19423431100978965309/19430000000000000000 : ℝ)+2*(400243806717/194300000000000 : ℝ)*(4433/50000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (19423431100978965309/19430000000000000000 : ℝ)+2*(400243806717/194300000000000 : ℝ)*(4433/50000 : ℝ)=(10000271860092471/10000000000000000 : ℝ) by norm_num, show 1+2*(2751237229884097/50000000000000000000 : ℝ)=(25002751237229884097/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35164379285810471/50000000000000000000 : ℝ)+(2751237229884097/50000000000000000000 : ℝ) ≤ ((19423431100978965309/19430000000000000000 : ℝ)+(400243806717/194300000000000 : ℝ)*((8319/50000 : ℝ)+(4433/50000 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (19423431100978965309/19430000000000000000 : ℝ)+(400243806717/194300000000000 : ℝ)*((8319/50000 : ℝ)+(4433/50000 : ℝ))=(10001872835319339/10000000000000000 : ℝ) by norm_num, show 1+(35164379285810471/50000000000000000000 : ℝ)+(2751237229884097/50000000000000000000 : ℝ)=(6254739452064461821/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35164379285810471/50000000000000000000 : ℝ) ≤ ((19423431100978965309/19430000000000000000 : ℝ)+2*(400243806717/194300000000000 : ℝ)*(8319/50000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (19423431100978965309/19430000000000000000 : ℝ)+2*(400243806717/194300000000000 : ℝ)*(8319/50000 : ℝ)=(10003473810546207/10000000000000000 : ℝ) by norm_num, show 1+2*(35164379285810471/50000000000000000000 : ℝ)=(25035164379285810471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19423431100978965309/19430000000000000000 : ℝ)*(X 1 0+X 2 0)+(400243806717/194300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (4433/50000 : ℝ)) (hi := (8319/50000 : ℝ)) (c := (19423431100978965309/19430000000000000000 : ℝ)) (alpha := (400243806717/194300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19423431100978965309/19430000000000000000 : ℝ)*(X 0 1+X 2 1)+(400243806717/194300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (4433/50000 : ℝ)) (hi := (8319/50000 : ℝ)) (c := (19423431100978965309/19430000000000000000 : ℝ)) (alpha := (400243806717/194300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19423431100978965309/19430000000000000000 : ℝ)*(X 0 2+X 1 2)+(400243806717/194300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (4433/50000 : ℝ)) (hi := (8319/50000 : ℝ)) (c := (19423431100978965309/19430000000000000000 : ℝ)) (alpha := (400243806717/194300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1091893001/5000000000 : ℝ)*X 0 0+(2716947979/5000000000 : ℝ)*X 0 1+(1306937993/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267743891/500000000 : ℝ)*X 1 0+(-2289265641/10000000000 : ℝ)*X 1 1+(5227752169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338719493/2500000000 : ℝ)*X 2 0+(1045550453/2000000000 : ℝ)*X 2 1+(-1144632657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368350291/10000000000 : ℝ)*X 0 0+(4169808651/10000000000 : ℝ)*X 0 1+(1144097289/2500000000 : ℝ)*X 0 2+(4368350291/10000000000 : ℝ)*X 1 0+(4169808651/10000000000 : ℝ)*X 1 1+(1144097289/2500000000 : ℝ)*X 1 2+(4368350291/10000000000 : ℝ)*X 2 0+(4169808651/10000000000 : ℝ)*X 2 1+(1144097289/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1091903401/5000000000 : ℝ)*X 0 0+(1045715491/2000000000 : ℝ)*X 0 1+(5433065417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302822869/10000000000 : ℝ)*X 1 0+(-32561759/156250000 : ℝ)*X 1 1+(1086613097/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302823373/10000000000 : ℝ)*X 2 0+(5433065761/10000000000 : ℝ)*X 2 1+(-1041975757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184194997/5000000000 : ℝ)*X 0 0+(1143690473/2500000000 : ℝ)*X 0 1+(4171445829/10000000000 : ℝ)*X 0 2+(2184194997/5000000000 : ℝ)*X 1 0+(1143690473/2500000000 : ℝ)*X 1 1+(4171445829/10000000000 : ℝ)*X 1 2+(2184194997/5000000000 : ℝ)*X 2 0+(1143690473/2500000000 : ℝ)*X 2 1+(4171445829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45906235880148791489408211/16750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1046562067/100000000000000 : ℝ)*(base19) + (195390951/20000000000000 : ℝ)*(base23) + (5617209/5000000000000 : ℝ)*(lower2) + (932541/500000000000 : ℝ)*(upper5) + (1827645898698303/50000000000000 : ℝ)*(major0) + (1827645898698303/50000000000000 : ℝ)*(major1) + (1827645898698303/50000000000000 : ℝ)*(major2) + (4850998633569727/100000000000000 : ℝ)*(sp0) + (2425513283801853/50000000000000 : ℝ)*(sp1) + (970205378722923/20000000000000 : ℝ)*(sp2) + (2459547137340987/100000000000000 : ℝ)*(sp3) + (29236999643/100000000000000 : ℝ)*(sp4) + (256403597/100000000000000 : ℝ)*(sp5) + (4247763577/50000000000000 : ℝ)*(sp7) + (2459555632868141/100000000000000 : ℝ)*(f.failure) + (485102787056937/10000000000000 : ℝ)*(f.sum) + (1102036689617/335000000000000000000000000 : ℝ)*base66 + (269017665179147263/33500000000000000000000000000000 : ℝ)*base67 + (272305037699647263/33500000000000000000000000000000 : ℝ)*base69 + (358997691334147263/33500000000000000000000000000000 : ℝ)*base71 + (1684257086507/335000000000000000000000000 : ℝ)*base74 + (295216019885647263/33500000000000000000000000000000 : ℝ)*base75 + (165146660910352737/33500000000000000000000000000000 : ℝ)*base78 + (391402706444852737/33500000000000000000000000000000 : ℝ)*base80 + (189163467621/167500000000000000000000000 : ℝ)*base82 + (30628037/10000000000000000000000 : ℝ)*base90 + (30628037/10000000000000000000000 : ℝ)*base92 + (30628037/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (271259258115394214936394927/485750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136267841/50000000000000 : ℝ)*(base19) + (769642373/50000000000000 : ℝ)*(base23) + (230358991/100000000000000 : ℝ)*(upper2) + (132634769/100000000000000 : ℝ)*(upper3) + (37855419/100000000000000 : ℝ)*(upper5) + (1842427306504333/50000000000000 : ℝ)*(major0) + (1842427306504333/50000000000000 : ℝ)*(major1) + (1842427306504333/50000000000000 : ℝ)*(major2) + (122175563/10000000000000 : ℝ)*(sp1) + (1546578747/4000000000000 : ℝ)*(sp2) + (195610459422403/4000000000000 : ℝ)*(sp4) + (4890259991268763/100000000000000 : ℝ)*(sp5) + (4890221281806653/100000000000000 : ℝ)*(sp6) + (123972386092139/5000000000000 : ℝ)*(sp7) + (123972386092139/5000000000000 : ℝ)*(f.failure) + (195610459422403/4000000000000 : ℝ)*(f.sum) + (11344836140743/2428750000000000000000000000 : ℝ)*base65 + (7043883760763783897/971500000000000000000000000000000 : ℝ)*base67 + (12108758198048783897/971500000000000000000000000000000 : ℝ)*base69 + (4675792198100783897/971500000000000000000000000000000 : ℝ)*base71 + (2040816972377/2428750000000000000000000000 : ℝ)*base74 + (8246093385173783897/971500000000000000000000000000000 : ℝ)*base75 + (9797579036727783897/971500000000000000000000000000000 : ℝ)*base77 + (3938972011729283897/971500000000000000000000000000000 : ℝ)*base79 + (18295627046251/4857500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7627923/500000000000000000000 : ℝ)*base90 + (7627923/500000000000000000000 : ℝ)*base92 + (7627923/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1098_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8319/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4433/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14861/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1098_s4_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-437433001/2000000000 : ℝ)*x 0 + (2702044689/5000000000 : ℝ)*x 1 + (5255349813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437433001/2000000000 : ℝ)^8291 ≤ (2656815484759/20000000000000 : ℝ)^6243 := by
    have hnat : (437433001 : ℕ)^8291*20000000000000^6243 ≤ 2656815484759^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437433001 2000000000 2656815484759 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702044689/5000000000 : ℝ)^8291 ≤ (138004376729/312500000000 : ℝ)^6243 := by
    have hnat : (2702044689 : ℕ)^8291*312500000000^6243 ≤ 138004376729^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702044689 5000000000 138004376729 312500000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255349813/10000000000 : ℝ)^8291 ≤ (42554522005061/100000000000000 : ℝ)^6243 := by
    have hnat : (5255349813 : ℕ)^8291*100000000000000^6243 ≤ 42554522005061^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255349813 10000000000 42554522005061 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437433001/2000000000 : ℝ), (2702044689/5000000000 : ℝ), (5255349813/10000000000 : ℝ)] ![(2656815484759/20000000000000 : ℝ), (138004376729/312500000000 : ℝ), (42554522005061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437433001/2000000000 : ℝ)|^8291 ≤ (2656815484759/20000000000000 : ℝ)^6243
        have hw : |(-437433001/2000000000 : ℝ)|=(437433001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702044689/5000000000 : ℝ)|^8291 ≤ (138004376729/312500000000 : ℝ)^6243
        have hw : |(2702044689/5000000000 : ℝ)|=(2702044689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255349813/10000000000 : ℝ)|^8291 ≤ (42554522005061/100000000000000 : ℝ)^6243
        have hw : |(5255349813/10000000000 : ℝ)|=(5255349813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s4_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347467903/10000000000 : ℝ)*x 0 + (-226279021/1000000000 : ℝ)*x 1 + (525534967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347467903/10000000000 : ℝ)^8291 ≤ (10886992180673/25000000000000 : ℝ)^6243 := by
    have hnat : (5347467903 : ℕ)^8291*25000000000000^6243 ≤ 10886992180673^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347467903 10000000000 10886992180673 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226279021/1000000000 : ℝ)^8291 ≤ (173718885017/1250000000000 : ℝ)^6243 := by
    have hnat : (226279021 : ℕ)^8291*1250000000000^6243 ≤ 173718885017^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226279021 1000000000 173718885017 1250000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525534967/1000000000 : ℝ)^8291 ≤ (21277260233641/50000000000000 : ℝ)^6243 := by
    have hnat : (525534967 : ℕ)^8291*50000000000000^6243 ≤ 21277260233641^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525534967 1000000000 21277260233641 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347467903/10000000000 : ℝ), (-226279021/1000000000 : ℝ), (525534967/1000000000 : ℝ)] ![(10886992180673/25000000000000 : ℝ), (173718885017/1250000000000 : ℝ), (21277260233641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347467903/10000000000 : ℝ)|^8291 ≤ (10886992180673/25000000000000 : ℝ)^6243
        have hw : |(5347467903/10000000000 : ℝ)|=(5347467903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226279021/1000000000 : ℝ)|^8291 ≤ (173718885017/1250000000000 : ℝ)^6243
        have hw : |(-226279021/1000000000 : ℝ)|=(226279021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525534967/1000000000 : ℝ)|^8291 ≤ (21277260233641/50000000000000 : ℝ)^6243
        have hw : |(525534967/1000000000 : ℝ)|=(525534967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s4_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347468319/10000000000 : ℝ)*x 0 + (2627674777/5000000000 : ℝ)*x 1 + (-2262789811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347468319/10000000000 : ℝ)^8291 ≤ (21773986610901/50000000000000 : ℝ)^6243 := by
    have hnat : (5347468319 : ℕ)^8291*50000000000000^6243 ≤ 21773986610901^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347468319 10000000000 21773986610901 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627674777/5000000000 : ℝ)^8291 ≤ (21277259609927/50000000000000 : ℝ)^6243 := by
    have hnat : (2627674777 : ℕ)^8291*50000000000000^6243 ≤ 21277259609927^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627674777 5000000000 21277259609927 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262789811/10000000000 : ℝ)^8291 ≤ (6948753773449/50000000000000 : ℝ)^6243 := by
    have hnat : (2262789811 : ℕ)^8291*50000000000000^6243 ≤ 6948753773449^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262789811 10000000000 6948753773449 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347468319/10000000000 : ℝ), (2627674777/5000000000 : ℝ), (-2262789811/10000000000 : ℝ)] ![(21773986610901/50000000000000 : ℝ), (21277259609927/50000000000000 : ℝ), (6948753773449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347468319/10000000000 : ℝ)|^8291 ≤ (21773986610901/50000000000000 : ℝ)^6243
        have hw : |(5347468319/10000000000 : ℝ)|=(5347468319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627674777/5000000000 : ℝ)|^8291 ≤ (21277259609927/50000000000000 : ℝ)^6243
        have hw : |(2627674777/5000000000 : ℝ)|=(2627674777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2262789811/10000000000 : ℝ)|^8291 ≤ (6948753773449/50000000000000 : ℝ)^6243
        have hw : |(-2262789811/10000000000 : ℝ)|=(2262789811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s4_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546295317/1250000000 : ℝ)*x 0 + (4226155299/10000000000 : ℝ)*x 1 + (4519517379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546295317/1250000000 : ℝ)^8291 ≤ (4163898762013/12500000000000 : ℝ)^6243 := by
    have hnat : (546295317 : ℕ)^8291*12500000000000^6243 ≤ 4163898762013^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546295317 1250000000 4163898762013 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226155299/10000000000 : ℝ)^8291 ≤ (31859417069733/100000000000000 : ℝ)^6243 := by
    have hnat : (4226155299 : ℕ)^8291*100000000000000^6243 ≤ 31859417069733^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226155299 10000000000 31859417069733 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519517379/10000000000 : ℝ)^8291 ≤ (34829392821701/100000000000000 : ℝ)^6243 := by
    have hnat : (4519517379 : ℕ)^8291*100000000000000^6243 ≤ 34829392821701^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519517379 10000000000 34829392821701 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546295317/1250000000 : ℝ), (4226155299/10000000000 : ℝ), (4519517379/10000000000 : ℝ)] ![(4163898762013/12500000000000 : ℝ), (31859417069733/100000000000000 : ℝ), (34829392821701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546295317/1250000000 : ℝ)|^8291 ≤ (4163898762013/12500000000000 : ℝ)^6243
        have hw : |(546295317/1250000000 : ℝ)|=(546295317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226155299/10000000000 : ℝ)|^8291 ≤ (31859417069733/100000000000000 : ℝ)^6243
        have hw : |(4226155299/10000000000 : ℝ)|=(4226155299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519517379/10000000000 : ℝ)|^8291 ≤ (34829392821701/100000000000000 : ℝ)^6243
        have hw : |(4519517379/10000000000 : ℝ)|=(4519517379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s4_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-546793337/2500000000 : ℝ)*x 0 + (5255780149/10000000000 : ℝ)*x 1 + (5403656751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546793337/2500000000 : ℝ)^8291 ≤ (6642072359641/50000000000000 : ℝ)^6243 := by
    have hnat : (546793337 : ℕ)^8291*50000000000000^6243 ≤ 6642072359641^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546793337 2500000000 6642072359641 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255780149/10000000000 : ℝ)^8291 ≤ (42559149768803/100000000000000 : ℝ)^6243 := by
    have hnat : (5255780149 : ℕ)^8291*100000000000000^6243 ≤ 42559149768803^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255780149 10000000000 42559149768803 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403656751/10000000000 : ℝ)^8291 ≤ (22078352743041/50000000000000 : ℝ)^6243 := by
    have hnat : (5403656751 : ℕ)^8291*50000000000000^6243 ≤ 22078352743041^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403656751 10000000000 22078352743041 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546793337/2500000000 : ℝ), (5255780149/10000000000 : ℝ), (5403656751/10000000000 : ℝ)] ![(6642072359641/50000000000000 : ℝ), (42559149768803/100000000000000 : ℝ), (22078352743041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546793337/2500000000 : ℝ)|^8291 ≤ (6642072359641/50000000000000 : ℝ)^6243
        have hw : |(-546793337/2500000000 : ℝ)|=(546793337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255780149/10000000000 : ℝ)|^8291 ≤ (42559149768803/100000000000000 : ℝ)^6243
        have hw : |(5255780149/10000000000 : ℝ)|=(5255780149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403656751/10000000000 : ℝ)|^8291 ≤ (22078352743041/50000000000000 : ℝ)^6243
        have hw : |(5403656751/10000000000 : ℝ)|=(5403656751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s4_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530991169/1000000000 : ℝ)*x 0 + (-211448239/1000000000 : ℝ)*x 1 + (1350914229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530991169/1000000000 : ℝ)^8291 ≤ (21571130293001/50000000000000 : ℝ)^6243 := by
    have hnat : (530991169 : ℕ)^8291*50000000000000^6243 ≤ 21571130293001^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530991169 1000000000 21571130293001 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211448239/1000000000 : ℝ)^8291 ≤ (12701032116511/100000000000000 : ℝ)^6243 := by
    have hnat : (211448239 : ℕ)^8291*100000000000000^6243 ≤ 12701032116511^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211448239 1000000000 12701032116511 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350914229/2500000000 : ℝ)^8291 ≤ (22078353638357/50000000000000 : ℝ)^6243 := by
    have hnat : (1350914229 : ℕ)^8291*50000000000000^6243 ≤ 22078353638357^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350914229 2500000000 22078353638357 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530991169/1000000000 : ℝ), (-211448239/1000000000 : ℝ), (1350914229/2500000000 : ℝ)] ![(21571130293001/50000000000000 : ℝ), (12701032116511/100000000000000 : ℝ), (22078353638357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530991169/1000000000 : ℝ)|^8291 ≤ (21571130293001/50000000000000 : ℝ)^6243
        have hw : |(530991169/1000000000 : ℝ)|=(530991169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211448239/1000000000 : ℝ)|^8291 ≤ (12701032116511/100000000000000 : ℝ)^6243
        have hw : |(-211448239/1000000000 : ℝ)|=(211448239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350914229/2500000000 : ℝ)|^8291 ≤ (22078353638357/50000000000000 : ℝ)^6243
        have hw : |(1350914229/2500000000 : ℝ)|=(1350914229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s4_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309911617/10000000000 : ℝ)*x 0 + (5403657187/10000000000 : ℝ)*x 1 + (-2114482121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309911617/10000000000 : ℝ)^8291 ≤ (21571129899159/50000000000000 : ℝ)^6243 := by
    have hnat : (5309911617 : ℕ)^8291*50000000000000^6243 ≤ 21571129899159^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309911617 10000000000 21571129899159 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403657187/10000000000 : ℝ)^8291 ≤ (11039177554423/25000000000000 : ℝ)^6243 := by
    have hnat : (5403657187 : ℕ)^8291*25000000000000^6243 ≤ 11039177554423^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403657187 10000000000 11039177554423 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114482121/10000000000 : ℝ)^8291 ≤ (6350514985327/50000000000000 : ℝ)^6243 := by
    have hnat : (2114482121 : ℕ)^8291*50000000000000^6243 ≤ 6350514985327^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114482121 10000000000 6350514985327 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309911617/10000000000 : ℝ), (5403657187/10000000000 : ℝ), (-2114482121/10000000000 : ℝ)] ![(21571129899159/50000000000000 : ℝ), (11039177554423/25000000000000 : ℝ), (6350514985327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309911617/10000000000 : ℝ)|^8291 ≤ (21571129899159/50000000000000 : ℝ)^6243
        have hw : |(5309911617/10000000000 : ℝ)|=(5309911617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403657187/10000000000 : ℝ)|^8291 ≤ (11039177554423/25000000000000 : ℝ)^6243
        have hw : |(5403657187/10000000000 : ℝ)|=(5403657187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2114482121/10000000000 : ℝ)|^8291 ≤ (6350514985327/50000000000000 : ℝ)^6243
        have hw : |(-2114482121/10000000000 : ℝ)|=(2114482121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s4_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370377531/10000000000 : ℝ)*x 0 + (2259334191/5000000000 : ℝ)*x 1 + (4227007979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370377531/10000000000 : ℝ)^8291 ≤ (6662268376509/20000000000000 : ℝ)^6243 := by
    have hnat : (4370377531 : ℕ)^8291*20000000000000^6243 ≤ 6662268376509^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370377531 10000000000 6662268376509 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259334191/5000000000 : ℝ)^8291 ≤ (6964140802757/20000000000000 : ℝ)^6243 := by
    have hnat : (2259334191 : ℕ)^8291*20000000000000^6243 ≤ 6964140802757^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259334191 5000000000 6964140802757 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227007979/10000000000 : ℝ)^8291 ≤ (31867954091751/100000000000000 : ℝ)^6243 := by
    have hnat : (4227007979 : ℕ)^8291*100000000000000^6243 ≤ 31867954091751^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227007979 10000000000 31867954091751 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370377531/10000000000 : ℝ), (2259334191/5000000000 : ℝ), (4227007979/10000000000 : ℝ)] ![(6662268376509/20000000000000 : ℝ), (6964140802757/20000000000000 : ℝ), (31867954091751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370377531/10000000000 : ℝ)|^8291 ≤ (6662268376509/20000000000000 : ℝ)^6243
        have hw : |(4370377531/10000000000 : ℝ)|=(4370377531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259334191/5000000000 : ℝ)|^8291 ≤ (6964140802757/20000000000000 : ℝ)^6243
        have hw : |(2259334191/5000000000 : ℝ)|=(2259334191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227007979/10000000000 : ℝ)|^8291 ≤ (31867954091751/100000000000000 : ℝ)^6243
        have hw : |(4227007979/10000000000 : ℝ)|=(4227007979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14861/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h) :
    (11089/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14861/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (21/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14861/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (21/200 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14861/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (21/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14861/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (21/200 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14861/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (21/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14861/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (21/200 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (21/200 : ℝ) ^ (4145/1024 : ℝ) ≤ (2728095589899471/25000000000000000000 : ℝ) := by
    have hpowers : (21/200 : ℝ)^4145 ≤ (2728095589899471/25000000000000000000 : ℝ)^1024 := by
      have hnat : (21 : ℕ)^4145*25000000000000000000^1024 ≤ 2728095589899471^1024*200^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21 200 2728095589899471 25000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21/200 : ℝ)) (X := (2728095589899471/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14861/100000 : ℝ) ^ (4145/1024 : ℝ) ≤ (22260932143561797/50000000000000000000 : ℝ) := by
    have hpowers : (14861/100000 : ℝ)^4145 ≤ (22260932143561797/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14861 : ℕ)^4145*50000000000000000000^1024 ≤ 22260932143561797^1024*100000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14861 100000 22260932143561797 50000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14861/100000 : ℝ)) (X := (22260932143561797/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502728095589899471/12500000000000000000 : ℝ) ≤ (2000107824960333/2000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (12502728095589899471/12500000000000000000 : ℝ)^1024 ≤ (2000107824960333/2000000000000000 : ℝ)^4145 := by
      have hnat : (12502728095589899471 : ℕ)^1024*2000000000000000^4145 ≤ 2000107824960333^4145*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502728095589899471 12500000000000000000 2000107824960333 2000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107824960333/2000000000000000 : ℝ)) (X := (12502728095589899471/12500000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027717123323360739/50000000000000000000 : ℝ) ≤ (5000684593796789/5000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50027717123323360739/50000000000000000000 : ℝ)^1024 ≤ (5000684593796789/5000000000000000 : ℝ)^4145 := by
      have hnat : (50027717123323360739 : ℕ)^1024*5000000000000000^4145 ≤ 5000684593796789^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027717123323360739 50000000000000000000 5000684593796789 5000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000684593796789/5000000000000000 : ℝ)) (X := (50027717123323360739/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022260932143561797/25000000000000000000 : ℝ) ≤ (10002199250385491/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25022260932143561797/25000000000000000000 : ℝ)^1024 ≤ (10002199250385491/10000000000000000 : ℝ)^4145 := by
      have hnat : (25022260932143561797 : ℕ)^1024*10000000000000000^4145 ≤ 10002199250385491^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022260932143561797 25000000000000000000 10002199250385491 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002199250385491/10000000000000000 : ℝ)) (X := (25022260932143561797/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2728095589899471/25000000000000000000 : ℝ) ≤ ((1245569137275139659/1246000000000000000 : ℝ)+2*(830062791913/436100000000000 : ℝ)*(21/200 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (1245569137275139659/1246000000000000000 : ℝ)+2*(830062791913/436100000000000 : ℝ)*(21/200 : ℝ)=(2000107824960333/2000000000000000 : ℝ) by norm_num, show 1+2*(2728095589899471/25000000000000000000 : ℝ)=(12502728095589899471/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22260932143561797/50000000000000000000 : ℝ)+(2728095589899471/25000000000000000000 : ℝ) ≤ ((1245569137275139659/1246000000000000000 : ℝ)+(830062791913/436100000000000 : ℝ)*((14861/100000 : ℝ)+(21/200 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (1245569137275139659/1246000000000000000 : ℝ)+(830062791913/436100000000000 : ℝ)*((14861/100000 : ℝ)+(21/200 : ℝ))=(5000684593796789/5000000000000000 : ℝ) by norm_num, show 1+(22260932143561797/50000000000000000000 : ℝ)+(2728095589899471/25000000000000000000 : ℝ)=(50027717123323360739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22260932143561797/50000000000000000000 : ℝ) ≤ ((1245569137275139659/1246000000000000000 : ℝ)+2*(830062791913/436100000000000 : ℝ)*(14861/100000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (1245569137275139659/1246000000000000000 : ℝ)+2*(830062791913/436100000000000 : ℝ)*(14861/100000 : ℝ)=(10002199250385491/10000000000000000 : ℝ) by norm_num, show 1+2*(22260932143561797/50000000000000000000 : ℝ)=(25022260932143561797/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1245569137275139659/1246000000000000000 : ℝ)*(X 1 0+X 2 0)+(830062791913/436100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (21/200 : ℝ)) (hi := (14861/100000 : ℝ)) (c := (1245569137275139659/1246000000000000000 : ℝ)) (alpha := (830062791913/436100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1245569137275139659/1246000000000000000 : ℝ)*(X 0 1+X 2 1)+(830062791913/436100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (21/200 : ℝ)) (hi := (14861/100000 : ℝ)) (c := (1245569137275139659/1246000000000000000 : ℝ)) (alpha := (830062791913/436100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1245569137275139659/1246000000000000000 : ℝ)*(X 0 2+X 1 2)+(830062791913/436100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (21/200 : ℝ)) (hi := (14861/100000 : ℝ)) (c := (1245569137275139659/1246000000000000000 : ℝ)) (alpha := (830062791913/436100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-437433001/2000000000 : ℝ)*X 0 0+(2702044689/5000000000 : ℝ)*X 0 1+(5255349813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347467903/10000000000 : ℝ)*X 1 0+(-226279021/1000000000 : ℝ)*X 1 1+(525534967/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347468319/10000000000 : ℝ)*X 2 0+(2627674777/5000000000 : ℝ)*X 2 1+(-2262789811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546295317/1250000000 : ℝ)*X 0 0+(4226155299/10000000000 : ℝ)*X 0 1+(4519517379/10000000000 : ℝ)*X 0 2+(546295317/1250000000 : ℝ)*X 1 0+(4226155299/10000000000 : ℝ)*X 1 1+(4519517379/10000000000 : ℝ)*X 1 2+(546295317/1250000000 : ℝ)*X 2 0+(4226155299/10000000000 : ℝ)*X 2 1+(4519517379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-546793337/2500000000 : ℝ)*X 0 0+(5255780149/10000000000 : ℝ)*X 0 1+(5403656751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530991169/1000000000 : ℝ)*X 1 0+(-211448239/1000000000 : ℝ)*X 1 1+(1350914229/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309911617/10000000000 : ℝ)*X 2 0+(5403657187/10000000000 : ℝ)*X 2 1+(-2114482121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370377531/10000000000 : ℝ)*X 0 0+(2259334191/5000000000 : ℝ)*X 0 1+(4227007979/10000000000 : ℝ)*X 0 2+(4370377531/10000000000 : ℝ)*X 1 0+(2259334191/5000000000 : ℝ)*X 1 1+(4227007979/10000000000 : ℝ)*X 1 2+(4370377531/10000000000 : ℝ)*X 2 0+(2259334191/5000000000 : ℝ)*X 2 1+(4227007979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2027818244580889894540560861/218050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68761053/50000000000000 : ℝ)*(base19) + (55119053/12500000000000 : ℝ)*(lower2) + (36281063/50000000000000 : ℝ)*(lower4) + (3754151/25000000000000 : ℝ)*(upper5) + (5065952243741701/100000000000000 : ℝ)*(major0) + (5065952243741701/100000000000000 : ℝ)*(major1) + (5065952243741701/100000000000000 : ℝ)*(major2) + (3361573995784179/50000000000000 : ℝ)*(sp0) + (6723145771103337/100000000000000 : ℝ)*(sp1) + (6723149947305627/100000000000000 : ℝ)*(sp2) + (3408752771445929/100000000000000 : ℝ)*(sp3) + (1955737269/100000000000000 : ℝ)*(sp4) + (504835023/12500000000000 : ℝ)*(sp5) + (291747797/20000000000000 : ℝ)*(sp7) + (1704377115092457/50000000000000 : ℝ)*(f.failure) + (6723149947305627/100000000000000 : ℝ)*(f.sum) + (10246782691559/2725625000000000000000000000 : ℝ)*base66 + (3768047055959599713/872200000000000000000000000000000 : ℝ)*base67 + (8560387431776999713/872200000000000000000000000000000 : ℝ)*base69 + (3071510551289200287/872200000000000000000000000000000 : ℝ)*base72 + (25358223888329/10902500000000000000000000000 : ℝ)*base73 + (14825896085932799713/872200000000000000000000000000000 : ℝ)*base75 + (15160707280138399713/872200000000000000000000000000000 : ℝ)*base77 + (5287623591752999713/872200000000000000000000000000000 : ℝ)*base79 + (711517293317/5451250000000000000000000000 : ℝ)*base81 + (20758049/5000000000000000000000 : ℝ)*base90 + (20758049/5000000000000000000000 : ℝ)*base92 + (20758049/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195996229944320091183970467/109025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (446470607/100000000000000 : ℝ)*(base19) + (551465057/100000000000000 : ℝ)*(base23) + (39182779/100000000000000 : ℝ)*(upper2) + (13348871/12500000000000 : ℝ)*(upper3) + (2547759801499947/50000000000000 : ℝ)*(major0) + (2547759801499947/50000000000000 : ℝ)*(major1) + (2547759801499947/50000000000000 : ℝ)*(major2) + (14159906321/100000000000000 : ℝ)*(sp1) + (6343104043/20000000000000 : ℝ)*(sp2) + (51520443/4000000000000 : ℝ)*(sp3) + (6762389769608947/100000000000000 : ℝ)*(sp4) + (6762375163232019/100000000000000 : ℝ)*(sp5) + (270494300104947/4000000000000 : ℝ)*(sp6) + (3428648088455819/100000000000000 : ℝ)*(sp7) + (1714324688233447/50000000000000 : ℝ)*(f.failure) + (6762389769608947/100000000000000 : ℝ)*(f.sum) + (102231648484843/21805000000000000000000000000 : ℝ)*base66 + (2550525088580306511/436100000000000000000000000000000 : ℝ)*base67 + (991180182544606511/436100000000000000000000000000000 : ℝ)*base69 + (3919110821676706511/436100000000000000000000000000000 : ℝ)*base71 + (107670773378493/21805000000000000000000000000 : ℝ)*base74 + (2756535124855093489/436100000000000000000000000000000 : ℝ)*base76 + (2491500801336006511/436100000000000000000000000000000 : ℝ)*base77 + (5859240545105106511/436100000000000000000000000000000 : ℝ)*base79 + (11098273359627/5451250000000000000000000000 : ℝ)*base82 + (30045521/5000000000000000000000 : ℝ)*base89 + (30045521/5000000000000000000000 : ℝ)*base91 + (30045521/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1098_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14861/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1098_s5_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-87516341/400000000 : ℝ)*x 0 + (5396090579/10000000000 : ℝ)*x 1 + (5262860733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87516341/400000000 : ℝ)^8291 ≤ (13290075062471/100000000000000 : ℝ)^6243 := by
    have hnat : (87516341 : ℕ)^8291*100000000000000^6243 ≤ 13290075062471^6243*400000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87516341 400000000 13290075062471 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396090579/10000000000 : ℝ)^8291 ≤ (22037306924719/50000000000000 : ℝ)^6243 := by
    have hnat : (5396090579 : ℕ)^8291*50000000000000^6243 ≤ 22037306924719^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396090579 10000000000 22037306924719 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262860733/10000000000 : ℝ)^8291 ≤ (42635311067359/100000000000000 : ℝ)^6243 := by
    have hnat : (5262860733 : ℕ)^8291*100000000000000^6243 ≤ 42635311067359^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262860733 10000000000 42635311067359 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87516341/400000000 : ℝ), (5396090579/10000000000 : ℝ), (5262860733/10000000000 : ℝ)] ![(13290075062471/100000000000000 : ℝ), (22037306924719/50000000000000 : ℝ), (42635311067359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87516341/400000000 : ℝ)|^8291 ≤ (13290075062471/100000000000000 : ℝ)^6243
        have hw : |(-87516341/400000000 : ℝ)|=(87516341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396090579/10000000000 : ℝ)|^8291 ≤ (22037306924719/50000000000000 : ℝ)^6243
        have hw : |(5396090579/10000000000 : ℝ)|=(5396090579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262860733/10000000000 : ℝ)|^8291 ≤ (42635311067359/100000000000000 : ℝ)^6243
        have hw : |(5262860733/10000000000 : ℝ)|=(5262860733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s5_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345471403/10000000000 : ℝ)*x 0 + (-70485379/312500000 : ℝ)*x 1 + (5262857969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345471403/10000000000 : ℝ)^8291 ≤ (43526377560899/100000000000000 : ℝ)^6243 := by
    have hnat : (5345471403 : ℕ)^8291*100000000000000^6243 ≤ 43526377560899^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345471403 10000000000 43526377560899 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70485379/312500000 : ℝ)^8291 ≤ (6919170544059/50000000000000 : ℝ)^6243 := by
    have hnat : (70485379 : ℕ)^8291*50000000000000^6243 ≤ 6919170544059^6243*312500000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70485379 312500000 6919170544059 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262857969/10000000000 : ℝ)^8291 ≤ (42635281330223/100000000000000 : ℝ)^6243 := by
    have hnat : (5262857969 : ℕ)^8291*100000000000000^6243 ≤ 42635281330223^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262857969 10000000000 42635281330223 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345471403/10000000000 : ℝ), (-70485379/312500000 : ℝ), (5262857969/10000000000 : ℝ)] ![(43526377560899/100000000000000 : ℝ), (6919170544059/50000000000000 : ℝ), (42635281330223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345471403/10000000000 : ℝ)|^8291 ≤ (43526377560899/100000000000000 : ℝ)^6243
        have hw : |(5345471403/10000000000 : ℝ)|=(5345471403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70485379/312500000 : ℝ)|^8291 ≤ (6919170544059/50000000000000 : ℝ)^6243
        have hw : |(-70485379/312500000 : ℝ)|=(70485379/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262857969/10000000000 : ℝ)|^8291 ≤ (42635281330223/100000000000000 : ℝ)^6243
        have hw : |(5262857969/10000000000 : ℝ)|=(5262857969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s5_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534547043/1000000000 : ℝ)*x 0 + (657857499/1250000000 : ℝ)*x 1 + (-2255530749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534547043/1000000000 : ℝ)^8291 ≤ (43526367039029/100000000000000 : ℝ)^6243 := by
    have hnat : (534547043 : ℕ)^8291*100000000000000^6243 ≤ 43526367039029^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534547043 1000000000 43526367039029 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657857499/1250000000 : ℝ)^8291 ≤ (21317651547569/50000000000000 : ℝ)^6243 := by
    have hnat : (657857499 : ℕ)^8291*50000000000000^6243 ≤ 21317651547569^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657857499 1250000000 21317651547569 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255530749/10000000000 : ℝ)^8291 ≤ (1383832985209/10000000000000 : ℝ)^6243 := by
    have hnat : (2255530749 : ℕ)^8291*10000000000000^6243 ≤ 1383832985209^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255530749 10000000000 1383832985209 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534547043/1000000000 : ℝ), (657857499/1250000000 : ℝ), (-2255530749/10000000000 : ℝ)] ![(43526367039029/100000000000000 : ℝ), (21317651547569/50000000000000 : ℝ), (1383832985209/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534547043/1000000000 : ℝ)|^8291 ≤ (43526367039029/100000000000000 : ℝ)^6243
        have hw : |(534547043/1000000000 : ℝ)|=(534547043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657857499/1250000000 : ℝ)|^8291 ≤ (21317651547569/50000000000000 : ℝ)^6243
        have hw : |(657857499/1250000000 : ℝ)|=(657857499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2255530749/10000000000 : ℝ)|^8291 ≤ (1383832985209/10000000000000 : ℝ)^6243
        have hw : |(-2255530749/10000000000 : ℝ)|=(2255530749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s5_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185397237/5000000000 : ℝ)*x 0 + (1060348101/2500000000 : ℝ)*x 1 + (70377617/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185397237/5000000000 : ℝ)^8291 ≤ (16657781222037/50000000000000 : ℝ)^6243 := by
    have hnat : (2185397237 : ℕ)^8291*50000000000000^6243 ≤ 16657781222037^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185397237 5000000000 16657781222037 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060348101/2500000000 : ℝ)^8291 ≤ (32012055876429/100000000000000 : ℝ)^6243 := by
    have hnat : (1060348101 : ℕ)^8291*100000000000000^6243 ≤ 32012055876429^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060348101 2500000000 32012055876429 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70377617/156250000 : ℝ)^8291 ≤ (17336190829619/50000000000000 : ℝ)^6243 := by
    have hnat : (70377617 : ℕ)^8291*50000000000000^6243 ≤ 17336190829619^6243*156250000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70377617 156250000 17336190829619 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185397237/5000000000 : ℝ), (1060348101/2500000000 : ℝ), (70377617/156250000 : ℝ)] ![(16657781222037/50000000000000 : ℝ), (32012055876429/100000000000000 : ℝ), (17336190829619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185397237/5000000000 : ℝ)|^8291 ≤ (16657781222037/50000000000000 : ℝ)^6243
        have hw : |(2185397237/5000000000 : ℝ)|=(2185397237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060348101/2500000000 : ℝ)|^8291 ≤ (32012055876429/100000000000000 : ℝ)^6243
        have hw : |(1060348101/2500000000 : ℝ)|=(1060348101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70377617/156250000 : ℝ)|^8291 ≤ (17336190829619/50000000000000 : ℝ)^6243
        have hw : |(70377617/156250000 : ℝ)|=(70377617/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s5_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093957109/5000000000 : ℝ)*x 0 + (526320549/1000000000 : ℝ)*x 1 + (5395744397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093957109/5000000000 : ℝ)^8291 ≤ (132901209879/1000000000000 : ℝ)^6243 := by
    have hnat : (1093957109 : ℕ)^8291*1000000000000^6243 ≤ 132901209879^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093957109 5000000000 132901209879 1000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526320549/1000000000 : ℝ)^8291 ≤ (213195101279/500000000000 : ℝ)^6243 := by
    have hnat : (526320549 : ℕ)^8291*500000000000^6243 ≤ 213195101279^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526320549 1000000000 213195101279 500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395744397/10000000000 : ℝ)^8291 ≤ (11017714684613/25000000000000 : ℝ)^6243 := by
    have hnat : (5395744397 : ℕ)^8291*25000000000000^6243 ≤ 11017714684613^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395744397 10000000000 11017714684613 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093957109/5000000000 : ℝ), (526320549/1000000000 : ℝ), (5395744397/10000000000 : ℝ)] ![(132901209879/1000000000000 : ℝ), (213195101279/500000000000 : ℝ), (11017714684613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093957109/5000000000 : ℝ)|^8291 ≤ (132901209879/1000000000000 : ℝ)^6243
        have hw : |(-1093957109/5000000000 : ℝ)|=(1093957109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526320549/1000000000 : ℝ)|^8291 ≤ (213195101279/500000000000 : ℝ)^6243
        have hw : |(526320549/1000000000 : ℝ)|=(526320549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395744397/10000000000 : ℝ)|^8291 ≤ (11017714684613/25000000000000 : ℝ)^6243
        have hw : |(5395744397/10000000000 : ℝ)|=(5395744397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s5_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311828301/10000000000 : ℝ)*x 0 + (-265330769/1250000000 : ℝ)*x 1 + (5395744567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311828301/10000000000 : ℝ)^8291 ≤ (21581471205649/50000000000000 : ℝ)^6243 := by
    have hnat : (5311828301 : ℕ)^8291*50000000000000^6243 ≤ 21581471205649^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311828301 10000000000 21581471205649 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265330769/1250000000 : ℝ)^8291 ≤ (2553239398131/20000000000000 : ℝ)^6243 := by
    have hnat : (265330769 : ℕ)^8291*20000000000000^6243 ≤ 2553239398131^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265330769 1250000000 2553239398131 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395744567/10000000000 : ℝ)^8291 ≤ (44070860582459/100000000000000 : ℝ)^6243 := by
    have hnat : (5395744567 : ℕ)^8291*100000000000000^6243 ≤ 44070860582459^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395744567 10000000000 44070860582459 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311828301/10000000000 : ℝ), (-265330769/1250000000 : ℝ), (5395744567/10000000000 : ℝ)] ![(21581471205649/50000000000000 : ℝ), (2553239398131/20000000000000 : ℝ), (44070860582459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311828301/10000000000 : ℝ)|^8291 ≤ (21581471205649/50000000000000 : ℝ)^6243
        have hw : |(5311828301/10000000000 : ℝ)|=(5311828301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265330769/1250000000 : ℝ)|^8291 ≤ (2553239398131/20000000000000 : ℝ)^6243
        have hw : |(-265330769/1250000000 : ℝ)|=(265330769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395744567/10000000000 : ℝ)|^8291 ≤ (44070860582459/100000000000000 : ℝ)^6243
        have hw : |(5395744567/10000000000 : ℝ)|=(5395744567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s5_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531182799/1000000000 : ℝ)*x 0 + (5395744729/10000000000 : ℝ)*x 1 + (-2122646353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531182799/1000000000 : ℝ)^8291 ≤ (43162939055151/100000000000000 : ℝ)^6243 := by
    have hnat : (531182799 : ℕ)^8291*100000000000000^6243 ≤ 43162939055151^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531182799 1000000000 43162939055151 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395744729/10000000000 : ℝ)^8291 ≤ (44070862339689/100000000000000 : ℝ)^6243 := by
    have hnat : (5395744729 : ℕ)^8291*100000000000000^6243 ≤ 44070862339689^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395744729 10000000000 44070862339689 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122646353/10000000000 : ℝ)^8291 ≤ (12766198596093/100000000000000 : ℝ)^6243 := by
    have hnat : (2122646353 : ℕ)^8291*100000000000000^6243 ≤ 12766198596093^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122646353 10000000000 12766198596093 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531182799/1000000000 : ℝ), (5395744729/10000000000 : ℝ), (-2122646353/10000000000 : ℝ)] ![(43162939055151/100000000000000 : ℝ), (44070862339689/100000000000000 : ℝ), (12766198596093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531182799/1000000000 : ℝ)|^8291 ≤ (43162939055151/100000000000000 : ℝ)^6243
        have hw : |(531182799/1000000000 : ℝ)|=(531182799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395744729/10000000000 : ℝ)|^8291 ≤ (44070862339689/100000000000000 : ℝ)^6243
        have hw : |(5395744729/10000000000 : ℝ)|=(5395744729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122646353/10000000000 : ℝ)|^8291 ≤ (12766198596093/100000000000000 : ℝ)^6243
        have hw : |(-2122646353/10000000000 : ℝ)|=(2122646353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s5_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185402507/5000000000 : ℝ)*x 0 + (4503486221/10000000000 : ℝ)*x 1 + (4242076559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185402507/5000000000 : ℝ)^8291 ≤ (33315669138351/100000000000000 : ℝ)^6243 := by
    have hnat : (2185402507 : ℕ)^8291*100000000000000^6243 ≤ 33315669138351^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185402507 5000000000 33315669138351 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503486221/10000000000 : ℝ)^8291 ≤ (34665417169529/100000000000000 : ℝ)^6243 := by
    have hnat : (4503486221 : ℕ)^8291*100000000000000^6243 ≤ 34665417169529^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503486221 10000000000 34665417169529 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242076559/10000000000 : ℝ)^8291 ≤ (32018913674409/100000000000000 : ℝ)^6243 := by
    have hnat : (4242076559 : ℕ)^8291*100000000000000^6243 ≤ 32018913674409^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242076559 10000000000 32018913674409 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185402507/5000000000 : ℝ), (4503486221/10000000000 : ℝ), (4242076559/10000000000 : ℝ)] ![(33315669138351/100000000000000 : ℝ), (34665417169529/100000000000000 : ℝ), (32018913674409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185402507/5000000000 : ℝ)|^8291 ≤ (33315669138351/100000000000000 : ℝ)^6243
        have hw : |(2185402507/5000000000 : ℝ)|=(2185402507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503486221/10000000000 : ℝ)|^8291 ≤ (34665417169529/100000000000000 : ℝ)^6243
        have hw : |(4503486221/10000000000 : ℝ)|=(4503486221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242076559/10000000000 : ℝ)|^8291 ≤ (32018913674409/100000000000000 : ℝ)^6243
        have hw : |(4242076559/10000000000 : ℝ)|=(4242076559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11089/100000 : ℝ) ^ (4145/1024 : ℝ) ≤ (13610251237013673/100000000000000000000 : ℝ) := by
    have hpowers : (11089/100000 : ℝ)^4145 ≤ (13610251237013673/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11089 : ℕ)^4145*100000000000000000000^1024 ≤ 13610251237013673^1024*100000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11089 100000 13610251237013673 100000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11089/100000 : ℝ)) (X := (13610251237013673/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (4145/1024 : ℝ) ≤ (4679475510423413/12500000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^4145 ≤ (4679475510423413/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7119 : ℕ)^4145*12500000000000000000^1024 ≤ 4679475510423413^1024*50000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 4679475510423413 12500000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (4679475510423413/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013610251237013673/50000000000000000000 : ℝ) ≤ (5000336199499467/5000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50013610251237013673/50000000000000000000 : ℝ)^1024 ≤ (5000336199499467/5000000000000000 : ℝ)^4145 := by
      have hnat : (50013610251237013673 : ℕ)^1024*5000000000000000^4145 ≤ 5000336199499467^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013610251237013673 50000000000000000000 5000336199499467 5000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000336199499467/5000000000000000 : ℝ)) (X := (50013610251237013673/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051046055320400977/100000000000000000000 : ℝ) ≤ (10001260823120099/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (100051046055320400977/100000000000000000000 : ℝ)^1024 ≤ (10001260823120099/10000000000000000 : ℝ)^4145 := by
      have hnat : (100051046055320400977 : ℕ)^1024*10000000000000000^4145 ≤ 10001260823120099^4145*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051046055320400977 100000000000000000000 10001260823120099 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001260823120099/10000000000000000 : ℝ)) (X := (100051046055320400977/100000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254679475510423413/6250000000000000000 : ℝ) ≤ (625115577952579/625000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (6254679475510423413/6250000000000000000 : ℝ)^1024 ≤ (625115577952579/625000000000000 : ℝ)^4145 := by
      have hnat : (6254679475510423413 : ℕ)^1024*625000000000000^4145 ≤ 625115577952579^4145*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254679475510423413 6250000000000000000 625115577952579 625000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625115577952579/625000000000000 : ℝ)) (X := (6254679475510423413/6250000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13610251237013673/100000000000000000000 : ℝ) ≤ ((7869766828572111449/7872500000000000000 : ℝ)+2*(117684824233/62980000000000 : ℝ)*(11089/100000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (7869766828572111449/7872500000000000000 : ℝ)+2*(117684824233/62980000000000 : ℝ)*(11089/100000 : ℝ)=(5000336199499467/5000000000000000 : ℝ) by norm_num, show 1+2*(13610251237013673/100000000000000000000 : ℝ)=(50013610251237013673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4679475510423413/12500000000000000000 : ℝ)+(13610251237013673/100000000000000000000 : ℝ) ≤ ((7869766828572111449/7872500000000000000 : ℝ)+(117684824233/62980000000000 : ℝ)*((7119/50000 : ℝ)+(11089/100000 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (7869766828572111449/7872500000000000000 : ℝ)+(117684824233/62980000000000 : ℝ)*((7119/50000 : ℝ)+(11089/100000 : ℝ))=(10001260823120099/10000000000000000 : ℝ) by norm_num, show 1+(4679475510423413/12500000000000000000 : ℝ)+(13610251237013673/100000000000000000000 : ℝ)=(100051046055320400977/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4679475510423413/12500000000000000000 : ℝ) ≤ ((7869766828572111449/7872500000000000000 : ℝ)+2*(117684824233/62980000000000 : ℝ)*(7119/50000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (7869766828572111449/7872500000000000000 : ℝ)+2*(117684824233/62980000000000 : ℝ)*(7119/50000 : ℝ)=(625115577952579/625000000000000 : ℝ) by norm_num, show 1+2*(4679475510423413/12500000000000000000 : ℝ)=(6254679475510423413/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7869766828572111449/7872500000000000000 : ℝ)*(X 1 0+X 2 0)+(117684824233/62980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (7869766828572111449/7872500000000000000 : ℝ)) (alpha := (117684824233/62980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7869766828572111449/7872500000000000000 : ℝ)*(X 0 1+X 2 1)+(117684824233/62980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (7869766828572111449/7872500000000000000 : ℝ)) (alpha := (117684824233/62980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7869766828572111449/7872500000000000000 : ℝ)*(X 0 2+X 1 2)+(117684824233/62980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (7869766828572111449/7872500000000000000 : ℝ)) (alpha := (117684824233/62980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87516341/400000000 : ℝ)*X 0 0+(5396090579/10000000000 : ℝ)*X 0 1+(5262860733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345471403/10000000000 : ℝ)*X 1 0+(-70485379/312500000 : ℝ)*X 1 1+(5262857969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534547043/1000000000 : ℝ)*X 2 0+(657857499/1250000000 : ℝ)*X 2 1+(-2255530749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185397237/5000000000 : ℝ)*X 0 0+(1060348101/2500000000 : ℝ)*X 0 1+(70377617/156250000 : ℝ)*X 0 2+(2185397237/5000000000 : ℝ)*X 1 0+(1060348101/2500000000 : ℝ)*X 1 1+(70377617/156250000 : ℝ)*X 1 2+(2185397237/5000000000 : ℝ)*X 2 0+(1060348101/2500000000 : ℝ)*X 2 1+(70377617/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1093957109/5000000000 : ℝ)*X 0 0+(526320549/1000000000 : ℝ)*X 0 1+(5395744397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311828301/10000000000 : ℝ)*X 1 0+(-265330769/1250000000 : ℝ)*X 1 1+(5395744567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531182799/1000000000 : ℝ)*X 2 0+(5395744729/10000000000 : ℝ)*X 2 1+(-2122646353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185402507/5000000000 : ℝ)*X 0 0+(4503486221/10000000000 : ℝ)*X 0 1+(4242076559/10000000000 : ℝ)*X 0 2+(2185402507/5000000000 : ℝ)*X 1 0+(4503486221/10000000000 : ℝ)*X 1 1+(4242076559/10000000000 : ℝ)*X 1 2+(2185402507/5000000000 : ℝ)*X 2 0+(4503486221/10000000000 : ℝ)*X 2 1+(4242076559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (391966917561176833694072949/98406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1229431523/50000000000000 : ℝ)*(base19) + (1237877709/100000000000000 : ℝ)*(base23) + (27808831/20000000000000 : ℝ)*(lower2) + (3744669/100000000000000 : ℝ)*(lower3) + (1413927409509139/25000000000000 : ℝ)*(major0) + (1413927409509139/25000000000000 : ℝ)*(major1) + (1413927409509139/25000000000000 : ℝ)*(major2) + (1501166343702891/20000000000000 : ℝ)*(sp0) + (7505761076035917/100000000000000 : ℝ)*(sp1) + (3752913352287863/50000000000000 : ℝ)*(sp2) + (3805563472405631/100000000000000 : ℝ)*(sp3) + (17045903873/25000000000000 : ℝ)*(sp5) + (3776061019/100000000000000 : ℝ)*(sp6) + (1497023833/6250000000000 : ℝ)*(sp7) + (47569842809837/1250000000000 : ℝ)*(f.failure) + (1501166343702891/20000000000000 : ℝ)*(f.sum) + (877531260291/3149000000000000000000000000 : ℝ)*base66 + (2295694948790405089/196812500000000000000000000000000 : ℝ)*base68 + (2531571372025530089/196812500000000000000000000000000 : ℝ)*base70 + (682886275810905089/196812500000000000000000000000000 : ℝ)*base72 + (66378763/787250000000000000000000 : ℝ)*base74 + (3668618003917905089/196812500000000000000000000000000 : ℝ)*base76 + (3412455879542342589/196812500000000000000000000000000 : ℝ)*base78 + (494969528796780089/196812500000000000000000000000000 : ℝ)*base80 + (176848447497/3149000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (431291/125000000000000000000 : ℝ)*base89 + (431291/125000000000000000000 : ℝ)*base91 + (431291/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1625722872814470318747814533/196812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35724381/2500000000000 : ℝ)*(base19) + (57001377/5000000000000 : ℝ)*(base23) + (23140463/25000000000000 : ℝ)*(upper2) + (21416813/12500000000000 : ℝ)*(upper3) + (2842588643400013/50000000000000 : ℝ)*(major0) + (2842588643400013/50000000000000 : ℝ)*(major1) + (2842588643400013/50000000000000 : ℝ)*(major2) + (46269990153/100000000000000 : ℝ)*(sp1) + (42882814619/100000000000000 : ℝ)*(sp2) + (50893049/5000000000000 : ℝ)*(sp3) + (7544938819919929/100000000000000 : ℝ)*(sp4) + (943111390119317/12500000000000 : ℝ)*(sp5) + (7544894797077771/100000000000000 : ℝ)*(sp6) + (956353615119263/25000000000000 : ℝ)*(sp7) + (3825415478338031/100000000000000 : ℝ)*(f.failure) + (7544938819919929/100000000000000 : ℝ)*(f.sum) + (3240489536029/787250000000000000000000000 : ℝ)*base66 + (2471469939982076163/393625000000000000000000000000000 : ℝ)*base68 + (8331650102275951163/393625000000000000000000000000000 : ℝ)*base70 + (5282296712673201163/393625000000000000000000000000000 : ℝ)*base72 + (7754911162993/1574500000000000000000000000 : ℝ)*base74 + (4731239911531451163/393625000000000000000000000000000 : ℝ)*base76 + (4033957719708826163/393625000000000000000000000000000 : ℝ)*base78 + (9749963007938701163/393625000000000000000000000000000 : ℝ)*base80 + (5185538941941/393625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (50171767/10000000000000000000000 : ℝ)*base90 + (50171767/10000000000000000000000 : ℝ)*base92 + (50171767/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1098_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1098_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8319/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4433/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1098_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1098_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1098_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8319/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4433/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1098_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1239_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:06.633987+00:00
-- url     : https://prove2.me/submissions/78e6173d-4fef-455f-bc4a-7094b8c6de38

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
theorem support_rectangle_w1239_s6_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-66291459/312500000 : ℝ)*x 0 + (5391450653/10000000000 : ℝ)*x 1 + (1053397753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66291459/312500000 : ℝ)^527 ≤ (6449884146179/50000000000000 : ℝ)^399 := by
    have hnat : (66291459 : ℕ)^527*50000000000000^399 ≤ 6449884146179^399*312500000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66291459 312500000 6449884146179 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391450653/10000000000 : ℝ)^527 ≤ (44221784531447/100000000000000 : ℝ)^399 := by
    have hnat : (5391450653 : ℕ)^527*100000000000000^399 ≤ 44221784531447^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391450653 10000000000 44221784531447 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053397753/2000000000 : ℝ)^527 ≤ (10719611790321/25000000000000 : ℝ)^399 := by
    have hnat : (1053397753 : ℕ)^527*25000000000000^399 ≤ 10719611790321^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053397753 2000000000 10719611790321 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66291459/312500000 : ℝ), (5391450653/10000000000 : ℝ), (1053397753/2000000000 : ℝ)] ![(6449884146179/50000000000000 : ℝ), (44221784531447/100000000000000 : ℝ), (10719611790321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66291459/312500000 : ℝ)|^527 ≤ (6449884146179/50000000000000 : ℝ)^399
        have hw : |(-66291459/312500000 : ℝ)|=(66291459/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391450653/10000000000 : ℝ)|^527 ≤ (44221784531447/100000000000000 : ℝ)^399
        have hw : |(5391450653/10000000000 : ℝ)|=(5391450653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053397753/2000000000 : ℝ)|^527 ≤ (10719611790321/25000000000000 : ℝ)^399
        have hw : |(1053397753/2000000000 : ℝ)|=(1053397753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s6_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (267218747/500000000 : ℝ)*x 0 + (-1092217719/5000000000 : ℝ)*x 1 + (2633494381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267218747/500000000 : ℝ)^527 ≤ (10928126499689/25000000000000 : ℝ)^399 := by
    have hnat : (267218747 : ℕ)^527*25000000000000^399 ≤ 10928126499689^399*500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267218747 500000000 10928126499689 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092217719/5000000000 : ℝ)^527 ≤ (1340904686053/10000000000000 : ℝ)^399 := by
    have hnat : (1092217719 : ℕ)^527*10000000000000^399 ≤ 1340904686053^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092217719 5000000000 1340904686053 10000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633494381/5000000000 : ℝ)^527 ≤ (21439223564513/50000000000000 : ℝ)^399 := by
    have hnat : (2633494381 : ℕ)^527*50000000000000^399 ≤ 21439223564513^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633494381 5000000000 21439223564513 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267218747/500000000 : ℝ), (-1092217719/5000000000 : ℝ), (2633494381/5000000000 : ℝ)] ![(10928126499689/25000000000000 : ℝ), (1340904686053/10000000000000 : ℝ), (21439223564513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267218747/500000000 : ℝ)|^527 ≤ (10928126499689/25000000000000 : ℝ)^399
        have hw : |(267218747/500000000 : ℝ)|=(267218747/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092217719/5000000000 : ℝ)|^527 ≤ (1340904686053/10000000000000 : ℝ)^399
        have hw : |(-1092217719/5000000000 : ℝ)|=(1092217719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633494381/5000000000 : ℝ)|^527 ≤ (21439223564513/50000000000000 : ℝ)^399
        have hw : |(2633494381/5000000000 : ℝ)|=(2633494381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s6_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344374953/10000000000 : ℝ)*x 0 + (5266988757/10000000000 : ℝ)*x 1 + (-1092217713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344374953/10000000000 : ℝ)^527 ≤ (8742501227839/20000000000000 : ℝ)^399 := by
    have hnat : (5344374953 : ℕ)^527*20000000000000^399 ≤ 8742501227839^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344374953 10000000000 8742501227839 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266988757/10000000000 : ℝ)^527 ≤ (42878447075263/100000000000000 : ℝ)^399 := by
    have hnat : (5266988757 : ℕ)^527*100000000000000^399 ≤ 42878447075263^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266988757 10000000000 42878447075263 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092217713/5000000000 : ℝ)^527 ≤ (6704523381619/50000000000000 : ℝ)^399 := by
    have hnat : (1092217713 : ℕ)^527*50000000000000^399 ≤ 6704523381619^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092217713 5000000000 6704523381619 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344374953/10000000000 : ℝ), (5266988757/10000000000 : ℝ), (-1092217713/5000000000 : ℝ)] ![(8742501227839/20000000000000 : ℝ), (42878447075263/100000000000000 : ℝ), (6704523381619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344374953/10000000000 : ℝ)|^527 ≤ (8742501227839/20000000000000 : ℝ)^399
        have hw : |(5344374953/10000000000 : ℝ)|=(5344374953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266988757/10000000000 : ℝ)|^527 ≤ (42878447075263/100000000000000 : ℝ)^399
        have hw : |(5266988757/10000000000 : ℝ)|=(5266988757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1092217713/5000000000 : ℝ)|^527 ≤ (6704523381619/50000000000000 : ℝ)^399
        have hw : |(-1092217713/5000000000 : ℝ)|=(1092217713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s6_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1087793769/2500000000 : ℝ)*x 0 + (2113393979/5000000000 : ℝ)*x 1 + (4479121439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087793769/2500000000 : ℝ)^527 ≤ (33317378096811/100000000000000 : ℝ)^399 := by
    have hnat : (1087793769 : ℕ)^527*100000000000000^399 ≤ 33317378096811^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087793769 2500000000 33317378096811 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113393979/5000000000 : ℝ)^527 ≤ (32065193691731/100000000000000 : ℝ)^399 := by
    have hnat : (2113393979 : ℕ)^527*100000000000000^399 ≤ 32065193691731^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113393979 5000000000 32065193691731 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479121439/10000000000 : ℝ)^527 ≤ (6923485640559/20000000000000 : ℝ)^399 := by
    have hnat : (4479121439 : ℕ)^527*20000000000000^399 ≤ 6923485640559^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479121439 10000000000 6923485640559 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087793769/2500000000 : ℝ), (2113393979/5000000000 : ℝ), (4479121439/10000000000 : ℝ)] ![(33317378096811/100000000000000 : ℝ), (32065193691731/100000000000000 : ℝ), (6923485640559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087793769/2500000000 : ℝ)|^527 ≤ (33317378096811/100000000000000 : ℝ)^399
        have hw : |(1087793769/2500000000 : ℝ)|=(1087793769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113393979/5000000000 : ℝ)|^527 ≤ (32065193691731/100000000000000 : ℝ)^399
        have hw : |(2113393979/5000000000 : ℝ)|=(2113393979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479121439/10000000000 : ℝ)|^527 ≤ (6923485640559/20000000000000 : ℝ)^399
        have hw : |(4479121439/10000000000 : ℝ)|=(4479121439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s6_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060665833/5000000000 : ℝ)*x 0 + (5267302829/10000000000 : ℝ)*x 1 + (5391135237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060665833/5000000000 : ℝ)^527 ≤ (12899808274599/100000000000000 : ℝ)^399 := by
    have hnat : (1060665833 : ℕ)^527*100000000000000^399 ≤ 12899808274599^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060665833 5000000000 12899808274599 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267302829/10000000000 : ℝ)^527 ≤ (21440912102521/50000000000000 : ℝ)^399 := by
    have hnat : (5267302829 : ℕ)^527*50000000000000^399 ≤ 21440912102521^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267302829 10000000000 21440912102521 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391135237/10000000000 : ℝ)^527 ≤ (44218367507727/100000000000000 : ℝ)^399 := by
    have hnat : (5391135237 : ℕ)^527*100000000000000^399 ≤ 44218367507727^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391135237 10000000000 44218367507727 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060665833/5000000000 : ℝ), (5267302829/10000000000 : ℝ), (5391135237/10000000000 : ℝ)] ![(12899808274599/100000000000000 : ℝ), (21440912102521/50000000000000 : ℝ), (44218367507727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060665833/5000000000 : ℝ)|^527 ≤ (12899808274599/100000000000000 : ℝ)^399
        have hw : |(-1060665833/5000000000 : ℝ)|=(1060665833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267302829/10000000000 : ℝ)|^527 ≤ (21440912102521/50000000000000 : ℝ)^399
        have hw : |(5267302829/10000000000 : ℝ)|=(5267302829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391135237/10000000000 : ℝ)|^527 ≤ (44218367507727/100000000000000 : ℝ)^399
        have hw : |(5391135237/10000000000 : ℝ)|=(5391135237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s6_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656312307/5000000000 : ℝ)*x 0 + (-515072573/2500000000 : ℝ)*x 1 + (673891733/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656312307/5000000000 : ℝ)^527 ≤ (21684916419659/50000000000000 : ℝ)^399 := by
    have hnat : (2656312307 : ℕ)^527*50000000000000^399 ≤ 21684916419659^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656312307 5000000000 21684916419659 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515072573/2500000000 : ℝ)^527 ≤ (387869203343/3125000000000 : ℝ)^399 := by
    have hnat : (515072573 : ℕ)^527*3125000000000^399 ≤ 387869203343^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515072573 2500000000 387869203343 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673891733/1250000000 : ℝ)^527 ≤ (22109176316813/50000000000000 : ℝ)^399 := by
    have hnat : (673891733 : ℕ)^527*50000000000000^399 ≤ 22109176316813^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673891733 1250000000 22109176316813 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656312307/5000000000 : ℝ), (-515072573/2500000000 : ℝ), (673891733/1250000000 : ℝ)] ![(21684916419659/50000000000000 : ℝ), (387869203343/3125000000000 : ℝ), (22109176316813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656312307/5000000000 : ℝ)|^527 ≤ (21684916419659/50000000000000 : ℝ)^399
        have hw : |(2656312307/5000000000 : ℝ)|=(2656312307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515072573/2500000000 : ℝ)|^527 ≤ (387869203343/3125000000000 : ℝ)^399
        have hw : |(-515072573/2500000000 : ℝ)|=(515072573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673891733/1250000000 : ℝ)|^527 ≤ (22109176316813/50000000000000 : ℝ)^399
        have hw : |(673891733/1250000000 : ℝ)|=(673891733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s6_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (265631199/500000000 : ℝ)*x 0 + (1078226951/2000000000 : ℝ)*x 1 + (-2060289939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265631199/500000000 : ℝ)^527 ≤ (21684913001631/50000000000000 : ℝ)^399 := by
    have hnat : (265631199 : ℕ)^527*50000000000000^399 ≤ 21684913001631^399*500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265631199 500000000 21684913001631 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078226951/2000000000 : ℝ)^527 ≤ (44218362286083/100000000000000 : ℝ)^399 := by
    have hnat : (1078226951 : ℕ)^527*100000000000000^399 ≤ 44218362286083^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078226951 2000000000 44218362286083 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060289939/10000000000 : ℝ)^527 ≤ (6205905849093/50000000000000 : ℝ)^399 := by
    have hnat : (2060289939 : ℕ)^527*50000000000000^399 ≤ 6205905849093^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060289939 10000000000 6205905849093 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265631199/500000000 : ℝ), (1078226951/2000000000 : ℝ), (-2060289939/10000000000 : ℝ)] ![(21684913001631/50000000000000 : ℝ), (44218362286083/100000000000000 : ℝ), (6205905849093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265631199/500000000 : ℝ)|^527 ≤ (21684913001631/50000000000000 : ℝ)^399
        have hw : |(265631199/500000000 : ℝ)|=(265631199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078226951/2000000000 : ℝ)|^527 ≤ (44218362286083/100000000000000 : ℝ)^399
        have hw : |(1078226951/2000000000 : ℝ)|=(1078226951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060289939/10000000000 : ℝ)|^527 ≤ (6205905849093/50000000000000 : ℝ)^399
        have hw : |(-2060289939/10000000000 : ℝ)|=(2060289939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s6_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (87023713/200000000 : ℝ)*x 0 + (895696671/2000000000 : ℝ)*x 1 + (4227427319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87023713/200000000 : ℝ)^527 ≤ (266539880297/800000000000 : ℝ)^399 := by
    have hnat : (87023713 : ℕ)^527*800000000000^399 ≤ 266539880297^399*200000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87023713 200000000 266539880297 800000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895696671/2000000000 : ℝ)^527 ≤ (2163182175303/6250000000000 : ℝ)^399 := by
    have hnat : (895696671 : ℕ)^527*6250000000000^399 ≤ 2163182175303^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895696671 2000000000 2163182175303 6250000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227427319/10000000000 : ℝ)^527 ≤ (16035800073543/50000000000000 : ℝ)^399 := by
    have hnat : (4227427319 : ℕ)^527*50000000000000^399 ≤ 16035800073543^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227427319 10000000000 16035800073543 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87023713/200000000 : ℝ), (895696671/2000000000 : ℝ), (4227427319/10000000000 : ℝ)] ![(266539880297/800000000000 : ℝ), (2163182175303/6250000000000 : ℝ), (16035800073543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87023713/200000000 : ℝ)|^527 ≤ (266539880297/800000000000 : ℝ)^399
        have hw : |(87023713/200000000 : ℝ)|=(87023713/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895696671/2000000000 : ℝ)|^527 ≤ (2163182175303/6250000000000 : ℝ)^399
        have hw : |(895696671/2000000000 : ℝ)|=(895696671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227427319/10000000000 : ℝ)|^527 ≤ (16035800073543/50000000000000 : ℝ)^399
        have hw : |(4227427319/10000000000 : ℝ)|=(4227427319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11471/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14107/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14129/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (229/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14129/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (229/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14129/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (229/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14129/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (229/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14129/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (229/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14129/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (229/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (229/2000 : ℝ) ^ (8431/2048 : ℝ) ≤ (13347049843434089/100000000000000000000 : ℝ) := by
    have hpowers : (229/2000 : ℝ)^8431 ≤ (13347049843434089/100000000000000000000 : ℝ)^2048 := by
      have hnat : (229 : ℕ)^8431*100000000000000000000^2048 ≤ 13347049843434089^2048*2000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        229 2000 13347049843434089 100000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (229/2000 : ℝ)) (X := (13347049843434089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14129/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (7928743647969327/25000000000000000000 : ℝ) := by
    have hpowers : (14129/100000 : ℝ)^8431 ≤ (7928743647969327/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14129 : ℕ)^8431*25000000000000000000^2048 ≤ 7928743647969327^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14129 100000 7928743647969327 25000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14129/100000 : ℝ)) (X := (7928743647969327/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013347049843434089/50000000000000000000 : ℝ) ≤ (2500162092256953/2500000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (50013347049843434089/50000000000000000000 : ℝ)^2048 ≤ (2500162092256953/2500000000000000 : ℝ)^8431 := by
      have hnat : (50013347049843434089 : ℕ)^2048*2500000000000000^8431 ≤ 2500162092256953^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013347049843434089 50000000000000000000 2500162092256953 2500000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500162092256953/2500000000000000 : ℝ)) (X := (50013347049843434089/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045062024435311397/100000000000000000000 : ℝ) ≤ (10001094428750279/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (100045062024435311397/100000000000000000000 : ℝ)^2048 ≤ (10001094428750279/10000000000000000 : ℝ)^8431 := by
      have hnat : (100045062024435311397 : ℕ)^2048*10000000000000000^8431 ≤ 10001094428750279^8431*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045062024435311397 100000000000000000000 10001094428750279 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001094428750279/10000000000000000 : ℝ)) (X := (100045062024435311397/100000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507928743647969327/12500000000000000000 : ℝ) ≤ (5000770244236373/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (12507928743647969327/12500000000000000000 : ℝ)^2048 ≤ (5000770244236373/5000000000000000 : ℝ)^8431 := by
      have hnat : (12507928743647969327 : ℕ)^2048*5000000000000000^8431 ≤ 5000770244236373^8431*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507928743647969327 12500000000000000000 5000770244236373 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000770244236373/5000000000000000 : ℝ)) (X := (12507928743647969327/12500000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13347049843434089/100000000000000000000 : ℝ) ≤ ((836922569155656689/837187500000000000 : ℝ)+2*(446059722467/267900000000000 : ℝ)*(229/2000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (836922569155656689/837187500000000000 : ℝ)+2*(446059722467/267900000000000 : ℝ)*(229/2000 : ℝ)=(2500162092256953/2500000000000000 : ℝ) by norm_num, show 1+2*(13347049843434089/100000000000000000000 : ℝ)=(50013347049843434089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7928743647969327/25000000000000000000 : ℝ)+(13347049843434089/100000000000000000000 : ℝ) ≤ ((836922569155656689/837187500000000000 : ℝ)+(446059722467/267900000000000 : ℝ)*((14129/100000 : ℝ)+(229/2000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (836922569155656689/837187500000000000 : ℝ)+(446059722467/267900000000000 : ℝ)*((14129/100000 : ℝ)+(229/2000 : ℝ))=(10001094428750279/10000000000000000 : ℝ) by norm_num, show 1+(7928743647969327/25000000000000000000 : ℝ)+(13347049843434089/100000000000000000000 : ℝ)=(100045062024435311397/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7928743647969327/25000000000000000000 : ℝ) ≤ ((836922569155656689/837187500000000000 : ℝ)+2*(446059722467/267900000000000 : ℝ)*(14129/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (836922569155656689/837187500000000000 : ℝ)+2*(446059722467/267900000000000 : ℝ)*(14129/100000 : ℝ)=(5000770244236373/5000000000000000 : ℝ) by norm_num, show 1+2*(7928743647969327/25000000000000000000 : ℝ)=(12507928743647969327/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (836922569155656689/837187500000000000 : ℝ)*(X 1 0+X 2 0)+(446059722467/267900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (836922569155656689/837187500000000000 : ℝ)) (alpha := (446059722467/267900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (836922569155656689/837187500000000000 : ℝ)*(X 0 1+X 2 1)+(446059722467/267900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (836922569155656689/837187500000000000 : ℝ)) (alpha := (446059722467/267900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (836922569155656689/837187500000000000 : ℝ)*(X 0 2+X 1 2)+(446059722467/267900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (836922569155656689/837187500000000000 : ℝ)) (alpha := (446059722467/267900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66291459/312500000 : ℝ)*X 0 0+(5391450653/10000000000 : ℝ)*X 0 1+(1053397753/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267218747/500000000 : ℝ)*X 1 0+(-1092217719/5000000000 : ℝ)*X 1 1+(2633494381/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344374953/10000000000 : ℝ)*X 2 0+(5266988757/10000000000 : ℝ)*X 2 1+(-1092217713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087793769/2500000000 : ℝ)*X 0 0+(2113393979/5000000000 : ℝ)*X 0 1+(4479121439/10000000000 : ℝ)*X 0 2+(1087793769/2500000000 : ℝ)*X 1 0+(2113393979/5000000000 : ℝ)*X 1 1+(4479121439/10000000000 : ℝ)*X 1 2+(1087793769/2500000000 : ℝ)*X 2 0+(2113393979/5000000000 : ℝ)*X 2 1+(4479121439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1060665833/5000000000 : ℝ)*X 0 0+(5267302829/10000000000 : ℝ)*X 0 1+(5391135237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656312307/5000000000 : ℝ)*X 1 0+(-515072573/2500000000 : ℝ)*X 1 1+(673891733/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265631199/500000000 : ℝ)*X 2 0+(1078226951/2000000000 : ℝ)*X 2 1+(-2060289939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((87023713/200000000 : ℝ)*X 0 0+(895696671/2000000000 : ℝ)*X 0 1+(4227427319/10000000000 : ℝ)*X 0 2+(87023713/200000000 : ℝ)*X 1 0+(895696671/2000000000 : ℝ)*X 1 1+(4227427319/10000000000 : ℝ)*X 1 2+(87023713/200000000 : ℝ)*X 2 0+(895696671/2000000000 : ℝ)*X 2 1+(4227427319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10650508339047957929822729/3488281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (615155213/100000000000000 : ℝ)*(base19) + (584129563/100000000000000 : ℝ)*(base23) + (13513139/50000000000000 : ℝ)*(lower2) + (18278979/25000000000000 : ℝ)*(upper3) + (58276117/100000000000000 : ℝ)*(upper5) + (2999412293178449/50000000000000 : ℝ)*(major0) + (2999412293178449/50000000000000 : ℝ)*(major1) + (2999412293178449/50000000000000 : ℝ)*(major2) + (4017302518336919/50000000000000 : ℝ)*(sp0) + (2008655447576173/25000000000000 : ℝ)*(sp1) + (4017310910665171/50000000000000 : ℝ)*(sp2) + (39630177442843/1000000000000 : ℝ)*(sp3) + (8684393033/50000000000000 : ℝ)*(sp4) + (1784239081/20000000000000 : ℝ)*(sp7) + (1981513332739853/50000000000000 : ℝ)*(f.failure) + (1606924481091981/20000000000000 : ℝ)*(f.sum) + (4744606777529/3348750000000000000000000000 : ℝ)*base65 + (138895022662086963/13953125000000000000000000000000 : ℝ)*base68 + (22818620038211963/13953125000000000000000000000000 : ℝ)*base70 + (68481420864723169/6976562500000000000000000000000 : ℝ)*base72 + (47019776390839/13395000000000000000000000000 : ℝ)*base74 + (40640020001586963/13953125000000000000000000000000 : ℝ)*base76 + (2163871488520821/109008789062500000000000000000 : ℝ)*base78 + (132284980375180713/13953125000000000000000000000000 : ℝ)*base80 + (46465092313181/13395000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (7180183/312500000000000000000 : ℝ)*base89 + (7180183/312500000000000000000 : ℝ)*base91 + (7180183/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10876134207314143073279073/6976562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (335902053/20000000000000 : ℝ)*(base19) + (323641153/100000000000000 : ℝ)*(base23) + (208333439/100000000000000 : ℝ)*(lower2) + (289951239/100000000000000 : ℝ)*(upper3) + (434587287/100000000000000 : ℝ)*(upper5) + (1507342769296691/25000000000000 : ℝ)*(major0) + (1507342769296691/25000000000000 : ℝ)*(major1) + (1507342769296691/25000000000000 : ℝ)*(major2) + (50316246467/100000000000000 : ℝ)*(sp0) + (2353247281/12500000000000 : ℝ)*(sp3) + (8075485074416027/100000000000000 : ℝ)*(sp4) + (2018883427788057/25000000000000 : ℝ)*(sp5) + (403776753351067/5000000000000 : ℝ)*(sp6) + (497898485720959/12500000000000 : ℝ)*(sp7) + (6223760487103/156250000000 : ℝ)*(f.failure) + (8075535390662493/100000000000000 : ℝ)*(f.sum) + (25825341687181/6697500000000000000000000000 : ℝ)*base66 + (65645791021040467/6976562500000000000000000000000 : ℝ)*base68 + (34849195938915467/6976562500000000000000000000000 : ℝ)*base70 + (27114058270232773/1744140625000000000000000000000 : ℝ)*base72 + (1167382962893/3348750000000000000000000000 : ℝ)*base74 + (5752243873039463/436035156250000000000000000000 : ℝ)*base75 + (590162217352489/54504394531250000000000000000 : ℝ)*base78 + (54926429642456329/3488281250000000000000000000000 : ℝ)*base79 + (975209585791/418593750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (15491/1953125000000000000 : ℝ)*base89 + (15491/1953125000000000000 : ℝ)*base91 + (15491/1953125000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1239_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1239_s7_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121343943/10000000000 : ℝ)*x 0 + (5391248441/10000000000 : ℝ)*x 1 + (5267179607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121343943/10000000000 : ℝ)^527 ≤ (12899906880989/100000000000000 : ℝ)^399 := by
    have hnat : (2121343943 : ℕ)^527*100000000000000^399 ≤ 12899906880989^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121343943 10000000000 12899906880989 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391248441/10000000000 : ℝ)^527 ≤ (86366394303/195312500000 : ℝ)^399 := by
    have hnat : (5391248441 : ℕ)^527*195312500000^399 ≤ 86366394303^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391248441 10000000000 86366394303 195312500000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267179607/10000000000 : ℝ)^527 ≤ (42880499225087/100000000000000 : ℝ)^399 := by
    have hnat : (5267179607 : ℕ)^527*100000000000000^399 ≤ 42880499225087^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267179607 10000000000 42880499225087 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121343943/10000000000 : ℝ), (5391248441/10000000000 : ℝ), (5267179607/10000000000 : ℝ)] ![(12899906880989/100000000000000 : ℝ), (86366394303/195312500000 : ℝ), (42880499225087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121343943/10000000000 : ℝ)|^527 ≤ (12899906880989/100000000000000 : ℝ)^399
        have hw : |(-2121343943/10000000000 : ℝ)|=(2121343943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391248441/10000000000 : ℝ)|^527 ≤ (86366394303/195312500000 : ℝ)^399
        have hw : |(5391248441/10000000000 : ℝ)|=(5391248441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267179607/10000000000 : ℝ)|^527 ≤ (42880499225087/100000000000000 : ℝ)^399
        have hw : |(5267179607/10000000000 : ℝ)|=(5267179607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s7_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668040447/1250000000 : ℝ)*x 0 + (-1092124957/5000000000 : ℝ)*x 1 + (1316795063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668040447/1250000000 : ℝ)^527 ≤ (21855975555799/50000000000000 : ℝ)^399 := by
    have hnat : (668040447 : ℕ)^527*50000000000000^399 ≤ 21855975555799^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668040447 1250000000 21855975555799 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092124957/5000000000 : ℝ)^527 ≤ (13407542712437/100000000000000 : ℝ)^399 := by
    have hnat : (1092124957 : ℕ)^527*100000000000000^399 ≤ 13407542712437^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092124957 5000000000 13407542712437 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316795063/2500000000 : ℝ)^527 ≤ (42880506160609/100000000000000 : ℝ)^399 := by
    have hnat : (1316795063 : ℕ)^527*100000000000000^399 ≤ 42880506160609^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316795063 2500000000 42880506160609 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668040447/1250000000 : ℝ), (-1092124957/5000000000 : ℝ), (1316795063/2500000000 : ℝ)] ![(21855975555799/50000000000000 : ℝ), (13407542712437/100000000000000 : ℝ), (42880506160609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668040447/1250000000 : ℝ)|^527 ≤ (21855975555799/50000000000000 : ℝ)^399
        have hw : |(668040447/1250000000 : ℝ)|=(668040447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092124957/5000000000 : ℝ)|^527 ≤ (13407542712437/100000000000000 : ℝ)^399
        have hw : |(-1092124957/5000000000 : ℝ)|=(1092124957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316795063/2500000000 : ℝ)|^527 ≤ (42880506160609/100000000000000 : ℝ)^399
        have hw : |(1316795063/2500000000 : ℝ)|=(1316795063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s7_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344323593/10000000000 : ℝ)*x 0 + (526718029/1000000000 : ℝ)*x 1 + (-2184249841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344323593/10000000000 : ℝ)^527 ≤ (174847805181/400000000000 : ℝ)^399 := by
    have hnat : (5344323593 : ℕ)^527*400000000000^399 ≤ 174847805181^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344323593 10000000000 174847805181 400000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526718029/1000000000 : ℝ)^527 ≤ (21440253284607/50000000000000 : ℝ)^399 := by
    have hnat : (526718029 : ℕ)^527*50000000000000^399 ≤ 21440253284607^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526718029 1000000000 21440253284607 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184249841/10000000000 : ℝ)^527 ≤ (13407542120593/100000000000000 : ℝ)^399 := by
    have hnat : (2184249841 : ℕ)^527*100000000000000^399 ≤ 13407542120593^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184249841 10000000000 13407542120593 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344323593/10000000000 : ℝ), (526718029/1000000000 : ℝ), (-2184249841/10000000000 : ℝ)] ![(174847805181/400000000000 : ℝ), (21440253284607/50000000000000 : ℝ), (13407542120593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344323593/10000000000 : ℝ)|^527 ≤ (174847805181/400000000000 : ℝ)^399
        have hw : |(5344323593/10000000000 : ℝ)|=(5344323593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526718029/1000000000 : ℝ)|^527 ≤ (21440253284607/50000000000000 : ℝ)^399
        have hw : |(526718029/1000000000 : ℝ)|=(526718029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2184249841/10000000000 : ℝ)|^527 ≤ (13407542120593/100000000000000 : ℝ)^399
        have hw : |(-2184249841/10000000000 : ℝ)|=(2184249841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s7_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (17404743/40000000 : ℝ)*x 0 + (4227185489/10000000000 : ℝ)*x 1 + (4478720647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17404743/40000000 : ℝ)^527 ≤ (33317486048477/100000000000000 : ℝ)^399 := by
    have hnat : (17404743 : ℕ)^527*100000000000000^399 ≤ 33317486048477^399*40000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17404743 40000000 33317486048477 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227185489/10000000000 : ℝ)^527 ≤ (6413835390389/20000000000000 : ℝ)^399 := by
    have hnat : (4227185489 : ℕ)^527*20000000000000^399 ≤ 6413835390389^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227185489 10000000000 6413835390389 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478720647/10000000000 : ℝ)^527 ≤ (8653334246501/25000000000000 : ℝ)^399 := by
    have hnat : (4478720647 : ℕ)^527*25000000000000^399 ≤ 8653334246501^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478720647 10000000000 8653334246501 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17404743/40000000 : ℝ), (4227185489/10000000000 : ℝ), (4478720647/10000000000 : ℝ)] ![(33317486048477/100000000000000 : ℝ), (6413835390389/20000000000000 : ℝ), (8653334246501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17404743/40000000 : ℝ)|^527 ≤ (33317486048477/100000000000000 : ℝ)^399
        have hw : |(17404743/40000000 : ℝ)|=(17404743/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227185489/10000000000 : ℝ)|^527 ≤ (6413835390389/20000000000000 : ℝ)^399
        have hw : |(4227185489/10000000000 : ℝ)|=(4227185489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478720647/10000000000 : ℝ)|^527 ≤ (8653334246501/25000000000000 : ℝ)^399
        have hw : |(4478720647/10000000000 : ℝ)|=(4478720647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s7_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-66292147/312500000 : ℝ)*x 0 + (5267492843/10000000000 : ℝ)*x 1 + (5390933999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66292147/312500000 : ℝ)^527 ≤ (12899945120431/100000000000000 : ℝ)^399 := by
    have hnat : (66292147 : ℕ)^527*100000000000000^399 ≤ 12899945120431^399*312500000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66292147 312500000 12899945120431 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267492843/10000000000 : ℝ)^527 ≤ (42883867404653/100000000000000 : ℝ)^399 := by
    have hnat : (5267492843 : ℕ)^527*100000000000000^399 ≤ 42883867404653^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267492843 10000000000 42883867404653 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390933999/10000000000 : ℝ)^527 ≤ (1768647498081/4000000000000 : ℝ)^399 := by
    have hnat : (5390933999 : ℕ)^527*4000000000000^399 ≤ 1768647498081^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390933999 10000000000 1768647498081 4000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66292147/312500000 : ℝ), (5267492843/10000000000 : ℝ), (5390933999/10000000000 : ℝ)] ![(12899945120431/100000000000000 : ℝ), (42883867404653/100000000000000 : ℝ), (1768647498081/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66292147/312500000 : ℝ)|^527 ≤ (12899945120431/100000000000000 : ℝ)^399
        have hw : |(-66292147/312500000 : ℝ)|=(66292147/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267492843/10000000000 : ℝ)|^527 ≤ (42883867404653/100000000000000 : ℝ)^399
        have hw : |(5267492843/10000000000 : ℝ)|=(5267492843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390933999/10000000000 : ℝ)|^527 ≤ (1768647498081/4000000000000 : ℝ)^399
        have hw : |(5390933999/10000000000 : ℝ)|=(5390933999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s7_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312673413/10000000000 : ℝ)*x 0 + (-1030248181/5000000000 : ℝ)*x 1 + (1078186787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312673413/10000000000 : ℝ)^527 ≤ (135532371911/312500000000 : ℝ)^399 := by
    have hnat : (5312673413 : ℕ)^527*312500000000^399 ≤ 135532371911^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312673413 10000000000 135532371911 312500000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030248181/5000000000 : ℝ)^527 ≤ (12413454214231/100000000000000 : ℝ)^399 := by
    have hnat : (1030248181 : ℕ)^527*100000000000000^399 ≤ 12413454214231^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030248181 5000000000 12413454214231 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078186787/2000000000 : ℝ)^527 ≤ (44216186758703/100000000000000 : ℝ)^399 := by
    have hnat : (1078186787 : ℕ)^527*100000000000000^399 ≤ 44216186758703^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078186787 2000000000 44216186758703 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312673413/10000000000 : ℝ), (-1030248181/5000000000 : ℝ), (1078186787/2000000000 : ℝ)] ![(135532371911/312500000000 : ℝ), (12413454214231/100000000000000 : ℝ), (44216186758703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312673413/10000000000 : ℝ)|^527 ≤ (135532371911/312500000000 : ℝ)^399
        have hw : |(5312673413/10000000000 : ℝ)|=(5312673413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030248181/5000000000 : ℝ)|^527 ≤ (12413454214231/100000000000000 : ℝ)^399
        have hw : |(-1030248181/5000000000 : ℝ)|=(1030248181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078186787/2000000000 : ℝ)|^527 ≤ (44216186758703/100000000000000 : ℝ)^399
        have hw : |(1078186787/2000000000 : ℝ)|=(1078186787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s7_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (664084167/1250000000 : ℝ)*x 0 + (16846669/31250000 : ℝ)*x 1 + (-206049627/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664084167/1250000000 : ℝ)^527 ≤ (43370358181271/100000000000000 : ℝ)^399 := by
    have hnat : (664084167 : ℕ)^527*100000000000000^399 ≤ 43370358181271^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664084167 1250000000 43370358181271 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16846669/31250000 : ℝ)^527 ≤ (44216188329511/100000000000000 : ℝ)^399 := by
    have hnat : (16846669 : ℕ)^527*100000000000000^399 ≤ 44216188329511^399*31250000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16846669 31250000 44216188329511 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206049627/1000000000 : ℝ)^527 ≤ (3103363370543/25000000000000 : ℝ)^399 := by
    have hnat : (206049627 : ℕ)^527*25000000000000^399 ≤ 3103363370543^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206049627 1000000000 3103363370543 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664084167/1250000000 : ℝ), (16846669/31250000 : ℝ), (-206049627/1000000000 : ℝ)] ![(43370358181271/100000000000000 : ℝ), (44216188329511/100000000000000 : ℝ), (3103363370543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664084167/1250000000 : ℝ)|^527 ≤ (43370358181271/100000000000000 : ℝ)^399
        have hw : |(664084167/1250000000 : ℝ)|=(664084167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16846669/31250000 : ℝ)|^527 ≤ (44216188329511/100000000000000 : ℝ)^399
        have hw : |(16846669/31250000 : ℝ)|=(16846669/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206049627/1000000000 : ℝ)|^527 ≤ (3103363370543/25000000000000 : ℝ)^399
        have hw : |(-206049627/1000000000 : ℝ)|=(206049627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s7_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4351194461/10000000000 : ℝ)*x 0 + (4478086543/10000000000 : ℝ)*x 1 + (4227822639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351194461/10000000000 : ℝ)^527 ≤ (16658787073687/50000000000000 : ℝ)^399 := by
    have hnat : (4351194461 : ℕ)^527*50000000000000^399 ≤ 16658787073687^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351194461 10000000000 16658787073687 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478086543/10000000000 : ℝ)^527 ≤ (1081464512493/3125000000000 : ℝ)^399 := by
    have hnat : (4478086543 : ℕ)^527*3125000000000^399 ≤ 1081464512493^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478086543 10000000000 1081464512493 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227822639/10000000000 : ℝ)^527 ≤ (16037780722473/50000000000000 : ℝ)^399 := by
    have hnat : (4227822639 : ℕ)^527*50000000000000^399 ≤ 16037780722473^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227822639 10000000000 16037780722473 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351194461/10000000000 : ℝ), (4478086543/10000000000 : ℝ), (4227822639/10000000000 : ℝ)] ![(16658787073687/50000000000000 : ℝ), (1081464512493/3125000000000 : ℝ), (16037780722473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351194461/10000000000 : ℝ)|^527 ≤ (16658787073687/50000000000000 : ℝ)^399
        have hw : |(4351194461/10000000000 : ℝ)|=(4351194461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478086543/10000000000 : ℝ)|^527 ≤ (1081464512493/3125000000000 : ℝ)^399
        have hw : |(4478086543/10000000000 : ℝ)|=(4478086543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227822639/10000000000 : ℝ)|^527 ≤ (16037780722473/50000000000000 : ℝ)^399
        have hw : |(4227822639/10000000000 : ℝ)|=(4227822639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (459/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14103/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11471/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (6724056088278563/50000000000000000000 : ℝ) := by
    have hpowers : (11471/100000 : ℝ)^8431 ≤ (6724056088278563/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11471 : ℕ)^8431*50000000000000000000^2048 ≤ 6724056088278563^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11471 100000 6724056088278563 50000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11471/100000 : ℝ)) (X := (6724056088278563/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14107/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (31512173245248933/100000000000000000000 : ℝ) := by
    have hpowers : (14107/100000 : ℝ)^8431 ≤ (31512173245248933/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14107 : ℕ)^8431*100000000000000000000^2048 ≤ 31512173245248933^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14107 100000 31512173245248933 100000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14107/100000 : ℝ)) (X := (31512173245248933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006724056088278563/25000000000000000000 : ℝ) ≤ (5000326638952057/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (25006724056088278563/25000000000000000000 : ℝ)^2048 ≤ (5000326638952057/5000000000000000 : ℝ)^8431 := by
      have hnat : (25006724056088278563 : ℕ)^2048*5000000000000000^8431 ≤ 5000326638952057^8431*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006724056088278563 25000000000000000000 5000326638952057 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000326638952057/5000000000000000 : ℝ)) (X := (25006724056088278563/25000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044960285421806059/100000000000000000000 : ℝ) ≤ (10001091958218627/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (100044960285421806059/100000000000000000000 : ℝ)^2048 ≤ (10001091958218627/10000000000000000 : ℝ)^8431 := by
      have hnat : (100044960285421806059 : ℕ)^2048*10000000000000000^8431 ≤ 10001091958218627^8431*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044960285421806059 100000000000000000000 10001091958218627 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001091958218627/10000000000000000 : ℝ)) (X := (100044960285421806059/100000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031512173245248933/50000000000000000000 : ℝ) ≤ (500076531926657/500000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (50031512173245248933/50000000000000000000 : ℝ)^2048 ≤ (500076531926657/500000000000000 : ℝ)^8431 := by
      have hnat : (50031512173245248933 : ℕ)^2048*500000000000000^8431 ≤ 500076531926657^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031512173245248933 50000000000000000000 500076531926657 500000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500076531926657/500000000000000 : ℝ)) (X := (50031512173245248933/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6724056088278563/50000000000000000000 : ℝ) ≤ ((13175828918389843629/13180000000000000000 : ℝ)+2*(438680314513/263600000000000 : ℝ)*(11471/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (13175828918389843629/13180000000000000000 : ℝ)+2*(438680314513/263600000000000 : ℝ)*(11471/100000 : ℝ)=(5000326638952057/5000000000000000 : ℝ) by norm_num, show 1+2*(6724056088278563/50000000000000000000 : ℝ)=(25006724056088278563/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31512173245248933/100000000000000000000 : ℝ)+(6724056088278563/50000000000000000000 : ℝ) ≤ ((13175828918389843629/13180000000000000000 : ℝ)+(438680314513/263600000000000 : ℝ)*((14107/100000 : ℝ)+(11471/100000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (13175828918389843629/13180000000000000000 : ℝ)+(438680314513/263600000000000 : ℝ)*((14107/100000 : ℝ)+(11471/100000 : ℝ))=(10001091958218627/10000000000000000 : ℝ) by norm_num, show 1+(31512173245248933/100000000000000000000 : ℝ)+(6724056088278563/50000000000000000000 : ℝ)=(100044960285421806059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31512173245248933/100000000000000000000 : ℝ) ≤ ((13175828918389843629/13180000000000000000 : ℝ)+2*(438680314513/263600000000000 : ℝ)*(14107/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (13175828918389843629/13180000000000000000 : ℝ)+2*(438680314513/263600000000000 : ℝ)*(14107/100000 : ℝ)=(500076531926657/500000000000000 : ℝ) by norm_num, show 1+2*(31512173245248933/100000000000000000000 : ℝ)=(50031512173245248933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13175828918389843629/13180000000000000000 : ℝ)*(X 1 0+X 2 0)+(438680314513/263600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (11471/100000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (13175828918389843629/13180000000000000000 : ℝ)) (alpha := (438680314513/263600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13175828918389843629/13180000000000000000 : ℝ)*(X 0 1+X 2 1)+(438680314513/263600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (11471/100000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (13175828918389843629/13180000000000000000 : ℝ)) (alpha := (438680314513/263600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13175828918389843629/13180000000000000000 : ℝ)*(X 0 2+X 1 2)+(438680314513/263600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (11471/100000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (13175828918389843629/13180000000000000000 : ℝ)) (alpha := (438680314513/263600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2121343943/10000000000 : ℝ)*X 0 0+(5391248441/10000000000 : ℝ)*X 0 1+(5267179607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668040447/1250000000 : ℝ)*X 1 0+(-1092124957/5000000000 : ℝ)*X 1 1+(1316795063/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344323593/10000000000 : ℝ)*X 2 0+(526718029/1000000000 : ℝ)*X 2 1+(-2184249841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17404743/40000000 : ℝ)*X 0 0+(4227185489/10000000000 : ℝ)*X 0 1+(4478720647/10000000000 : ℝ)*X 0 2+(17404743/40000000 : ℝ)*X 1 0+(4227185489/10000000000 : ℝ)*X 1 1+(4478720647/10000000000 : ℝ)*X 1 2+(17404743/40000000 : ℝ)*X 2 0+(4227185489/10000000000 : ℝ)*X 2 1+(4478720647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-66292147/312500000 : ℝ)*X 0 0+(5267492843/10000000000 : ℝ)*X 0 1+(5390933999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312673413/10000000000 : ℝ)*X 1 0+(-1030248181/5000000000 : ℝ)*X 1 1+(1078186787/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664084167/1250000000 : ℝ)*X 2 0+(16846669/31250000 : ℝ)*X 2 1+(-206049627/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351194461/10000000000 : ℝ)*X 0 0+(4478086543/10000000000 : ℝ)*X 0 1+(4227822639/10000000000 : ℝ)*X 0 2+(4351194461/10000000000 : ℝ)*X 1 0+(4478086543/10000000000 : ℝ)*X 1 1+(4227822639/10000000000 : ℝ)*X 1 2+(4351194461/10000000000 : ℝ)*X 2 0+(4478086543/10000000000 : ℝ)*X 2 1+(4227822639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24346121737041245229867/13180000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1463706091/100000000000000 : ℝ)*(base19) + (231920017/25000000000000 : ℝ)*(base23) + (172682489/50000000000000 : ℝ)*(lower2) + (28741811/10000000000000 : ℝ)*(upper3) + (9038599/20000000000000 : ℝ)*(lower4) + (6017918530793069/100000000000000 : ℝ)*(major0) + (6017918530793069/100000000000000 : ℝ)*(major1) + (6017918530793069/100000000000000 : ℝ)*(major2) + (8060121466430863/100000000000000 : ℝ)*(sp0) + (4030097382268273/50000000000000 : ℝ)*(sp1) + (8060195300562569/100000000000000 : ℝ)*(sp2) + (1987804720810931/50000000000000 : ℝ)*(sp3) + (37380905887/50000000000000 : ℝ)*(sp4) + (31330148237/100000000000000 : ℝ)*(sp7) + (3975640771770099/100000000000000 : ℝ)*(f.failure) + (8060196228242637/100000000000000 : ℝ)*(f.sum) + (485590785037/13180000000000000000000000000 : ℝ)*base65 + (6212048570654857401/1318000000000000000000000000000000 : ℝ)*base67 + (305110775445142599/1318000000000000000000000000000000 : ℝ)*base70 + (1383831867667142599/1318000000000000000000000000000000 : ℝ)*base72 + (31062530295697/13180000000000000000000000000 : ℝ)*base73 + (934633600604857401/1318000000000000000000000000000000 : ℝ)*base75 + (4254412039545142599/1318000000000000000000000000000000 : ℝ)*base78 + (11342499397144857401/1318000000000000000000000000000000 : ℝ)*base79 + (51548962633357/13180000000000000000000000000 : ℝ)*base81 + (6820489/625000000000000000000 : ℝ)*base89 + (6820489/625000000000000000000 : ℝ)*base91 + (6820489/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3936437481325377037307868039/659000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (491266789/50000000000000 : ℝ)*(base19) + (49265093/5000000000000 : ℝ)*(base23) + (43391007/50000000000000 : ℝ)*(upper3) + (2842533/6250000000000 : ℝ)*(lower4) + (69577929/50000000000000 : ℝ)*(upper5) + (6048403276256097/100000000000000 : ℝ)*(major0) + (6048403276256097/100000000000000 : ℝ)*(major1) + (6048403276256097/100000000000000 : ℝ)*(major2) + (25391376241/100000000000000 : ℝ)*(sp1) + (6238949967/20000000000000 : ℝ)*(sp2) + (8101026326444489/100000000000000 : ℝ)*(sp4) + (810099995253467/10000000000000 : ℝ)*(sp5) + (8100994146392793/100000000000000 : ℝ)*(sp6) + (99894500673901/2500000000000 : ℝ)*(sp7) + (99894500673901/2500000000000 : ℝ)*(f.failure) + (8101026326444489/100000000000000 : ℝ)*(f.sum) + (108626806949359/13180000000000000000000000000 : ℝ)*base66 + (1555120741970093987/1318000000000000000000000000000000 : ℝ)*base68 + (12648689632597906013/1318000000000000000000000000000000 : ℝ)*base69 + (10517150409012093987/1318000000000000000000000000000000 : ℝ)*base72 + (39384408005319/13180000000000000000000000000 : ℝ)*base74 + (14934332217780093987/1318000000000000000000000000000000 : ℝ)*base76 + (7544715194498093987/1318000000000000000000000000000000 : ℝ)*base78 + (9254396469595906013/1318000000000000000000000000000000 : ℝ)*base79 + (12174759422061/13180000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (57261/15625000000000000000 : ℝ)*base89 + (57261/15625000000000000000 : ℝ)*base91 + (57261/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1239_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1239_s8_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (334019641/625000000 : ℝ)*x 0 + (-1092107771/5000000000 : ℝ)*x 1 + (1316803883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334019641/625000000 : ℝ)^527 ≤ (43711850427483/100000000000000 : ℝ)^399 := by
    have hnat : (334019641 : ℕ)^527*100000000000000^399 ≤ 43711850427483^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334019641 625000000 43711850427483 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092107771/5000000000 : ℝ)^527 ≤ (536290561747/4000000000000 : ℝ)^399 := by
    have hnat : (1092107771 : ℕ)^527*4000000000000^399 ≤ 536290561747^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092107771 5000000000 536290561747 4000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316803883/2500000000 : ℝ)^527 ≤ (42880885517943/100000000000000 : ℝ)^399 := by
    have hnat : (1316803883 : ℕ)^527*100000000000000^399 ≤ 42880885517943^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316803883 2500000000 42880885517943 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334019641/625000000 : ℝ), (-1092107771/5000000000 : ℝ), (1316803883/2500000000 : ℝ)] ![(43711850427483/100000000000000 : ℝ), (536290561747/4000000000000 : ℝ), (42880885517943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334019641/625000000 : ℝ)|^527 ≤ (43711850427483/100000000000000 : ℝ)^399
        have hw : |(334019641/625000000 : ℝ)|=(334019641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092107771/5000000000 : ℝ)|^527 ≤ (536290561747/4000000000000 : ℝ)^399
        have hw : |(-1092107771/5000000000 : ℝ)|=(1092107771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316803883/2500000000 : ℝ)|^527 ≤ (42880885517943/100000000000000 : ℝ)^399
        have hw : |(1316803883/2500000000 : ℝ)|=(1316803883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s8_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121351467/10000000000 : ℝ)*x 0 + (658440989/1250000000 : ℝ)*x 1 + (2695448571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121351467/10000000000 : ℝ)^527 ≤ (12899967312331/100000000000000 : ℝ)^399 := by
    have hnat : (2121351467 : ℕ)^527*100000000000000^399 ≤ 12899967312331^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121351467 10000000000 12899967312331 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658440989/1250000000 : ℝ)^527 ≤ (10721061125083/25000000000000 : ℝ)^399 := by
    have hnat : (658440989 : ℕ)^527*25000000000000^399 ≤ 10721061125083^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658440989 1250000000 10721061125083 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695448571/5000000000 : ℝ)^527 ≤ (2763486760927/6250000000000 : ℝ)^399 := by
    have hnat : (2695448571 : ℕ)^527*6250000000000^399 ≤ 2763486760927^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695448571 5000000000 2763486760927 6250000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121351467/10000000000 : ℝ), (658440989/1250000000 : ℝ), (2695448571/5000000000 : ℝ)] ![(12899967312331/100000000000000 : ℝ), (10721061125083/25000000000000 : ℝ), (2763486760927/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121351467/10000000000 : ℝ)|^527 ≤ (12899967312331/100000000000000 : ℝ)^399
        have hw : |(-2121351467/10000000000 : ℝ)|=(2121351467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658440989/1250000000 : ℝ)|^527 ≤ (10721061125083/25000000000000 : ℝ)^399
        have hw : |(658440989/1250000000 : ℝ)|=(658440989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695448571/5000000000 : ℝ)|^527 ≤ (2763486760927/6250000000000 : ℝ)^399
        have hw : |(2695448571/5000000000 : ℝ)|=(2695448571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s8_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1328170687/2500000000 : ℝ)*x 0 + (-128783361/625000000 : ℝ)*x 1 + (5390897163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328170687/2500000000 : ℝ)^527 ≤ (43370459665757/100000000000000 : ℝ)^399 := by
    have hnat : (1328170687 : ℕ)^527*100000000000000^399 ≤ 43370459665757^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328170687 2500000000 43370459665757 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128783361/625000000 : ℝ)^527 ≤ (12413751924573/100000000000000 : ℝ)^399 := by
    have hnat : (128783361 : ℕ)^527*100000000000000^399 ≤ 12413751924573^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128783361 625000000 12413751924573 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390897163/10000000000 : ℝ)^527 ≤ (5526973550291/12500000000000 : ℝ)^399 := by
    have hnat : (5390897163 : ℕ)^527*12500000000000^399 ≤ 5526973550291^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390897163 10000000000 5526973550291 12500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328170687/2500000000 : ℝ), (-128783361/625000000 : ℝ), (5390897163/10000000000 : ℝ)] ![(43370459665757/100000000000000 : ℝ), (12413751924573/100000000000000 : ℝ), (5526973550291/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328170687/2500000000 : ℝ)|^527 ≤ (43370459665757/100000000000000 : ℝ)^399
        have hw : |(1328170687/2500000000 : ℝ)|=(1328170687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128783361/625000000 : ℝ)|^527 ≤ (12413751924573/100000000000000 : ℝ)^399
        have hw : |(-128783361/625000000 : ℝ)|=(128783361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390897163/10000000000 : ℝ)|^527 ≤ (5526973550291/12500000000000 : ℝ)^399
        have hw : |(5390897163/10000000000 : ℝ)|=(5390897163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s8_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (664085351/1250000000 : ℝ)*x 0 + (1347724259/2500000000 : ℝ)*x 1 + (-1030266933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664085351/1250000000 : ℝ)^527 ≤ (8674092062541/20000000000000 : ℝ)^399 := by
    have hnat : (664085351 : ℕ)^527*20000000000000^399 ≤ 8674092062541^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664085351 1250000000 8674092062541 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347724259/2500000000 : ℝ)^527 ≤ (1105394675663/2500000000000 : ℝ)^399 := by
    have hnat : (1347724259 : ℕ)^527*2500000000000^399 ≤ 1105394675663^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347724259 2500000000 1105394675663 2500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030266933/5000000000 : ℝ)^527 ≤ (6206876320361/50000000000000 : ℝ)^399 := by
    have hnat : (1030266933 : ℕ)^527*50000000000000^399 ≤ 6206876320361^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030266933 5000000000 6206876320361 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664085351/1250000000 : ℝ), (1347724259/2500000000 : ℝ), (-1030266933/5000000000 : ℝ)] ![(8674092062541/20000000000000 : ℝ), (1105394675663/2500000000000 : ℝ), (6206876320361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664085351/1250000000 : ℝ)|^527 ≤ (8674092062541/20000000000000 : ℝ)^399
        have hw : |(664085351/1250000000 : ℝ)|=(664085351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347724259/2500000000 : ℝ)|^527 ≤ (1105394675663/2500000000000 : ℝ)^399
        have hw : |(1347724259/2500000000 : ℝ)|=(1347724259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030266933/5000000000 : ℝ)|^527 ≤ (6206876320361/50000000000000 : ℝ)^399
        have hw : |(-1030266933/5000000000 : ℝ)|=(1030266933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s8_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1087799073/2500000000 : ℝ)*x 0 + (4478013489/10000000000 : ℝ)*x 1 + (1056973801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087799073/2500000000 : ℝ)^527 ≤ (16658796332621/50000000000000 : ℝ)^399 := by
    have hnat : (1087799073 : ℕ)^527*50000000000000^399 ≤ 16658796332621^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087799073 2500000000 16658796332621 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478013489/10000000000 : ℝ)^527 ≤ (6921223744691/20000000000000 : ℝ)^399 := by
    have hnat : (4478013489 : ℕ)^527*20000000000000^399 ≤ 6921223744691^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478013489 10000000000 6921223744691 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056973801/2500000000 : ℝ)^527 ≤ (16038144297149/50000000000000 : ℝ)^399 := by
    have hnat : (1056973801 : ℕ)^527*50000000000000^399 ≤ 16038144297149^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056973801 2500000000 16038144297149 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087799073/2500000000 : ℝ), (4478013489/10000000000 : ℝ), (1056973801/2500000000 : ℝ)] ![(16658796332621/50000000000000 : ℝ), (6921223744691/20000000000000 : ℝ), (16038144297149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087799073/2500000000 : ℝ)|^527 ≤ (16658796332621/50000000000000 : ℝ)^399
        have hw : |(1087799073/2500000000 : ℝ)|=(1087799073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478013489/10000000000 : ℝ)|^527 ≤ (6921223744691/20000000000000 : ℝ)^399
        have hw : |(4478013489/10000000000 : ℝ)|=(4478013489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056973801/2500000000 : ℝ)|^527 ≤ (16038144297149/50000000000000 : ℝ)^399
        have hw : |(1056973801/2500000000 : ℝ)|=(1056973801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (459/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7051/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (459/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (459/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (459/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (459/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (459/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (459/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (459/4000 : ℝ) ^ (8431/2048 : ℝ) ≤ (2693485528272009/20000000000000000000 : ℝ) := by
    have hpowers : (459/4000 : ℝ)^8431 ≤ (2693485528272009/20000000000000000000 : ℝ)^2048 := by
      have hnat : (459 : ℕ)^8431*20000000000000000000^2048 ≤ 2693485528272009^2048*4000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 4000 2693485528272009 20000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/4000 : ℝ)) (X := (2693485528272009/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14103/100000 : ℝ) ^ (8431/2048 : ℝ) ≤ (251803248120807/800000000000000000 : ℝ) := by
    have hpowers : (14103/100000 : ℝ)^8431 ≤ (251803248120807/800000000000000000 : ℝ)^2048 := by
      have hnat : (14103 : ℕ)^8431*800000000000000000^2048 ≤ 251803248120807^2048*100000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14103 100000 251803248120807 800000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14103/100000 : ℝ)) (X := (251803248120807/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002693485528272009/10000000000000000000 : ℝ) ≤ (5000327108054333/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (10002693485528272009/10000000000000000000 : ℝ)^2048 ≤ (5000327108054333/5000000000000000 : ℝ)^8431 := by
      have hnat : (10002693485528272009 : ℕ)^2048*5000000000000000^8431 ≤ 5000327108054333^8431*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002693485528272009 10000000000000000000 5000327108054333 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000327108054333/5000000000000000 : ℝ)) (X := (10002693485528272009/10000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501123570841411523/2500000000000000000 : ℝ) ≤ (10001091534436671/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (2501123570841411523/2500000000000000000 : ℝ)^2048 ≤ (10001091534436671/10000000000000000 : ℝ)^8431 := by
      have hnat : (2501123570841411523 : ℕ)^2048*10000000000000000^8431 ≤ 10001091534436671^8431*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501123570841411523 2500000000000000000 10001091534436671 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001091534436671/10000000000000000 : ℝ)) (X := (2501123570841411523/2500000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (400251803248120807/400000000000000000 : ℝ) ≤ (2500382213191169/2500000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (400251803248120807/400000000000000000 : ℝ)^2048 ≤ (2500382213191169/2500000000000000 : ℝ)^8431 := by
      have hnat : (400251803248120807 : ℕ)^2048*2500000000000000^8431 ≤ 2500382213191169^8431*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400251803248120807 400000000000000000 2500382213191169 2500000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500382213191169/2500000000000000 : ℝ)) (X := (400251803248120807/400000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2693485528272009/20000000000000000000 : ℝ) ≤ ((1459537934683658861/1460000000000000000 : ℝ)+2*(87463665601/52560000000000 : ℝ)*(459/4000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (1459537934683658861/1460000000000000000 : ℝ)+2*(87463665601/52560000000000 : ℝ)*(459/4000 : ℝ)=(5000327108054333/5000000000000000 : ℝ) by norm_num, show 1+2*(2693485528272009/20000000000000000000 : ℝ)=(10002693485528272009/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(251803248120807/800000000000000000 : ℝ)+(2693485528272009/20000000000000000000 : ℝ) ≤ ((1459537934683658861/1460000000000000000 : ℝ)+(87463665601/52560000000000 : ℝ)*((14103/100000 : ℝ)+(459/4000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (1459537934683658861/1460000000000000000 : ℝ)+(87463665601/52560000000000 : ℝ)*((14103/100000 : ℝ)+(459/4000 : ℝ))=(10001091534436671/10000000000000000 : ℝ) by norm_num, show 1+(251803248120807/800000000000000000 : ℝ)+(2693485528272009/20000000000000000000 : ℝ)=(2501123570841411523/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(251803248120807/800000000000000000 : ℝ) ≤ ((1459537934683658861/1460000000000000000 : ℝ)+2*(87463665601/52560000000000 : ℝ)*(14103/100000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (1459537934683658861/1460000000000000000 : ℝ)+2*(87463665601/52560000000000 : ℝ)*(14103/100000 : ℝ)=(2500382213191169/2500000000000000 : ℝ) by norm_num, show 1+2*(251803248120807/800000000000000000 : ℝ)=(400251803248120807/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1459537934683658861/1460000000000000000 : ℝ)*(X 1 0+X 2 0)+(87463665601/52560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (1459537934683658861/1460000000000000000 : ℝ)) (alpha := (87463665601/52560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1459537934683658861/1460000000000000000 : ℝ)*(X 0 1+X 2 1)+(87463665601/52560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (1459537934683658861/1460000000000000000 : ℝ)) (alpha := (87463665601/52560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1459537934683658861/1460000000000000000 : ℝ)*(X 0 2+X 1 2)+(87463665601/52560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (1459537934683658861/1460000000000000000 : ℝ)) (alpha := (87463665601/52560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((334019641/625000000 : ℝ)*X 1 0+(-1092107771/5000000000 : ℝ)*X 1 1+(1316803883/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s8_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2121351467/10000000000 : ℝ)*X 0 0+(658440989/1250000000 : ℝ)*X 0 1+(2695448571/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1328170687/2500000000 : ℝ)*X 1 0+(-128783361/625000000 : ℝ)*X 1 1+(5390897163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((664085351/1250000000 : ℝ)*X 2 0+(1347724259/2500000000 : ℝ)*X 2 1+(-1030266933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1087799073/2500000000 : ℝ)*X 0 0+(4478013489/10000000000 : ℝ)*X 0 1+(1056973801/2500000000 : ℝ)*X 0 2+(1087799073/2500000000 : ℝ)*X 1 0+(4478013489/10000000000 : ℝ)*X 1 1+(1056973801/2500000000 : ℝ)*X 1 2+(1087799073/2500000000 : ℝ)*X 2 0+(4478013489/10000000000 : ℝ)*X 2 1+(1056973801/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87657037148631334181/43800000000000000000000000 : ℝ) := by norm_num
    linear_combination (485027981/50000000000000 : ℝ)*(base19) + (150759309/12500000000000 : ℝ)*(base23) + (180235893/50000000000000 : ℝ)*(lower1) + (79202411/100000000000000 : ℝ)*(upper2) + (94088841/100000000000000 : ℝ)*(upper3) + (40927861/50000000000000 : ℝ)*(upper5) + (151297641580429/2500000000000 : ℝ)*(major0) + (151297641580429/2500000000000 : ℝ)*(major1) + (151297641580429/2500000000000 : ℝ)*(major2) + (773773049/100000000000000 : ℝ)*(sp0) + (1621143487467431/20000000000000 : ℝ)*(sp1) + (506607230844259/6250000000000 : ℝ)*(sp2) + (8105716231262683/100000000000000 : ℝ)*(sp3) + (99952345559677/2500000000000 : ℝ)*(sp4) + (99952345559677/2500000000000 : ℝ)*(f.failure) + (1621143487467431/20000000000000 : ℝ)*(f.sum) + (341988972457/131400000000000000000000000 : ℝ)*base66 + (85424147709532321/32850000000000000000000000000000 : ℝ)*base67 + (734708388912967679/32850000000000000000000000000000 : ℝ)*base70 + (223906570391932321/32850000000000000000000000000000 : ℝ)*base71 + (40641041777/20531250000000000000000000 : ℝ)*base73 + (252010952826532321/32850000000000000000000000000000 : ℝ)*base75 + (78328790530867679/32850000000000000000000000000000 : ℝ)*base78 + (354928040230267679/32850000000000000000000000000000 : ℝ)*base80 + (1845794141369/41062500000000000000000000 : ℝ)*base82 + (132647/15625000000000000000 : ℝ)*base89 + (132647/15625000000000000000 : ℝ)*base91 + (132647/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1239_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1239_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1239_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1239_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1239_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1239_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

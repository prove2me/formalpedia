-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1174_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:48.429852+00:00
-- url     : https://prove2.me/submissions/efbcc45c-3230-49c7-91c0-180ec668165a

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
theorem support_rectangle_w1174_s0_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-940861957/5000000000 : ℝ)*x 0 + (151174093/250000000 : ℝ)*x 1 + (2392253019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940861957/5000000000 : ℝ)^8367 ≤ (684412764987/6250000000000 : ℝ)^6319 := by
    have hnat : (940861957 : ℕ)^8367*6250000000000^6319 ≤ 684412764987^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940861957 5000000000 684412764987 6250000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151174093/250000000 : ℝ)^8367 ≤ (10274559219971/20000000000000 : ℝ)^6319 := by
    have hnat : (151174093 : ℕ)^8367*20000000000000^6319 ≤ 10274559219971^6319*250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151174093 250000000 10274559219971 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2392253019/5000000000 : ℝ)^8367 ≤ (9419149910681/25000000000000 : ℝ)^6319 := by
    have hnat : (2392253019 : ℕ)^8367*25000000000000^6319 ≤ 9419149910681^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392253019 5000000000 9419149910681 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-940861957/5000000000 : ℝ), (151174093/250000000 : ℝ), (2392253019/5000000000 : ℝ)] ![(684412764987/6250000000000 : ℝ), (10274559219971/20000000000000 : ℝ), (9419149910681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-940861957/5000000000 : ℝ)|^8367 ≤ (684412764987/6250000000000 : ℝ)^6319
        have hw : |(-940861957/5000000000 : ℝ)|=(940861957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151174093/250000000 : ℝ)|^8367 ≤ (10274559219971/20000000000000 : ℝ)^6319
        have hw : |(151174093/250000000 : ℝ)|=(151174093/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2392253019/5000000000 : ℝ)|^8367 ≤ (9419149910681/25000000000000 : ℝ)^6319
        have hw : |(2392253019/5000000000 : ℝ)|=(2392253019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s0_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689373849/1250000000 : ℝ)*x 0 + (-260532571/1000000000 : ℝ)*x 1 + (299031627/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689373849/1250000000 : ℝ)^8367 ≤ (45475655071141/100000000000000 : ℝ)^6319 := by
    have hnat : (689373849 : ℕ)^8367*100000000000000^6319 ≤ 45475655071141^6319*1250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689373849 1250000000 45475655071141 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260532571/1000000000 : ℝ)^8367 ≤ (16847745327879/100000000000000 : ℝ)^6319 := by
    have hnat : (260532571 : ℕ)^8367*100000000000000^6319 ≤ 16847745327879^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260532571 1000000000 16847745327879 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299031627/625000000 : ℝ)^8367 ≤ (37676599580163/100000000000000 : ℝ)^6319 := by
    have hnat : (299031627 : ℕ)^8367*100000000000000^6319 ≤ 37676599580163^6319*625000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299031627 625000000 37676599580163 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689373849/1250000000 : ℝ), (-260532571/1000000000 : ℝ), (299031627/625000000 : ℝ)] ![(45475655071141/100000000000000 : ℝ), (16847745327879/100000000000000 : ℝ), (37676599580163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689373849/1250000000 : ℝ)|^8367 ≤ (45475655071141/100000000000000 : ℝ)^6319
        have hw : |(689373849/1250000000 : ℝ)|=(689373849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260532571/1000000000 : ℝ)|^8367 ≤ (16847745327879/100000000000000 : ℝ)^6319
        have hw : |(-260532571/1000000000 : ℝ)|=(260532571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299031627/625000000 : ℝ)|^8367 ≤ (37676599580163/100000000000000 : ℝ)^6319
        have hw : |(299031627/625000000 : ℝ)|=(299031627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s0_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757495443/5000000000 : ℝ)*x 0 + (598063243/1250000000 : ℝ)*x 1 + (-1302662849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757495443/5000000000 : ℝ)^8367 ≤ (22737828048731/50000000000000 : ℝ)^6319 := by
    have hnat : (2757495443 : ℕ)^8367*50000000000000^6319 ≤ 22737828048731^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757495443 5000000000 22737828048731 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598063243/1250000000 : ℝ)^8367 ≤ (18838299331297/50000000000000 : ℝ)^6319 := by
    have hnat : (598063243 : ℕ)^8367*50000000000000^6319 ≤ 18838299331297^6319*1250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598063243 1250000000 18838299331297 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302662849/5000000000 : ℝ)^8367 ≤ (16847745225129/100000000000000 : ℝ)^6319 := by
    have hnat : (1302662849 : ℕ)^8367*100000000000000^6319 ≤ 16847745225129^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302662849 5000000000 16847745225129 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757495443/5000000000 : ℝ), (598063243/1250000000 : ℝ), (-1302662849/5000000000 : ℝ)] ![(22737828048731/50000000000000 : ℝ), (18838299331297/50000000000000 : ℝ), (16847745225129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757495443/5000000000 : ℝ)|^8367 ≤ (22737828048731/50000000000000 : ℝ)^6319
        have hw : |(2757495443/5000000000 : ℝ)|=(2757495443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598063243/1250000000 : ℝ)|^8367 ≤ (18838299331297/50000000000000 : ℝ)^6319
        have hw : |(598063243/1250000000 : ℝ)|=(598063243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1302662849/5000000000 : ℝ)|^8367 ≤ (16847745225129/100000000000000 : ℝ)^6319
        have hw : |(-1302662849/5000000000 : ℝ)|=(1302662849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s0_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2099207503/5000000000 : ℝ)*x 0 + (3119642093/10000000000 : ℝ)*x 1 + (2823521697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099207503/5000000000 : ℝ)^8367 ≤ (31690318999019/100000000000000 : ℝ)^6319 := by
    have hnat : (2099207503 : ℕ)^8367*100000000000000^6319 ≤ 31690318999019^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099207503 5000000000 31690318999019 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3119642093/10000000000 : ℝ)^8367 ≤ (21386669562163/100000000000000 : ℝ)^6319 := by
    have hnat : (3119642093 : ℕ)^8367*100000000000000^6319 ≤ 21386669562163^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119642093 10000000000 21386669562163 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823521697/5000000000 : ℝ)^8367 ≤ (46923011418237/100000000000000 : ℝ)^6319 := by
    have hnat : (2823521697 : ℕ)^8367*100000000000000^6319 ≤ 46923011418237^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823521697 5000000000 46923011418237 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099207503/5000000000 : ℝ), (3119642093/10000000000 : ℝ), (2823521697/5000000000 : ℝ)] ![(31690318999019/100000000000000 : ℝ), (21386669562163/100000000000000 : ℝ), (46923011418237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099207503/5000000000 : ℝ)|^8367 ≤ (31690318999019/100000000000000 : ℝ)^6319
        have hw : |(2099207503/5000000000 : ℝ)|=(2099207503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3119642093/10000000000 : ℝ)|^8367 ≤ (21386669562163/100000000000000 : ℝ)^6319
        have hw : |(3119642093/10000000000 : ℝ)|=(3119642093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823521697/5000000000 : ℝ)|^8367 ≤ (46923011418237/100000000000000 : ℝ)^6319
        have hw : |(2823521697/5000000000 : ℝ)|=(2823521697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s0_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-235847013/1250000000 : ℝ)*x 0 + (4817057089/10000000000 : ℝ)*x 1 + (3006632919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235847013/1250000000 : ℝ)^8367 ≤ (2747387766403/25000000000000 : ℝ)^6319 := by
    have hnat : (235847013 : ℕ)^8367*25000000000000^6319 ≤ 2747387766403^6319*1250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235847013 1250000000 2747387766403 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4817057089/10000000000 : ℝ)^8367 ≤ (19008190222847/50000000000000 : ℝ)^6319 := by
    have hnat : (4817057089 : ℕ)^8367*50000000000000^6319 ≤ 19008190222847^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817057089 10000000000 19008190222847 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3006632919/5000000000 : ℝ)^8367 ≤ (50994068466119/100000000000000 : ℝ)^6319 := by
    have hnat : (3006632919 : ℕ)^8367*100000000000000^6319 ≤ 50994068466119^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3006632919 5000000000 50994068466119 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235847013/1250000000 : ℝ), (4817057089/10000000000 : ℝ), (3006632919/5000000000 : ℝ)] ![(2747387766403/25000000000000 : ℝ), (19008190222847/50000000000000 : ℝ), (50994068466119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235847013/1250000000 : ℝ)|^8367 ≤ (2747387766403/25000000000000 : ℝ)^6319
        have hw : |(-235847013/1250000000 : ℝ)|=(235847013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4817057089/10000000000 : ℝ)|^8367 ≤ (19008190222847/50000000000000 : ℝ)^6319
        have hw : |(4817057089/10000000000 : ℝ)|=(4817057089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3006632919/5000000000 : ℝ)|^8367 ≤ (50994068466119/100000000000000 : ℝ)^6319
        have hw : |(3006632919/5000000000 : ℝ)|=(3006632919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s0_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171799777/10000000000 : ℝ)*x 0 + (-688283047/5000000000 : ℝ)*x 1 + (6013265589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171799777/10000000000 : ℝ)^8367 ≤ (8353383620619/20000000000000 : ℝ)^6319 := by
    have hnat : (5171799777 : ℕ)^8367*20000000000000^6319 ≤ 8353383620619^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171799777 10000000000 8353383620619 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688283047/5000000000 : ℝ)^8367 ≤ (904877026113/12500000000000 : ℝ)^6319 := by
    have hnat : (688283047 : ℕ)^8367*12500000000000^6319 ≤ 904877026113^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688283047 5000000000 904877026113 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6013265589/10000000000 : ℝ)^8367 ≤ (10198813134033/20000000000000 : ℝ)^6319 := by
    have hnat : (6013265589 : ℕ)^8367*20000000000000^6319 ≤ 10198813134033^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013265589 10000000000 10198813134033 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171799777/10000000000 : ℝ), (-688283047/5000000000 : ℝ), (6013265589/10000000000 : ℝ)] ![(8353383620619/20000000000000 : ℝ), (904877026113/12500000000000 : ℝ), (10198813134033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171799777/10000000000 : ℝ)|^8367 ≤ (8353383620619/20000000000000 : ℝ)^6319
        have hw : |(5171799777/10000000000 : ℝ)|=(5171799777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-688283047/5000000000 : ℝ)|^8367 ≤ (904877026113/12500000000000 : ℝ)^6319
        have hw : |(-688283047/5000000000 : ℝ)|=(688283047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6013265589/10000000000 : ℝ)|^8367 ≤ (10198813134033/20000000000000 : ℝ)^6319
        have hw : |(6013265589/10000000000 : ℝ)|=(6013265589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s0_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585899867/5000000000 : ℝ)*x 0 + (6013265707/10000000000 : ℝ)*x 1 + (-137656597/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585899867/5000000000 : ℝ)^8367 ≤ (41766917643283/100000000000000 : ℝ)^6319 := by
    have hnat : (2585899867 : ℕ)^8367*100000000000000^6319 ≤ 41766917643283^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585899867 5000000000 41766917643283 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6013265707/10000000000 : ℝ)^8367 ≤ (10198813399031/20000000000000 : ℝ)^6319 := by
    have hnat : (6013265707 : ℕ)^8367*20000000000000^6319 ≤ 10198813399031^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013265707 10000000000 10198813399031 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137656597/1000000000 : ℝ)^8367 ≤ (7239015345477/100000000000000 : ℝ)^6319 := by
    have hnat : (137656597 : ℕ)^8367*100000000000000^6319 ≤ 7239015345477^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137656597 1000000000 7239015345477 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585899867/5000000000 : ℝ), (6013265707/10000000000 : ℝ), (-137656597/1000000000 : ℝ)] ![(41766917643283/100000000000000 : ℝ), (10198813399031/20000000000000 : ℝ), (7239015345477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585899867/5000000000 : ℝ)|^8367 ≤ (41766917643283/100000000000000 : ℝ)^6319
        have hw : |(2585899867/5000000000 : ℝ)|=(2585899867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6013265707/10000000000 : ℝ)|^8367 ≤ (10198813399031/20000000000000 : ℝ)^6319
        have hw : |(6013265707/10000000000 : ℝ)|=(6013265707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137656597/1000000000 : ℝ)|^8367 ≤ (7239015345477/100000000000000 : ℝ)^6319
        have hw : |(-137656597/1000000000 : ℝ)|=(137656597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s0_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4208529327/10000000000 : ℝ)*x 0 + (5581876683/10000000000 : ℝ)*x 1 + (3187104489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208529327/10000000000 : ℝ)^8367 ≤ (15895723196131/50000000000000 : ℝ)^6319 := by
    have hnat : (4208529327 : ℕ)^8367*50000000000000^6319 ≤ 15895723196131^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208529327 10000000000 15895723196131 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5581876683/10000000000 : ℝ)^8367 ≤ (46207367601609/100000000000000 : ℝ)^6319 := by
    have hnat : (5581876683 : ℕ)^8367*100000000000000^6319 ≤ 46207367601609^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5581876683 10000000000 46207367601609 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187104489/10000000000 : ℝ)^8367 ≤ (5500296499601/25000000000000 : ℝ)^6319 := by
    have hnat : (3187104489 : ℕ)^8367*25000000000000^6319 ≤ 5500296499601^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187104489 10000000000 5500296499601 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208529327/10000000000 : ℝ), (5581876683/10000000000 : ℝ), (3187104489/10000000000 : ℝ)] ![(15895723196131/50000000000000 : ℝ), (46207367601609/100000000000000 : ℝ), (5500296499601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208529327/10000000000 : ℝ)|^8367 ≤ (15895723196131/50000000000000 : ℝ)^6319
        have hw : |(4208529327/10000000000 : ℝ)|=(4208529327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5581876683/10000000000 : ℝ)|^8367 ≤ (46207367601609/100000000000000 : ℝ)^6319
        have hw : |(5581876683/10000000000 : ℝ)|=(5581876683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187104489/10000000000 : ℝ)|^8367 ≤ (5500296499601/25000000000000 : ℝ)^6319
        have hw : |(3187104489/10000000000 : ℝ)|=(3187104489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (109/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27693/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4183/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4183 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4183*1^1024 ≤ 0^1024*1^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4183/1024 : ℝ) ≤ (592066675899848219/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4183 ≤ (592066675899848219/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4183*25000000000000000000^1024 ≤ 592066675899848219^1024*5^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 592066675899848219 25000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (592066675899848219/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4183 := by
      have hnat : (1 : ℕ)^1024*1^4183 ≤ 1^4183*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25592066675899848219/25000000000000000000 : ℝ) ≤ (10057463880085817/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (25592066675899848219/25000000000000000000 : ℝ)^1024 ≤ (10057463880085817/10000000000000000 : ℝ)^4183 := by
      have hnat : (25592066675899848219 : ℕ)^1024*10000000000000000^4183 ≤ 10057463880085817^4183*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25592066675899848219 25000000000000000000 10057463880085817 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057463880085817/10000000000000000 : ℝ)) (X := (25592066675899848219/25000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13092066675899848219/12500000000000000000 : ℝ) ≤ (5057463880085817/5000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (13092066675899848219/12500000000000000000 : ℝ)^1024 ≤ (5057463880085817/5000000000000000 : ℝ)^4183 := by
      have hnat : (13092066675899848219 : ℕ)^1024*5000000000000000^4183 ≤ 5057463880085817^4183*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13092066675899848219 12500000000000000000 5057463880085817 5000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057463880085817/5000000000000000 : ℝ)) (X := (13092066675899848219/12500000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57463880085817/4000000000000000 : ℝ)*(0 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(57463880085817/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(592066675899848219/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57463880085817/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (1 : ℝ)+(57463880085817/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057463880085817/10000000000000000 : ℝ) by norm_num, show 1+(592066675899848219/25000000000000000000 : ℝ)+(0 : ℝ)=(25592066675899848219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(592066675899848219/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57463880085817/4000000000000000 : ℝ)*(2/5 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(57463880085817/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057463880085817/5000000000000000 : ℝ) by norm_num, show 1+2*(592066675899848219/25000000000000000000 : ℝ)=(13092066675899848219/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57463880085817/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57463880085817/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57463880085817/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57463880085817/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57463880085817/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57463880085817/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-940861957/5000000000 : ℝ)*X 0 0+(151174093/250000000 : ℝ)*X 0 1+(2392253019/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((689373849/1250000000 : ℝ)*X 1 0+(-260532571/1000000000 : ℝ)*X 1 1+(299031627/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757495443/5000000000 : ℝ)*X 2 0+(598063243/1250000000 : ℝ)*X 2 1+(-1302662849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099207503/5000000000 : ℝ)*X 0 0+(3119642093/10000000000 : ℝ)*X 0 1+(2823521697/5000000000 : ℝ)*X 0 2+(2099207503/5000000000 : ℝ)*X 1 0+(3119642093/10000000000 : ℝ)*X 1 1+(2823521697/5000000000 : ℝ)*X 1 2+(2099207503/5000000000 : ℝ)*X 2 0+(3119642093/10000000000 : ℝ)*X 2 1+(2823521697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-235847013/1250000000 : ℝ)*X 0 0+(4817057089/10000000000 : ℝ)*X 0 1+(3006632919/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171799777/10000000000 : ℝ)*X 1 0+(-688283047/5000000000 : ℝ)*X 1 1+(6013265589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585899867/5000000000 : ℝ)*X 2 0+(6013265707/10000000000 : ℝ)*X 2 1+(-137656597/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4208529327/10000000000 : ℝ)*X 0 0+(5581876683/10000000000 : ℝ)*X 0 1+(3187104489/10000000000 : ℝ)*X 0 2+(4208529327/10000000000 : ℝ)*X 1 0+(5581876683/10000000000 : ℝ)*X 1 1+(3187104489/10000000000 : ℝ)*X 1 2+(4208529327/10000000000 : ℝ)*X 2 0+(5581876683/10000000000 : ℝ)*X 2 1+(3187104489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (283702695953935419355347/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23903729/100000000000000 : ℝ)*(base1) + (316439837/100000000000000 : ℝ)*(base19) + (61649061/20000000000000 : ℝ)*(base23) + (5423891/25000000000000 : ℝ)*(base24) + (12950743/20000000000000 : ℝ)*(upper3) + (296942939764087/50000000000000 : ℝ)*(major0) + (296942939764087/50000000000000 : ℝ)*(major1) + (23755435181127/4000000000000 : ℝ)*(major2) + (396053390886023/50000000000000 : ℝ)*(sp0) + (792107160635551/100000000000000 : ℝ)*(sp1) + (396053573567259/50000000000000 : ℝ)*(sp2) + (49457957365939/12500000000000 : ℝ)*(sp3) + (71920707/10000000000000 : ℝ)*(sp4) + (551865931/100000000000000 : ℝ)*(sp7) + (98916058674293/25000000000000 : ℝ)*(f.failure) + (198026869268847/25000000000000 : ℝ)*(f.sum) + (308355015297867/400000000000000000000000000000 : ℝ)*base66 + (16210938648241/16000000000000000000000000000 : ℝ)*base68 + (261342384345921/200000000000000000000000000000 : ℝ)*base70 + (136675099640241/16000000000000000000000000000 : ℝ)*base72 + (720567747102133/400000000000000000000000000000 : ℝ)*base73 + (222833429145921/200000000000000000000000000000 : ℝ)*base76 + (1567801996745921/200000000000000000000000000000 : ℝ)*base78 + (124165601545921/200000000000000000000000000000 : ℝ)*base80 + (1021308347645921/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (25471557/2500000000000000000000 : ℝ)*base89 + (25471557/2500000000000000000000 : ℝ)*base91 + (471557/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317833837456979155700391/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74554807/100000000000000 : ℝ)*(base1) + (794525281/50000000000000 : ℝ)*(base19) + (197955259/12500000000000 : ℝ)*(base23) + (6817333/4000000000000 : ℝ)*(upper3) + (189798567/100000000000000 : ℝ)*(upper5) + (156693878089941/25000000000000 : ℝ)*(major0) + (156693878089941/25000000000000 : ℝ)*(major1) + (156693878089941/25000000000000 : ℝ)*(major2) + (3234411281/100000000000000 : ℝ)*(sp1) + (407206047/12500000000000 : ℝ)*(sp2) + (835974612256663/100000000000000 : ℝ)*(sp4) + (417984857120007/50000000000000 : ℝ)*(sp5) + (52248106025713/6250000000000 : ℝ)*(sp6) + (83515240114727/20000000000000 : ℝ)*(sp7) + (208788137564221/50000000000000 : ℝ)*(f.failure) + (26124204303183/3125000000000 : ℝ)*(f.sum) + (4501489816797/50000000000000000000000000000 : ℝ)*base65 + (75098453266797/100000000000000000000000000000 : ℝ)*base67 + (621565486433203/100000000000000000000000000000 : ℝ)*base70 + (753242383033203/100000000000000000000000000000 : ℝ)*base72 + (243505480516797/50000000000000000000000000000 : ℝ)*base73 + (1189630150833203/100000000000000000000000000000 : ℝ)*base76 + (122848900833203/100000000000000000000000000000 : ℝ)*base78 + (358131386033203/100000000000000000000000000000 : ℝ)*base80 + (106142640883203/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9993229/5000000000000000000000 : ℝ)*base89 + (9993229/5000000000000000000000 : ℝ)*base91 + (9993229/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1174_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (109/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27693/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1174_s1_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1042034573/5000000000 : ℝ)*x 0 + (711630071/1250000000 : ℝ)*x 1 + (125222461/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042034573/5000000000 : ℝ)^8367 ≤ (3134081226307/25000000000000 : ℝ)^6319 := by
    have hnat : (1042034573 : ℕ)^8367*25000000000000^6319 ≤ 3134081226307^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042034573 5000000000 3134081226307 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (711630071/1250000000 : ℝ)^8367 ≤ (94859512067/200000000000 : ℝ)^6319 := by
    have hnat : (711630071 : ℕ)^8367*200000000000^6319 ≤ 94859512067^6319*1250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711630071 1250000000 94859512067 200000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125222461/250000000 : ℝ)^8367 ≤ (40033919040391/100000000000000 : ℝ)^6319 := by
    have hnat : (125222461 : ℕ)^8367*100000000000000^6319 ≤ 40033919040391^6319*250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125222461 250000000 40033919040391 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1042034573/5000000000 : ℝ), (711630071/1250000000 : ℝ), (125222461/250000000 : ℝ)] ![(3134081226307/25000000000000 : ℝ), (94859512067/200000000000 : ℝ), (40033919040391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1042034573/5000000000 : ℝ)|^8367 ≤ (3134081226307/25000000000000 : ℝ)^6319
        have hw : |(-1042034573/5000000000 : ℝ)|=(1042034573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(711630071/1250000000 : ℝ)|^8367 ≤ (94859512067/200000000000 : ℝ)^6319
        have hw : |(711630071/1250000000 : ℝ)|=(711630071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125222461/250000000 : ℝ)|^8367 ≤ (40033919040391/100000000000000 : ℝ)^6319
        have hw : |(125222461/250000000 : ℝ)|=(125222461/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s1_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417368349/10000000000 : ℝ)*x 0 + (-1226336811/5000000000 : ℝ)*x 1 + (2504448743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417368349/10000000000 : ℝ)^8367 ≤ (44412852322591/100000000000000 : ℝ)^6319 := by
    have hnat : (5417368349 : ℕ)^8367*100000000000000^6319 ≤ 44412852322591^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417368349 10000000000 44412852322591 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226336811/5000000000 : ℝ)^8367 ≤ (1555323872303/10000000000000 : ℝ)^6319 := by
    have hnat : (1226336811 : ℕ)^8367*10000000000000^6319 ≤ 1555323872303^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226336811 5000000000 1555323872303 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2504448743/5000000000 : ℝ)^8367 ≤ (10008477236061/25000000000000 : ℝ)^6319 := by
    have hnat : (2504448743 : ℕ)^8367*25000000000000^6319 ≤ 10008477236061^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504448743 5000000000 10008477236061 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417368349/10000000000 : ℝ), (-1226336811/5000000000 : ℝ), (2504448743/5000000000 : ℝ)] ![(44412852322591/100000000000000 : ℝ), (1555323872303/10000000000000 : ℝ), (10008477236061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417368349/10000000000 : ℝ)|^8367 ≤ (44412852322591/100000000000000 : ℝ)^6319
        have hw : |(5417368349/10000000000 : ℝ)|=(5417368349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1226336811/5000000000 : ℝ)|^8367 ≤ (1555323872303/10000000000000 : ℝ)^6319
        have hw : |(-1226336811/5000000000 : ℝ)|=(1226336811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2504448743/5000000000 : ℝ)|^8367 ≤ (10008477236061/25000000000000 : ℝ)^6319
        have hw : |(2504448743/5000000000 : ℝ)|=(2504448743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s1_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417370457/10000000000 : ℝ)*x 0 + (2504447753/5000000000 : ℝ)*x 1 + (-153292087/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417370457/10000000000 : ℝ)^8367 ≤ (44412875205559/100000000000000 : ℝ)^6319 := by
    have hnat : (5417370457 : ℕ)^8367*100000000000000^6319 ≤ 44412875205559^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417370457 10000000000 44412875205559 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2504447753/5000000000 : ℝ)^8367 ≤ (40033887989979/100000000000000 : ℝ)^6319 := by
    have hnat : (2504447753 : ℕ)^8367*100000000000000^6319 ≤ 40033887989979^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504447753 5000000000 40033887989979 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153292087/625000000 : ℝ)^8367 ≤ (15553236791817/100000000000000 : ℝ)^6319 := by
    have hnat : (153292087 : ℕ)^8367*100000000000000^6319 ≤ 15553236791817^6319*625000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153292087 625000000 15553236791817 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417370457/10000000000 : ℝ), (2504447753/5000000000 : ℝ), (-153292087/625000000 : ℝ)] ![(44412875205559/100000000000000 : ℝ), (40033887989979/100000000000000 : ℝ), (15553236791817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417370457/10000000000 : ℝ)|^8367 ≤ (44412875205559/100000000000000 : ℝ)^6319
        have hw : |(5417370457/10000000000 : ℝ)|=(5417370457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2504447753/5000000000 : ℝ)|^8367 ≤ (40033887989979/100000000000000 : ℝ)^6319
        have hw : |(2504447753/5000000000 : ℝ)|=(2504447753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153292087/625000000 : ℝ)|^8367 ≤ (15553236791817/100000000000000 : ℝ)^6319
        have hw : |(-153292087/625000000 : ℝ)|=(153292087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s1_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4314718059/10000000000 : ℝ)*x 0 + (920753791/2500000000 : ℝ)*x 1 + (101052819/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314718059/10000000000 : ℝ)^8367 ≤ (3285789999891/10000000000000 : ℝ)^6319 := by
    have hnat : (4314718059 : ℕ)^8367*10000000000000^6319 ≤ 3285789999891^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314718059 10000000000 3285789999891 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920753791/2500000000 : ℝ)^8367 ≤ (3330575215543/12500000000000 : ℝ)^6319 := by
    have hnat : (920753791 : ℕ)^8367*12500000000000^6319 ≤ 3330575215543^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920753791 2500000000 3330575215543 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101052819/200000000 : ℝ)^8367 ≤ (40497498263269/100000000000000 : ℝ)^6319 := by
    have hnat : (101052819 : ℕ)^8367*100000000000000^6319 ≤ 40497498263269^6319*200000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101052819 200000000 40497498263269 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314718059/10000000000 : ℝ), (920753791/2500000000 : ℝ), (101052819/200000000 : ℝ)] ![(3285789999891/10000000000000 : ℝ), (3330575215543/12500000000000 : ℝ), (40497498263269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314718059/10000000000 : ℝ)|^8367 ≤ (3285789999891/10000000000000 : ℝ)^6319
        have hw : |(4314718059/10000000000 : ℝ)|=(4314718059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(920753791/2500000000 : ℝ)|^8367 ≤ (3330575215543/12500000000000 : ℝ)^6319
        have hw : |(920753791/2500000000 : ℝ)|=(920753791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101052819/200000000 : ℝ)|^8367 ≤ (40497498263269/100000000000000 : ℝ)^6319
        have hw : |(101052819/200000000 : ℝ)|=(101052819/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s1_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1042417707/5000000000 : ℝ)*x 0 + (5018126041/10000000000 : ℝ)*x 1 + (1420907391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042417707/5000000000 : ℝ)^8367 ≤ (6271214252807/50000000000000 : ℝ)^6319 := by
    have hnat : (1042417707 : ℕ)^8367*50000000000000^6319 ≤ 6271214252807^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042417707 5000000000 6271214252807 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5018126041/10000000000 : ℝ)^8367 ≤ (20065801772843/50000000000000 : ℝ)^6319 := by
    have hnat : (5018126041 : ℕ)^8367*50000000000000^6319 ≤ 20065801772843^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018126041 10000000000 20065801772843 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1420907391/2500000000 : ℝ)^8367 ≤ (11831491981961/25000000000000 : ℝ)^6319 := by
    have hnat : (1420907391 : ℕ)^8367*25000000000000^6319 ≤ 11831491981961^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420907391 2500000000 11831491981961 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1042417707/5000000000 : ℝ), (5018126041/10000000000 : ℝ), (1420907391/2500000000 : ℝ)] ![(6271214252807/50000000000000 : ℝ), (20065801772843/50000000000000 : ℝ), (11831491981961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1042417707/5000000000 : ℝ)|^8367 ≤ (6271214252807/50000000000000 : ℝ)^6319
        have hw : |(-1042417707/5000000000 : ℝ)|=(1042417707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5018126041/10000000000 : ℝ)|^8367 ≤ (20065801772843/50000000000000 : ℝ)^6319
        have hw : |(5018126041/10000000000 : ℝ)|=(5018126041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1420907391/2500000000 : ℝ)|^8367 ≤ (11831491981961/25000000000000 : ℝ)^6319
        have hw : |(1420907391/2500000000 : ℝ)|=(1420907391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s1_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5241687589/10000000000 : ℝ)*x 0 + (-177793889/1000000000 : ℝ)*x 1 + (1420908027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241687589/10000000000 : ℝ)^8367 ≤ (5314485211709/12500000000000 : ℝ)^6319 := by
    have hnat : (5241687589 : ℕ)^8367*12500000000000^6319 ≤ 5314485211709^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241687589 10000000000 5314485211709 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177793889/1000000000 : ℝ)^8367 ≤ (10158122313039/100000000000000 : ℝ)^6319 := by
    have hnat : (177793889 : ℕ)^8367*100000000000000^6319 ≤ 10158122313039^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177793889 1000000000 10158122313039 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1420908027/2500000000 : ℝ)^8367 ≤ (9465199195303/20000000000000 : ℝ)^6319 := by
    have hnat : (1420908027 : ℕ)^8367*20000000000000^6319 ≤ 9465199195303^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420908027 2500000000 9465199195303 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241687589/10000000000 : ℝ), (-177793889/1000000000 : ℝ), (1420908027/2500000000 : ℝ)] ![(5314485211709/12500000000000 : ℝ), (10158122313039/100000000000000 : ℝ), (9465199195303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241687589/10000000000 : ℝ)|^8367 ≤ (5314485211709/12500000000000 : ℝ)^6319
        have hw : |(5241687589/10000000000 : ℝ)|=(5241687589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177793889/1000000000 : ℝ)|^8367 ≤ (10158122313039/100000000000000 : ℝ)^6319
        have hw : |(-177793889/1000000000 : ℝ)|=(177793889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1420908027/2500000000 : ℝ)|^8367 ≤ (9465199195303/20000000000000 : ℝ)^6319
        have hw : |(1420908027/2500000000 : ℝ)|=(1420908027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s1_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048337401/2000000000 : ℝ)*x 0 + (1136726649/2000000000 : ℝ)*x 1 + (-1777938063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048337401/2000000000 : ℝ)^8367 ≤ (42515875421553/100000000000000 : ℝ)^6319 := by
    have hnat : (1048337401 : ℕ)^8367*100000000000000^6319 ≤ 42515875421553^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048337401 2000000000 42515875421553 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136726649/2000000000 : ℝ)^8367 ≤ (2366300425621/5000000000000 : ℝ)^6319 := by
    have hnat : (1136726649 : ℕ)^8367*5000000000000^6319 ≤ 2366300425621^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136726649 2000000000 2366300425621 5000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1777938063/10000000000 : ℝ)^8367 ≤ (5079058028327/50000000000000 : ℝ)^6319 := by
    have hnat : (1777938063 : ℕ)^8367*50000000000000^6319 ≤ 5079058028327^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777938063 10000000000 5079058028327 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048337401/2000000000 : ℝ), (1136726649/2000000000 : ℝ), (-1777938063/10000000000 : ℝ)] ![(42515875421553/100000000000000 : ℝ), (2366300425621/5000000000000 : ℝ), (5079058028327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048337401/2000000000 : ℝ)|^8367 ≤ (42515875421553/100000000000000 : ℝ)^6319
        have hw : |(1048337401/2000000000 : ℝ)|=(1048337401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136726649/2000000000 : ℝ)|^8367 ≤ (2366300425621/5000000000000 : ℝ)^6319
        have hw : |(1136726649/2000000000 : ℝ)|=(1136726649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1777938063/10000000000 : ℝ)|^8367 ≤ (5079058028327/50000000000000 : ℝ)^6319
        have hw : |(-1777938063/10000000000 : ℝ)|=(1777938063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s1_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4316240599/10000000000 : ℝ)*x 0 + (5034170851/10000000000 : ℝ)*x 1 + (740369569/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316240599/10000000000 : ℝ)^8367 ≤ (1314930132807/4000000000000 : ℝ)^6319 := by
    have hnat : (4316240599 : ℕ)^8367*4000000000000^6319 ≤ 1314930132807^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316240599 10000000000 1314930132807 4000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5034170851/10000000000 : ℝ)^8367 ≤ (20150797236717/50000000000000 : ℝ)^6319 := by
    have hnat : (5034170851 : ℕ)^8367*50000000000000^6319 ≤ 20150797236717^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5034170851 10000000000 20150797236717 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (740369569/2000000000 : ℝ)^8367 ≤ (26825152183163/100000000000000 : ℝ)^6319 := by
    have hnat : (740369569 : ℕ)^8367*100000000000000^6319 ≤ 26825152183163^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740369569 2000000000 26825152183163 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316240599/10000000000 : ℝ), (5034170851/10000000000 : ℝ), (740369569/2000000000 : ℝ)] ![(1314930132807/4000000000000 : ℝ), (20150797236717/50000000000000 : ℝ), (26825152183163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316240599/10000000000 : ℝ)|^8367 ≤ (1314930132807/4000000000000 : ℝ)^6319
        have hw : |(4316240599/10000000000 : ℝ)|=(4316240599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5034170851/10000000000 : ℝ)|^8367 ≤ (20150797236717/50000000000000 : ℝ)^6319
        have hw : |(5034170851/10000000000 : ℝ)|=(5034170851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(740369569/2000000000 : ℝ)|^8367 ≤ (26825152183163/100000000000000 : ℝ)^6319
        have hw : |(740369569/2000000000 : ℝ)|=(740369569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5827/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10147/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (109/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (109/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (109/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (109/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (109/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (109/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (109/20000 : ℝ) ^ (4183/1024 : ℝ) ≤ (14164724841/25000000000000000000 : ℝ) := by
    have hpowers : (109/20000 : ℝ)^4183 ≤ (14164724841/25000000000000000000 : ℝ)^1024 := by
      have hnat : (109 : ℕ)^4183*25000000000000000000^1024 ≤ 14164724841^1024*20000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109 20000 14164724841 25000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (109/20000 : ℝ)) (X := (14164724841/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27693/100000 : ℝ) ^ (4183/1024 : ℝ) ≤ (527355227821862467/100000000000000000000 : ℝ) := by
    have hpowers : (27693/100000 : ℝ)^4183 ≤ (527355227821862467/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27693 : ℕ)^4183*100000000000000000000^1024 ≤ 527355227821862467^1024*100000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27693 100000 527355227821862467 100000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27693/100000 : ℝ)) (X := (527355227821862467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000014164724841/12500000000000000000 : ℝ) ≤ (400000000110961/400000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (12500000014164724841/12500000000000000000 : ℝ)^1024 ≤ (400000000110961/400000000000000 : ℝ)^4183 := by
      have hnat : (12500000014164724841 : ℕ)^1024*400000000000000^4183 ≤ 400000000110961^4183*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000014164724841 12500000000000000000 400000000110961 400000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000000110961/400000000000000 : ℝ)) (X := (12500000014164724841/12500000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100527355284480761831/100000000000000000000 : ℝ) ≤ (10012884049619521/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (100527355284480761831/100000000000000000000 : ℝ)^1024 ≤ (10012884049619521/10000000000000000 : ℝ)^4183 := by
      have hnat : (100527355284480761831 : ℕ)^1024*10000000000000000^4183 ≤ 10012884049619521^4183*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100527355284480761831 100000000000000000000 10012884049619521 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012884049619521/10000000000000000 : ℝ)) (X := (100527355284480761831/100000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50527355227821862467/50000000000000000000 : ℝ) ≤ (10025768096465017/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50527355227821862467/50000000000000000000 : ℝ)^1024 ≤ (10025768096465017/10000000000000000 : ℝ)^4183 := by
      have hnat : (50527355227821862467 : ℕ)^1024*10000000000000000^4183 ≤ 10025768096465017^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50527355227821862467 50000000000000000000 10025768096465017 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025768096465017/10000000000000000 : ℝ)) (X := (50527355227821862467/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14164724841/25000000000000000000 : ℝ) ≤ ((13573297823212382003/13574000000000000000 : ℝ)+2*(1610505855687/339350000000000 : ℝ)*(109/20000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (13573297823212382003/13574000000000000000 : ℝ)+2*(1610505855687/339350000000000 : ℝ)*(109/20000 : ℝ)=(400000000110961/400000000000000 : ℝ) by norm_num, show 1+2*(14164724841/25000000000000000000 : ℝ)=(12500000014164724841/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(527355227821862467/100000000000000000000 : ℝ)+(14164724841/25000000000000000000 : ℝ) ≤ ((13573297823212382003/13574000000000000000 : ℝ)+(1610505855687/339350000000000 : ℝ)*((27693/100000 : ℝ)+(109/20000 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (13573297823212382003/13574000000000000000 : ℝ)+(1610505855687/339350000000000 : ℝ)*((27693/100000 : ℝ)+(109/20000 : ℝ))=(10012884049619521/10000000000000000 : ℝ) by norm_num, show 1+(527355227821862467/100000000000000000000 : ℝ)+(14164724841/25000000000000000000 : ℝ)=(100527355284480761831/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(527355227821862467/100000000000000000000 : ℝ) ≤ ((13573297823212382003/13574000000000000000 : ℝ)+2*(1610505855687/339350000000000 : ℝ)*(27693/100000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (13573297823212382003/13574000000000000000 : ℝ)+2*(1610505855687/339350000000000 : ℝ)*(27693/100000 : ℝ)=(10025768096465017/10000000000000000 : ℝ) by norm_num, show 1+2*(527355227821862467/100000000000000000000 : ℝ)=(50527355227821862467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13573297823212382003/13574000000000000000 : ℝ)*(X 1 0+X 2 0)+(1610505855687/339350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (109/20000 : ℝ)) (hi := (27693/100000 : ℝ)) (c := (13573297823212382003/13574000000000000000 : ℝ)) (alpha := (1610505855687/339350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13573297823212382003/13574000000000000000 : ℝ)*(X 0 1+X 2 1)+(1610505855687/339350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (109/20000 : ℝ)) (hi := (27693/100000 : ℝ)) (c := (13573297823212382003/13574000000000000000 : ℝ)) (alpha := (1610505855687/339350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13573297823212382003/13574000000000000000 : ℝ)*(X 0 2+X 1 2)+(1610505855687/339350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (109/20000 : ℝ)) (hi := (27693/100000 : ℝ)) (c := (13573297823212382003/13574000000000000000 : ℝ)) (alpha := (1610505855687/339350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1042034573/5000000000 : ℝ)*X 0 0+(711630071/1250000000 : ℝ)*X 0 1+(125222461/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5417368349/10000000000 : ℝ)*X 1 0+(-1226336811/5000000000 : ℝ)*X 1 1+(2504448743/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417370457/10000000000 : ℝ)*X 2 0+(2504447753/5000000000 : ℝ)*X 2 1+(-153292087/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314718059/10000000000 : ℝ)*X 0 0+(920753791/2500000000 : ℝ)*X 0 1+(101052819/200000000 : ℝ)*X 0 2+(4314718059/10000000000 : ℝ)*X 1 0+(920753791/2500000000 : ℝ)*X 1 1+(101052819/200000000 : ℝ)*X 1 2+(4314718059/10000000000 : ℝ)*X 2 0+(920753791/2500000000 : ℝ)*X 2 1+(101052819/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1042417707/5000000000 : ℝ)*X 0 0+(5018126041/10000000000 : ℝ)*X 0 1+(1420907391/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241687589/10000000000 : ℝ)*X 1 0+(-177793889/1000000000 : ℝ)*X 1 1+(1420908027/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1048337401/2000000000 : ℝ)*X 2 0+(1136726649/2000000000 : ℝ)*X 2 1+(-1777938063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316240599/10000000000 : ℝ)*X 0 0+(5034170851/10000000000 : ℝ)*X 0 1+(740369569/2000000000 : ℝ)*X 0 2+(4316240599/10000000000 : ℝ)*X 1 0+(5034170851/10000000000 : ℝ)*X 1 1+(740369569/2000000000 : ℝ)*X 1 2+(4316240599/10000000000 : ℝ)*X 2 0+(5034170851/10000000000 : ℝ)*X 2 1+(740369569/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (875878481784588854885530623/339350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3821211/1250000000000 : ℝ)*(base1) + (215826533/25000000000000 : ℝ)*(base19) + (910501467/100000000000000 : ℝ)*(base23) + (214963413/100000000000000 : ℝ)*(base37) + (254008511/100000000000000 : ℝ)*(lower2) + (1095905191849847/100000000000000 : ℝ)*(major0) + (1095905191849847/100000000000000 : ℝ)*(major1) + (1095905191849847/100000000000000 : ℝ)*(major2) + (730842146077369/50000000000000 : ℝ)*(sp0) + (730842586574009/50000000000000 : ℝ)*(sp1) + (146168350102659/10000000000000 : ℝ)*(sp2) + (365061870275163/50000000000000 : ℝ)*(sp3) + (512499073/25000000000000 : ℝ)*(sp4) + (812463047/50000000000000 : ℝ)*(sp6) + (365062130605309/50000000000000 : ℝ)*(f.failure) + (29233720729083/2000000000000 : ℝ)*(f.sum) + (1967635717081/4241875000000000000000000000 : ℝ)*base65 + (294443625211336459/1357400000000000000000000000000000 : ℝ)*base68 + (6773504523622536459/1357400000000000000000000000000000 : ℝ)*base70 + (1094007040958263541/1357400000000000000000000000000000 : ℝ)*base71 + (12087032252401/16967500000000000000000000000 : ℝ)*base74 + (5901642892938536459/1357400000000000000000000000000000 : ℝ)*base76 + (857089609194936459/1357400000000000000000000000000000 : ℝ)*base78 + (10010507062374936459/1357400000000000000000000000000000 : ℝ)*base80 + (29021568309963/8483750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (37934259/5000000000000000000000 : ℝ)*base90 + (37934259/5000000000000000000000 : ℝ)*base92 + (37934259/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (332665731208318383817241577/67870000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2396909117/100000000000000 : ℝ)*(base19) + (1486452829/50000000000000 : ℝ)*(base23) + (72541269/25000000000000 : ℝ)*(upper2) + (549285869/100000000000000 : ℝ)*(upper3) + (274719411/100000000000000 : ℝ)*(upper5) + (112659337914047/10000000000000 : ℝ)*(major0) + (112659337914047/10000000000000 : ℝ)*(major1) + (112659337914047/10000000000000 : ℝ)*(major2) + (1607250489/12500000000000 : ℝ)*(sp1) + (18521799267/100000000000000 : ℝ)*(sp2) + (375654240250687/25000000000000 : ℝ)*(sp4) + (751300853044859/50000000000000 : ℝ)*(sp5) + (751297733148911/50000000000000 : ℝ)*(sp6) + (375284816947199/50000000000000 : ℝ)*(sp7) + (375284816947199/50000000000000 : ℝ)*(f.failure) + (375654240250687/25000000000000 : ℝ)*(f.sum) + (216764942323/3393500000000000000000000000 : ℝ)*base65 + (567862522345583859/135740000000000000000000000000000 : ℝ)*base68 + (18132376490576141/135740000000000000000000000000000 : ℝ)*base69 + (432853177497176141/135740000000000000000000000000000 : ℝ)*base71 + (9565690009331/3393500000000000000000000000 : ℝ)*base74 + (489097386661616141/135740000000000000000000000000000 : ℝ)*base75 + (85560542802683859/135740000000000000000000000000000 : ℝ)*base78 + (994596390304656141/135740000000000000000000000000000 : ℝ)*base79 + (490660550167/848375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (15205649/5000000000000000000000 : ℝ)*base90 + (15205649/5000000000000000000000 : ℝ)*base92 + (15205649/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1174_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5827/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10147/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1174_s2_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135602023/10000000000 : ℝ)*x 0 + (5504829/10000000 : ℝ)*x 1 + (1032862019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135602023/10000000000 : ℝ)^8367 ≤ (12948413997557/100000000000000 : ℝ)^6319 := by
    have hnat : (2135602023 : ℕ)^8367*100000000000000^6319 ≤ 12948413997557^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135602023 10000000000 12948413997557 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504829/10000000 : ℝ)^8367 ≤ (45364738576193/100000000000000 : ℝ)^6319 := by
    have hnat : (5504829 : ℕ)^8367*100000000000000^6319 ≤ 45364738576193^6319*10000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504829 10000000 45364738576193 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032862019/2000000000 : ℝ)^8367 ≤ (41686847416031/100000000000000 : ℝ)^6319 := by
    have hnat : (1032862019 : ℕ)^8367*100000000000000^6319 ≤ 41686847416031^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032862019 2000000000 41686847416031 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135602023/10000000000 : ℝ), (5504829/10000000 : ℝ), (1032862019/2000000000 : ℝ)] ![(12948413997557/100000000000000 : ℝ), (45364738576193/100000000000000 : ℝ), (41686847416031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135602023/10000000000 : ℝ)|^8367 ≤ (12948413997557/100000000000000 : ℝ)^6319
        have hw : |(-2135602023/10000000000 : ℝ)|=(2135602023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504829/10000000 : ℝ)|^8367 ≤ (45364738576193/100000000000000 : ℝ)^6319
        have hw : |(5504829/10000000 : ℝ)|=(5504829/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032862019/2000000000 : ℝ)|^8367 ≤ (41686847416031/100000000000000 : ℝ)^6319
        have hw : |(1032862019/2000000000 : ℝ)|=(1032862019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s2_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686251089/5000000000 : ℝ)*x 0 + (-578105113/2500000000 : ℝ)*x 1 + (516431313/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686251089/5000000000 : ℝ)^8367 ≤ (43926471578103/100000000000000 : ℝ)^6319 := by
    have hnat : (2686251089 : ℕ)^8367*100000000000000^6319 ≤ 43926471578103^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686251089 5000000000 43926471578103 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (578105113/2500000000 : ℝ)^8367 ≤ (899165534669/6250000000000 : ℝ)^6319 := by
    have hnat : (578105113 : ℕ)^8367*6250000000000^6319 ≤ 899165534669^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578105113 2500000000 899165534669 6250000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516431313/1000000000 : ℝ)^8367 ≤ (41686879854989/100000000000000 : ℝ)^6319 := by
    have hnat : (516431313 : ℕ)^8367*100000000000000^6319 ≤ 41686879854989^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516431313 1000000000 41686879854989 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686251089/5000000000 : ℝ), (-578105113/2500000000 : ℝ), (516431313/1000000000 : ℝ)] ![(43926471578103/100000000000000 : ℝ), (899165534669/6250000000000 : ℝ), (41686879854989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686251089/5000000000 : ℝ)|^8367 ≤ (43926471578103/100000000000000 : ℝ)^6319
        have hw : |(2686251089/5000000000 : ℝ)|=(2686251089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-578105113/2500000000 : ℝ)|^8367 ≤ (899165534669/6250000000000 : ℝ)^6319
        have hw : |(-578105113/2500000000 : ℝ)|=(578105113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516431313/1000000000 : ℝ)|^8367 ≤ (41686879854989/100000000000000 : ℝ)^6319
        have hw : |(516431313/1000000000 : ℝ)|=(516431313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s2_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5372502937/10000000000 : ℝ)*x 0 + (1032862389/2000000000 : ℝ)*x 1 + (-231242099/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372502937/10000000000 : ℝ)^8367 ≤ (5490809974387/12500000000000 : ℝ)^6319 := by
    have hnat : (5372502937 : ℕ)^8367*12500000000000^6319 ≤ 5490809974387^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372502937 10000000000 5490809974387 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032862389/2000000000 : ℝ)^8367 ≤ (20843433594683/50000000000000 : ℝ)^6319 := by
    have hnat : (1032862389 : ℕ)^8367*50000000000000^6319 ≤ 20843433594683^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032862389 2000000000 20843433594683 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231242099/1000000000 : ℝ)^8367 ≤ (14386652986671/100000000000000 : ℝ)^6319 := by
    have hnat : (231242099 : ℕ)^8367*100000000000000^6319 ≤ 14386652986671^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231242099 1000000000 14386652986671 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372502937/10000000000 : ℝ), (1032862389/2000000000 : ℝ), (-231242099/1000000000 : ℝ)] ![(5490809974387/12500000000000 : ℝ), (20843433594683/50000000000000 : ℝ), (14386652986671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372502937/10000000000 : ℝ)|^8367 ≤ (5490809974387/12500000000000 : ℝ)^6319
        have hw : |(5372502937/10000000000 : ℝ)|=(5372502937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032862389/2000000000 : ℝ)|^8367 ≤ (20843433594683/50000000000000 : ℝ)^6319
        have hw : |(1032862389/2000000000 : ℝ)|=(1032862389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231242099/1000000000 : ℝ)|^8367 ≤ (14386652986671/100000000000000 : ℝ)^6319
        have hw : |(-231242099/1000000000 : ℝ)|=(231242099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s2_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350147007/10000000000 : ℝ)*x 0 + (804486331/2000000000 : ℝ)*x 1 + (117603383/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350147007/10000000000 : ℝ)^8367 ≤ (33215620218713/100000000000000 : ℝ)^6319 := by
    have hnat : (4350147007 : ℕ)^8367*100000000000000^6319 ≤ 33215620218713^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350147007 10000000000 33215620218713 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804486331/2000000000 : ℝ)^8367 ≤ (29943509190491/100000000000000 : ℝ)^6319 := by
    have hnat : (804486331 : ℕ)^8367*100000000000000^6319 ≤ 29943509190491^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804486331 2000000000 29943509190491 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117603383/250000000 : ℝ)^8367 ≤ (36840870572111/100000000000000 : ℝ)^6319 := by
    have hnat : (117603383 : ℕ)^8367*100000000000000^6319 ≤ 36840870572111^6319*250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117603383 250000000 36840870572111 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350147007/10000000000 : ℝ), (804486331/2000000000 : ℝ), (117603383/250000000 : ℝ)] ![(33215620218713/100000000000000 : ℝ), (29943509190491/100000000000000 : ℝ), (36840870572111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350147007/10000000000 : ℝ)|^8367 ≤ (33215620218713/100000000000000 : ℝ)^6319
        have hw : |(4350147007/10000000000 : ℝ)|=(4350147007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804486331/2000000000 : ℝ)|^8367 ≤ (29943509190491/100000000000000 : ℝ)^6319
        have hw : |(804486331/2000000000 : ℝ)|=(804486331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117603383/250000000 : ℝ)|^8367 ≤ (36840870572111/100000000000000 : ℝ)^6319
        have hw : |(117603383/250000000 : ℝ)|=(117603383/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s2_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067847699/5000000000 : ℝ)*x 0 + (5166606897/10000000000 : ℝ)*x 1 + (2751255111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067847699/5000000000 : ℝ)^8367 ≤ (809322727197/6250000000000 : ℝ)^6319 := by
    have hnat : (1067847699 : ℕ)^8367*6250000000000^6319 ≤ 809322727197^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067847699 5000000000 809322727197 6250000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5166606897/10000000000 : ℝ)^8367 ≤ (41711398066769/100000000000000 : ℝ)^6319 := by
    have hnat : (5166606897 : ℕ)^8367*100000000000000^6319 ≤ 41711398066769^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166606897 10000000000 41711398066769 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751255111/5000000000 : ℝ)^8367 ≤ (45339438285227/100000000000000 : ℝ)^6319 := by
    have hnat : (2751255111 : ℕ)^8367*100000000000000^6319 ≤ 45339438285227^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751255111 5000000000 45339438285227 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067847699/5000000000 : ℝ), (5166606897/10000000000 : ℝ), (2751255111/5000000000 : ℝ)] ![(809322727197/6250000000000 : ℝ), (41711398066769/100000000000000 : ℝ), (45339438285227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067847699/5000000000 : ℝ)|^8367 ≤ (809322727197/6250000000000 : ℝ)^6319
        have hw : |(-1067847699/5000000000 : ℝ)|=(1067847699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5166606897/10000000000 : ℝ)|^8367 ≤ (41711398066769/100000000000000 : ℝ)^6319
        have hw : |(5166606897/10000000000 : ℝ)|=(5166606897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751255111/5000000000 : ℝ)|^8367 ≤ (45339438285227/100000000000000 : ℝ)^6319
        have hw : |(2751255111/5000000000 : ℝ)|=(2751255111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s2_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642960421/5000000000 : ℝ)*x 0 + (-123388881/625000000 : ℝ)*x 1 + (2751255111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642960421/5000000000 : ℝ)^8367 ≤ (21495796087939/50000000000000 : ℝ)^6319 := by
    have hnat : (2642960421 : ℕ)^8367*50000000000000^6319 ≤ 21495796087939^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642960421 5000000000 21495796087939 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123388881/625000000 : ℝ)^8367 ≤ (11668969519337/100000000000000 : ℝ)^6319 := by
    have hnat : (123388881 : ℕ)^8367*100000000000000^6319 ≤ 11668969519337^6319*625000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123388881 625000000 11668969519337 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751255111/5000000000 : ℝ)^8367 ≤ (45339438285227/100000000000000 : ℝ)^6319 := by
    have hnat : (2751255111 : ℕ)^8367*100000000000000^6319 ≤ 45339438285227^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751255111 5000000000 45339438285227 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642960421/5000000000 : ℝ), (-123388881/625000000 : ℝ), (2751255111/5000000000 : ℝ)] ![(21495796087939/50000000000000 : ℝ), (11668969519337/100000000000000 : ℝ), (45339438285227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642960421/5000000000 : ℝ)|^8367 ≤ (21495796087939/50000000000000 : ℝ)^6319
        have hw : |(2642960421/5000000000 : ℝ)|=(2642960421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123388881/625000000 : ℝ)|^8367 ≤ (11668969519337/100000000000000 : ℝ)^6319
        have hw : |(-123388881/625000000 : ℝ)|=(123388881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751255111/5000000000 : ℝ)|^8367 ≤ (45339438285227/100000000000000 : ℝ)^6319
        have hw : |(2751255111/5000000000 : ℝ)|=(2751255111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s2_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (264296049/500000000 : ℝ)*x 0 + (5502510221/10000000000 : ℝ)*x 1 + (-493555477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264296049/500000000 : ℝ)^8367 ≤ (42991593662031/100000000000000 : ℝ)^6319 := by
    have hnat : (264296049 : ℕ)^8367*100000000000000^6319 ≤ 42991593662031^6319*500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264296049 500000000 42991593662031 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502510221/10000000000 : ℝ)^8367 ≤ (45339438274317/100000000000000 : ℝ)^6319 := by
    have hnat : (5502510221 : ℕ)^8367*100000000000000^6319 ≤ 45339438274317^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502510221 10000000000 45339438274317 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493555477/2500000000 : ℝ)^8367 ≤ (2917242011997/25000000000000 : ℝ)^6319 := by
    have hnat : (493555477 : ℕ)^8367*25000000000000^6319 ≤ 2917242011997^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493555477 2500000000 2917242011997 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264296049/500000000 : ℝ), (5502510221/10000000000 : ℝ), (-493555477/2500000000 : ℝ)] ![(42991593662031/100000000000000 : ℝ), (45339438274317/100000000000000 : ℝ), (2917242011997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264296049/500000000 : ℝ)|^8367 ≤ (42991593662031/100000000000000 : ℝ)^6319
        have hw : |(264296049/500000000 : ℝ)|=(264296049/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502510221/10000000000 : ℝ)|^8367 ≤ (45339438274317/100000000000000 : ℝ)^6319
        have hw : |(5502510221/10000000000 : ℝ)|=(5502510221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493555477/2500000000 : ℝ)|^8367 ≤ (2917242011997/25000000000000 : ℝ)^6319
        have hw : |(-493555477/2500000000 : ℝ)|=(493555477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s2_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175167833/5000000000 : ℝ)*x 0 + (4699539713/10000000000 : ℝ)*x 1 + (4027071317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175167833/5000000000 : ℝ)^8367 ≤ (4152190951597/12500000000000 : ℝ)^6319 := by
    have hnat : (2175167833 : ℕ)^8367*12500000000000^6319 ≤ 4152190951597^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175167833 5000000000 4152190951597 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4699539713/10000000000 : ℝ)^8367 ≤ (3679322247083/10000000000000 : ℝ)^6319 := by
    have hnat : (4699539713 : ℕ)^8367*10000000000000^6319 ≤ 3679322247083^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4699539713 10000000000 3679322247083 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027071317/10000000000 : ℝ)^8367 ≤ (7497312475797/25000000000000 : ℝ)^6319 := by
    have hnat : (4027071317 : ℕ)^8367*25000000000000^6319 ≤ 7497312475797^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027071317 10000000000 7497312475797 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175167833/5000000000 : ℝ), (4699539713/10000000000 : ℝ), (4027071317/10000000000 : ℝ)] ![(4152190951597/12500000000000 : ℝ), (3679322247083/10000000000000 : ℝ), (7497312475797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175167833/5000000000 : ℝ)|^8367 ≤ (4152190951597/12500000000000 : ℝ)^6319
        have hw : |(2175167833/5000000000 : ℝ)|=(2175167833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4699539713/10000000000 : ℝ)|^8367 ≤ (3679322247083/10000000000000 : ℝ)^6319
        have hw : |(4699539713/10000000000 : ℝ)|=(4699539713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027071317/10000000000 : ℝ)|^8367 ≤ (7497312475797/25000000000000 : ℝ)^6319
        have hw : |(4027071317/10000000000 : ℝ)|=(4027071317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10147/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5827/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2303/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16409/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10147/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5827/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10147/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5827/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10147/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5827/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10147/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5827/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10147/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5827/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10147/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5827/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5827/100000 : ℝ) ^ (4183/1024 : ℝ) ≤ (905505564966317/100000000000000000000 : ℝ) := by
    have hpowers : (5827/100000 : ℝ)^4183 ≤ (905505564966317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5827 : ℕ)^4183*100000000000000000000^1024 ≤ 905505564966317^1024*100000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5827 100000 905505564966317 100000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5827/100000 : ℝ)) (X := (905505564966317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10147/50000 : ℝ) ^ (4183/1024 : ℝ) ≤ (14812348821792171/10000000000000000000 : ℝ) := by
    have hpowers : (10147/50000 : ℝ)^4183 ≤ (14812348821792171/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10147 : ℕ)^4183*10000000000000000000^1024 ≤ 14812348821792171^1024*50000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10147 50000 14812348821792171 10000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10147/50000 : ℝ)) (X := (14812348821792171/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000905505564966317/50000000000000000000 : ℝ) ≤ (5000022166659283/5000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50000905505564966317/50000000000000000000 : ℝ)^1024 ≤ (5000022166659283/5000000000000000 : ℝ)^4183 := by
      have hnat : (50000905505564966317 : ℕ)^1024*5000000000000000^4183 ≤ 5000022166659283^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000905505564966317 50000000000000000000 5000022166659283 5000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000022166659283/5000000000000000 : ℝ)) (X := (50000905505564966317/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100149028993782888027/100000000000000000000 : ℝ) ≤ (1000364618427317/1000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (100149028993782888027/100000000000000000000 : ℝ)^1024 ≤ (1000364618427317/1000000000000000 : ℝ)^4183 := by
      have hnat : (100149028993782888027 : ℕ)^1024*1000000000000000^4183 ≤ 1000364618427317^4183*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100149028993782888027 100000000000000000000 1000364618427317 1000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000364618427317/1000000000000000 : ℝ)) (X := (100149028993782888027/100000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5014812348821792171/5000000000000000000 : ℝ) ≤ (5003624017613887/5000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (5014812348821792171/5000000000000000000 : ℝ)^1024 ≤ (5003624017613887/5000000000000000 : ℝ)^4183 := by
      have hnat : (5014812348821792171 : ℕ)^1024*5000000000000000^4183 ≤ 5003624017613887^4183*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5014812348821792171 5000000000000000000 5003624017613887 5000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003624017613887/5000000000000000 : ℝ)) (X := (5014812348821792171/5000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(905505564966317/100000000000000000000 : ℝ) ≤ ((72314332699547369653/72335000000000000000 : ℝ)+2*(900462738651/361675000000000 : ℝ)*(5827/100000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (72314332699547369653/72335000000000000000 : ℝ)+2*(900462738651/361675000000000 : ℝ)*(5827/100000 : ℝ)=(5000022166659283/5000000000000000 : ℝ) by norm_num, show 1+2*(905505564966317/100000000000000000000 : ℝ)=(50000905505564966317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14812348821792171/10000000000000000000 : ℝ)+(905505564966317/100000000000000000000 : ℝ) ≤ ((72314332699547369653/72335000000000000000 : ℝ)+(900462738651/361675000000000 : ℝ)*((10147/50000 : ℝ)+(5827/100000 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (72314332699547369653/72335000000000000000 : ℝ)+(900462738651/361675000000000 : ℝ)*((10147/50000 : ℝ)+(5827/100000 : ℝ))=(1000364618427317/1000000000000000 : ℝ) by norm_num, show 1+(14812348821792171/10000000000000000000 : ℝ)+(905505564966317/100000000000000000000 : ℝ)=(100149028993782888027/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14812348821792171/10000000000000000000 : ℝ) ≤ ((72314332699547369653/72335000000000000000 : ℝ)+2*(900462738651/361675000000000 : ℝ)*(10147/50000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (72314332699547369653/72335000000000000000 : ℝ)+2*(900462738651/361675000000000 : ℝ)*(10147/50000 : ℝ)=(5003624017613887/5000000000000000 : ℝ) by norm_num, show 1+2*(14812348821792171/10000000000000000000 : ℝ)=(5014812348821792171/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72314332699547369653/72335000000000000000 : ℝ)*(X 1 0+X 2 0)+(900462738651/361675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (5827/100000 : ℝ)) (hi := (10147/50000 : ℝ)) (c := (72314332699547369653/72335000000000000000 : ℝ)) (alpha := (900462738651/361675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72314332699547369653/72335000000000000000 : ℝ)*(X 0 1+X 2 1)+(900462738651/361675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (5827/100000 : ℝ)) (hi := (10147/50000 : ℝ)) (c := (72314332699547369653/72335000000000000000 : ℝ)) (alpha := (900462738651/361675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72314332699547369653/72335000000000000000 : ℝ)*(X 0 2+X 1 2)+(900462738651/361675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (5827/100000 : ℝ)) (hi := (10147/50000 : ℝ)) (c := (72314332699547369653/72335000000000000000 : ℝ)) (alpha := (900462738651/361675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2135602023/10000000000 : ℝ)*X 0 0+(5504829/10000000 : ℝ)*X 0 1+(1032862019/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686251089/5000000000 : ℝ)*X 1 0+(-578105113/2500000000 : ℝ)*X 1 1+(516431313/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372502937/10000000000 : ℝ)*X 2 0+(1032862389/2000000000 : ℝ)*X 2 1+(-231242099/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350147007/10000000000 : ℝ)*X 0 0+(804486331/2000000000 : ℝ)*X 0 1+(117603383/250000000 : ℝ)*X 0 2+(4350147007/10000000000 : ℝ)*X 1 0+(804486331/2000000000 : ℝ)*X 1 1+(117603383/250000000 : ℝ)*X 1 2+(4350147007/10000000000 : ℝ)*X 2 0+(804486331/2000000000 : ℝ)*X 2 1+(117603383/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1067847699/5000000000 : ℝ)*X 0 0+(5166606897/10000000000 : ℝ)*X 0 1+(2751255111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642960421/5000000000 : ℝ)*X 1 0+(-123388881/625000000 : ℝ)*X 1 1+(2751255111/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264296049/500000000 : ℝ)*X 2 0+(5502510221/10000000000 : ℝ)*X 2 1+(-493555477/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175167833/5000000000 : ℝ)*X 0 0+(4699539713/10000000000 : ℝ)*X 0 1+(4027071317/10000000000 : ℝ)*X 0 2+(2175167833/5000000000 : ℝ)*X 1 0+(4699539713/10000000000 : ℝ)*X 1 1+(4027071317/10000000000 : ℝ)*X 1 2+(2175167833/5000000000 : ℝ)*X 2 0+(4699539713/10000000000 : ℝ)*X 2 1+(4027071317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41018785753475613511255842633/3616750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1645510899/100000000000000 : ℝ)*(base19) + (1648440477/100000000000000 : ℝ)*(base23) + (148178067/25000000000000 : ℝ)*(upper3) + (110663231/50000000000000 : ℝ)*(upper4) + (674123/4000000000000 : ℝ)*(upper5) + (275231541438139/12500000000000 : ℝ)*(major0) + (275231541438139/12500000000000 : ℝ)*(major1) + (2201852331505113/100000000000000 : ℝ)*(major2) + (367091645584189/12500000000000 : ℝ)*(sp0) + (293676387614669/10000000000000 : ℝ)*(sp1) + (367095484152139/12500000000000 : ℝ)*(sp2) + (733461363225017/50000000000000 : ℝ)*(sp3) + (32356984077/100000000000000 : ℝ)*(sp4) + (16036857981/100000000000000 : ℝ)*(sp7) + (91683672706751/6250000000000 : ℝ)*(f.failure) + (2936765521657589/100000000000000 : ℝ)*(f.sum) + (1420040004617/1808375000000000000000000000 : ℝ)*base65 + (180179724287029233/904187500000000000000000000000000 : ℝ)*base68 + (63507638058454435789/7233500000000000000000000000000000 : ℝ)*base69 + (2610759247149779233/904187500000000000000000000000000 : ℝ)*base72 + (78074663679909/14467000000000000000000000000 : ℝ)*base73 + (43336292970893435789/7233500000000000000000000000000000 : ℝ)*base75 + (1357661697952195767/904187500000000000000000000000000 : ℝ)*base77 + (4912138464805633267/904187500000000000000000000000000 : ℝ)*base79 + (421381441514353/72335000000000000000000000000 : ℝ)*base81 + (6929199/625000000000000000000 : ℝ)*base89 + (6929199/625000000000000000000 : ℝ)*base91 + (679199/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4308313280700677641904782509/904187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1196126261/100000000000000 : ℝ)*(base19) + (1349251819/100000000000000 : ℝ)*(base23) + (15744877/100000000000000 : ℝ)*(upper2) + (146219/97656250000 : ℝ)*(upper3) + (103561503/100000000000000 : ℝ)*(upper5) + (558013236013451/25000000000000 : ℝ)*(major0) + (558013236013451/25000000000000 : ℝ)*(major1) + (558013236013451/25000000000000 : ℝ)*(major2) + (2869837709/25000000000000 : ℝ)*(sp1) + (14264243533/100000000000000 : ℝ)*(sp2) + (2977046429916657/100000000000000 : ℝ)*(sp4) + (74425843860989/2500000000000 : ℝ)*(sp5) + (595406163284261/20000000000000 : ℝ)*(sp6) + (1487059299362783/100000000000000 : ℝ)*(sp7) + (1487059299362783/100000000000000 : ℝ)*(f.failure) + (2977046429916657/100000000000000 : ℝ)*(f.sum) + (4365523287787/9041875000000000000000000000 : ℝ)*base65 + (283954729705402503/1808375000000000000000000000000000 : ℝ)*base67 + (3287727774971972497/1808375000000000000000000000000000 : ℝ)*base70 + (1652055160647152503/1808375000000000000000000000000000 : ℝ)*base71 + (329688468237871/72335000000000000000000000000 : ℝ)*base73 + (5569700176119722497/1808375000000000000000000000000000 : ℝ)*base76 + (291595318569222497/1808375000000000000000000000000000 : ℝ)*base78 + (3466934670467972497/1808375000000000000000000000000000 : ℝ)*base80 + (103843989895281/72335000000000000000000000000 : ℝ)*base81 + (16623567/10000000000000000000000 : ℝ)*base89 + (16623567/10000000000000000000000 : ℝ)*base91 + (16623567/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1174_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10147/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5827/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16409/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1174_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16409/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1174_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1174_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1174_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16409/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1174_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

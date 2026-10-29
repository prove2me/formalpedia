-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1721_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:00:11.194778+00:00
-- url     : https://prove2.me/submissions/2328752f-ec1b-41de-b5c6-07027a916417

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
theorem support_rectangle_w1721_s0_0 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1304825387/10000000000 : ℝ)*x 0 + (5676385039/10000000000 : ℝ)*x 1 + (2485745299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1304825387/10000000000 : ℝ)^5391 ≤ (4046987799009/50000000000000 : ℝ)^4367 := by
    have hnat : (1304825387 : ℕ)^5391*50000000000000^4367 ≤ 4046987799009^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304825387 10000000000 4046987799009 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5676385039/10000000000 : ℝ)^5391 ≤ (2485279070663/5000000000000 : ℝ)^4367 := by
    have hnat : (5676385039 : ℕ)^5391*5000000000000^4367 ≤ 2485279070663^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676385039 10000000000 2485279070663 5000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2485745299/5000000000 : ℝ)^5391 ≤ (10550110743319/25000000000000 : ℝ)^4367 := by
    have hnat : (2485745299 : ℕ)^5391*25000000000000^4367 ≤ 10550110743319^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2485745299 5000000000 10550110743319 25000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1304825387/10000000000 : ℝ), (5676385039/10000000000 : ℝ), (2485745299/5000000000 : ℝ)] ![(4046987799009/50000000000000 : ℝ), (2485279070663/5000000000000 : ℝ), (10550110743319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1304825387/10000000000 : ℝ)|^5391 ≤ (4046987799009/50000000000000 : ℝ)^4367
        have hw : |(-1304825387/10000000000 : ℝ)|=(1304825387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5676385039/10000000000 : ℝ)|^5391 ≤ (2485279070663/5000000000000 : ℝ)^4367
        have hw : |(5676385039/10000000000 : ℝ)|=(5676385039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2485745299/5000000000 : ℝ)|^5391 ≤ (10550110743319/25000000000000 : ℝ)^4367
        have hw : |(2485745299/5000000000 : ℝ)|=(2485745299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s0_1 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674587203/1250000000 : ℝ)*x 0 + (-168519349/1000000000 : ℝ)*x 1 + (4971490019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674587203/1250000000 : ℝ)^5391 ≤ (46699893883937/100000000000000 : ℝ)^4367 := by
    have hnat : (674587203 : ℕ)^5391*100000000000000^4367 ≤ 46699893883937^4367*1250000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674587203 1250000000 46699893883937 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168519349/1000000000 : ℝ)^5391 ≤ (2219933838149/20000000000000 : ℝ)^4367 := by
    have hnat : (168519349 : ℕ)^5391*20000000000000^4367 ≤ 2219933838149^4367*1000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168519349 1000000000 2219933838149 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4971490019/10000000000 : ℝ)^5391 ≤ (42200436905981/100000000000000 : ℝ)^4367 := by
    have hnat : (4971490019 : ℕ)^5391*100000000000000^4367 ≤ 42200436905981^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971490019 10000000000 42200436905981 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674587203/1250000000 : ℝ), (-168519349/1000000000 : ℝ), (4971490019/10000000000 : ℝ)] ![(46699893883937/100000000000000 : ℝ), (2219933838149/20000000000000 : ℝ), (42200436905981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674587203/1250000000 : ℝ)|^5391 ≤ (46699893883937/100000000000000 : ℝ)^4367
        have hw : |(674587203/1250000000 : ℝ)|=(674587203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168519349/1000000000 : ℝ)|^5391 ≤ (2219933838149/20000000000000 : ℝ)^4367
        have hw : |(-168519349/1000000000 : ℝ)|=(168519349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4971490019/10000000000 : ℝ)|^5391 ≤ (42200436905981/100000000000000 : ℝ)^4367
        have hw : |(4971490019/10000000000 : ℝ)|=(4971490019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s0_2 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698348283/5000000000 : ℝ)*x 0 + (1242872657/2500000000 : ℝ)*x 1 + (-105324631/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698348283/5000000000 : ℝ)^5391 ≤ (1867995303273/4000000000000 : ℝ)^4367 := by
    have hnat : (2698348283 : ℕ)^5391*4000000000000^4367 ≤ 1867995303273^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698348283 5000000000 1867995303273 4000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1242872657/2500000000 : ℝ)^5391 ≤ (42200443287643/100000000000000 : ℝ)^4367 := by
    have hnat : (1242872657 : ℕ)^5391*100000000000000^4367 ≤ 42200443287643^4367*2500000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242872657 2500000000 42200443287643 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105324631/625000000 : ℝ)^5391 ≤ (11099674118159/100000000000000 : ℝ)^4367 := by
    have hnat : (105324631 : ℕ)^5391*100000000000000^4367 ≤ 11099674118159^4367*625000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105324631 625000000 11099674118159 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698348283/5000000000 : ℝ), (1242872657/2500000000 : ℝ), (-105324631/625000000 : ℝ)] ![(1867995303273/4000000000000 : ℝ), (42200443287643/100000000000000 : ℝ), (11099674118159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698348283/5000000000 : ℝ)|^5391 ≤ (1867995303273/4000000000000 : ℝ)^4367
        have hw : |(2698348283/5000000000 : ℝ)|=(2698348283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1242872657/2500000000 : ℝ)|^5391 ≤ (42200443287643/100000000000000 : ℝ)^4367
        have hw : |(1242872657/2500000000 : ℝ)|=(1242872657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105324631/625000000 : ℝ)|^5391 ≤ (11099674118159/100000000000000 : ℝ)^4367
        have hw : |(-105324631/625000000 : ℝ)|=(105324631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s0_3 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4030432787/10000000000 : ℝ)*x 0 + (3065910507/10000000000 : ℝ)*x 1 + (2580459317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4030432787/10000000000 : ℝ)^5391 ≤ (6513916785913/20000000000000 : ℝ)^4367 := by
    have hnat : (4030432787 : ℕ)^5391*20000000000000^4367 ≤ 6513916785913^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030432787 10000000000 6513916785913 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3065910507/10000000000 : ℝ)^5391 ≤ (23236189042693/100000000000000 : ℝ)^4367 := by
    have hnat : (3065910507 : ℕ)^5391*100000000000000^4367 ≤ 23236189042693^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3065910507 10000000000 23236189042693 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2580459317/5000000000 : ℝ)^5391 ≤ (22097113501761/50000000000000 : ℝ)^4367 := by
    have hnat : (2580459317 : ℕ)^5391*50000000000000^4367 ≤ 22097113501761^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580459317 5000000000 22097113501761 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4030432787/10000000000 : ℝ), (3065910507/10000000000 : ℝ), (2580459317/5000000000 : ℝ)] ![(6513916785913/20000000000000 : ℝ), (23236189042693/100000000000000 : ℝ), (22097113501761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4030432787/10000000000 : ℝ)|^5391 ≤ (6513916785913/20000000000000 : ℝ)^4367
        have hw : |(4030432787/10000000000 : ℝ)|=(4030432787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3065910507/10000000000 : ℝ)|^5391 ≤ (23236189042693/100000000000000 : ℝ)^4367
        have hw : |(3065910507/10000000000 : ℝ)|=(3065910507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2580459317/5000000000 : ℝ)|^5391 ≤ (22097113501761/50000000000000 : ℝ)^4367
        have hw : |(2580459317/5000000000 : ℝ)|=(2580459317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s0_4 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1306331309/10000000000 : ℝ)*x 0 + (2494301823/5000000000 : ℝ)*x 1 + (5658715801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306331309/10000000000 : ℝ)^5391 ≤ (8105508984749/100000000000000 : ℝ)^4367 := by
    have hnat : (1306331309 : ℕ)^5391*100000000000000^4367 ≤ 8105508984749^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306331309 10000000000 8105508984749 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2494301823/5000000000 : ℝ)^5391 ≤ (8475968308777/20000000000000 : ℝ)^4367 := by
    have hnat : (2494301823 : ℕ)^5391*20000000000000^4367 ≤ 8475968308777^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494301823 5000000000 8475968308777 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5658715801/10000000000 : ℝ)^5391 ≤ (12378662364351/25000000000000 : ℝ)^4367 := by
    have hnat : (5658715801 : ℕ)^5391*25000000000000^4367 ≤ 12378662364351^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658715801 10000000000 12378662364351 25000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1306331309/10000000000 : ℝ), (2494301823/5000000000 : ℝ), (5658715801/10000000000 : ℝ)] ![(8105508984749/100000000000000 : ℝ), (8475968308777/20000000000000 : ℝ), (12378662364351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1306331309/10000000000 : ℝ)|^5391 ≤ (8105508984749/100000000000000 : ℝ)^4367
        have hw : |(-1306331309/10000000000 : ℝ)|=(1306331309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2494301823/5000000000 : ℝ)|^5391 ≤ (8475968308777/20000000000000 : ℝ)^4367
        have hw : |(2494301823/5000000000 : ℝ)|=(2494301823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5658715801/10000000000 : ℝ)|^5391 ≤ (12378662364351/25000000000000 : ℝ)^4367
        have hw : |(5658715801/10000000000 : ℝ)|=(5658715801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s0_5 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (325379403/625000000 : ℝ)*x 0 + (-498984729/5000000000 : ℝ)*x 1 + (1414679049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325379403/625000000 : ℝ)^5391 ≤ (44672024781579/100000000000000 : ℝ)^4367 := by
    have hnat : (325379403 : ℕ)^5391*100000000000000^4367 ≤ 44672024781579^4367*625000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325379403 625000000 44672024781579 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498984729/5000000000 : ℝ)^5391 ≤ (5813321485939/100000000000000 : ℝ)^4367 := by
    have hnat : (498984729 : ℕ)^5391*100000000000000^4367 ≤ 5813321485939^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498984729 5000000000 5813321485939 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414679049/2500000000 : ℝ)^5391 ≤ (12378663431043/25000000000000 : ℝ)^4367 := by
    have hnat : (1414679049 : ℕ)^5391*25000000000000^4367 ≤ 12378663431043^4367*2500000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414679049 2500000000 12378663431043 25000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(325379403/625000000 : ℝ), (-498984729/5000000000 : ℝ), (1414679049/2500000000 : ℝ)] ![(44672024781579/100000000000000 : ℝ), (5813321485939/100000000000000 : ℝ), (12378663431043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(325379403/625000000 : ℝ)|^5391 ≤ (44672024781579/100000000000000 : ℝ)^4367
        have hw : |(325379403/625000000 : ℝ)|=(325379403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498984729/5000000000 : ℝ)|^5391 ≤ (5813321485939/100000000000000 : ℝ)^4367
        have hw : |(-498984729/5000000000 : ℝ)|=(498984729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414679049/2500000000 : ℝ)|^5391 ≤ (12378663431043/25000000000000 : ℝ)^4367
        have hw : |(1414679049/2500000000 : ℝ)|=(1414679049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s0_6 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520607171/1000000000 : ℝ)*x 0 + (5658715203/10000000000 : ℝ)*x 1 + (-997969089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520607171/1000000000 : ℝ)^5391 ≤ (44672038149723/100000000000000 : ℝ)^4367 := by
    have hnat : (520607171 : ℕ)^5391*100000000000000^4367 ≤ 44672038149723^4367*1000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520607171 1000000000 44672038149723 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5658715203/10000000000 : ℝ)^5391 ≤ (49514642997841/100000000000000 : ℝ)^4367 := by
    have hnat : (5658715203 : ℕ)^5391*100000000000000^4367 ≤ 49514642997841^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658715203 10000000000 49514642997841 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997969089/10000000000 : ℝ)^5391 ≤ (1453329708109/25000000000000 : ℝ)^4367 := by
    have hnat : (997969089 : ℕ)^5391*25000000000000^4367 ≤ 1453329708109^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997969089 10000000000 1453329708109 25000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520607171/1000000000 : ℝ), (5658715203/10000000000 : ℝ), (-997969089/10000000000 : ℝ)] ![(44672038149723/100000000000000 : ℝ), (49514642997841/100000000000000 : ℝ), (1453329708109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520607171/1000000000 : ℝ)|^5391 ≤ (44672038149723/100000000000000 : ℝ)^4367
        have hw : |(520607171/1000000000 : ℝ)|=(520607171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5658715203/10000000000 : ℝ)|^5391 ≤ (49514642997841/100000000000000 : ℝ)^4367
        have hw : |(5658715203/10000000000 : ℝ)|=(5658715203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-997969089/10000000000 : ℝ)|^5391 ≤ (1453329708109/25000000000000 : ℝ)^4367
        have hw : |(-997969089/10000000000 : ℝ)|=(997969089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s0_7 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4034912977/10000000000 : ℝ)*x 0 + (2555028931/5000000000 : ℝ)*x 1 + (3118428019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4034912977/10000000000 : ℝ)^5391 ≤ (16307141561153/50000000000000 : ℝ)^4367 := by
    have hnat : (4034912977 : ℕ)^5391*50000000000000^4367 ≤ 16307141561153^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034912977 10000000000 16307141561153 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2555028931/5000000000 : ℝ)^5391 ≤ (43657189935629/100000000000000 : ℝ)^4367 := by
    have hnat : (2555028931 : ℕ)^5391*100000000000000^4367 ≤ 43657189935629^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555028931 5000000000 43657189935629 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3118428019/10000000000 : ℝ)^5391 ≤ (23728526931513/100000000000000 : ℝ)^4367 := by
    have hnat : (3118428019 : ℕ)^5391*100000000000000^4367 ≤ 23728526931513^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118428019 10000000000 23728526931513 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4034912977/10000000000 : ℝ), (2555028931/5000000000 : ℝ), (3118428019/10000000000 : ℝ)] ![(16307141561153/50000000000000 : ℝ), (43657189935629/100000000000000 : ℝ), (23728526931513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4034912977/10000000000 : ℝ)|^5391 ≤ (16307141561153/50000000000000 : ℝ)^4367
        have hw : |(4034912977/10000000000 : ℝ)|=(4034912977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2555028931/5000000000 : ℝ)|^5391 ≤ (43657189935629/100000000000000 : ℝ)^4367
        have hw : |(2555028931/5000000000 : ℝ)|=(2555028931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3118428019/10000000000 : ℝ)|^5391 ≤ (23728526931513/100000000000000 : ℝ)^4367
        have hw : |(3118428019/10000000000 : ℝ)|=(3118428019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1721_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (159/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21531/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (5383/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5383 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5383*1^1024 ≤ 0^1024*1^5383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5383/1024 : ℝ) ≤ (809272273819997861/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5383 ≤ (809272273819997861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5383*100000000000000000000^1024 ≤ 809272273819997861^1024*5^5383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 809272273819997861 100000000000000000000 5383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (809272273819997861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5383 := by
      have hnat : (1 : ℕ)^1024*1^5383 ≤ 1^5383*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100809272273819997861/100000000000000000000 : ℝ) ≤ (5007672233559117/5000000000000000 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (100809272273819997861/100000000000000000000 : ℝ)^1024 ≤ (5007672233559117/5000000000000000 : ℝ)^5383 := by
      have hnat : (100809272273819997861 : ℕ)^1024*5000000000000000^5383 ≤ 5007672233559117^5383*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100809272273819997861 100000000000000000000 5007672233559117 5000000000000000 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007672233559117/5000000000000000 : ℝ)) (X := (100809272273819997861/100000000000000000000 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50809272273819997861/50000000000000000000 : ℝ) ≤ (2507672233559117/2500000000000000 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (50809272273819997861/50000000000000000000 : ℝ)^1024 ≤ (2507672233559117/2500000000000000 : ℝ)^5383 := by
      have hnat : (50809272273819997861 : ℕ)^1024*2500000000000000^5383 ≤ 2507672233559117^5383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50809272273819997861 50000000000000000000 2507672233559117 2500000000000000 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507672233559117/2500000000000000 : ℝ)) (X := (50809272273819997861/50000000000000000000 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7672233559117/2000000000000000 : ℝ)*(0 : ℝ))^(5383/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7672233559117/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(809272273819997861/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7672233559117/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5383/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7672233559117/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5007672233559117/5000000000000000 : ℝ) by norm_num, show 1+(809272273819997861/100000000000000000000 : ℝ)+(0 : ℝ)=(100809272273819997861/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(809272273819997861/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7672233559117/2000000000000000 : ℝ)*(2/5 : ℝ))^(5383/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7672233559117/2000000000000000 : ℝ)*(2/5 : ℝ)=(2507672233559117/2500000000000000 : ℝ) by norm_num, show 1+2*(809272273819997861/100000000000000000000 : ℝ)=(50809272273819997861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7672233559117/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7672233559117/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7672233559117/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7672233559117/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7672233559117/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7672233559117/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1304825387/10000000000 : ℝ)*X 0 0+(5676385039/10000000000 : ℝ)*X 0 1+(2485745299/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((674587203/1250000000 : ℝ)*X 1 0+(-168519349/1000000000 : ℝ)*X 1 1+(4971490019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2698348283/5000000000 : ℝ)*X 2 0+(1242872657/2500000000 : ℝ)*X 2 1+(-105324631/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4030432787/10000000000 : ℝ)*X 0 0+(3065910507/10000000000 : ℝ)*X 0 1+(2580459317/5000000000 : ℝ)*X 0 2+(4030432787/10000000000 : ℝ)*X 1 0+(3065910507/10000000000 : ℝ)*X 1 1+(2580459317/5000000000 : ℝ)*X 1 2+(4030432787/10000000000 : ℝ)*X 2 0+(3065910507/10000000000 : ℝ)*X 2 1+(2580459317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1306331309/10000000000 : ℝ)*X 0 0+(2494301823/5000000000 : ℝ)*X 0 1+(5658715801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((325379403/625000000 : ℝ)*X 1 0+(-498984729/5000000000 : ℝ)*X 1 1+(1414679049/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((520607171/1000000000 : ℝ)*X 2 0+(5658715203/10000000000 : ℝ)*X 2 1+(-997969089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4034912977/10000000000 : ℝ)*X 0 0+(2555028931/5000000000 : ℝ)*X 0 1+(3118428019/10000000000 : ℝ)*X 0 2+(4034912977/10000000000 : ℝ)*X 1 0+(2555028931/5000000000 : ℝ)*X 1 1+(3118428019/10000000000 : ℝ)*X 1 2+(4034912977/10000000000 : ℝ)*X 2 0+(2555028931/5000000000 : ℝ)*X 2 1+(3118428019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2191819382131355277/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (12752017/6250000000000 : ℝ)*(base1) + (444003253/25000000000000 : ℝ)*(base19) + (1497890099/100000000000000 : ℝ)*(base23) + (401297027/100000000000000 : ℝ)*(upper3) + (90800563/100000000000000 : ℝ)*(upper5) + (29624901693917/3125000000000 : ℝ)*(major0) + (29624901693917/3125000000000 : ℝ)*(major1) + (29624901693917/3125000000000 : ℝ)*(major2) + (88666252478097/6250000000000 : ℝ)*(sp0) + (2837325088547/200000000000 : ℝ)*(sp1) + (709331411198207/50000000000000 : ℝ)*(sp2) + (23866326105823/5000000000000 : ℝ)*(sp3) + (280291827/6250000000000 : ℝ)*(sp4) + (1184866427/50000000000000 : ℝ)*(sp7) + (477329095881587/100000000000000 : ℝ)*(f.failure) + (88666520017907/6250000000000 : ℝ)*(f.sum) + (1626874210039/3125000000000000000000000000 : ℝ)*base65 + (39260085241289/6250000000000000000000000000 : ℝ)*base67 + (8872933671211/6250000000000000000000000000 : ℝ)*base70 + (189656428789/6250000000000000000000000000 : ℝ)*base71 + (2584157641289/3125000000000000000000000000 : ℝ)*base73 + (11975118496211/6250000000000000000000000000 : ℝ)*base76 + (18987533096211/6250000000000000000000000000 : ℝ)*base78 + (54907012208711/6250000000000000000000000000 : ℝ)*base80 + (5264754089961/3125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3318959/1250000000000000000000 : ℝ)*base89 + (3318959/1250000000000000000000 : ℝ)*base91 + (3318959/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131851938216508570141791/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (196067027/100000000000000 : ℝ)*(base32) + (3223199/100000000000000 : ℝ)*(base37) + (51989659/25000000000000 : ℝ)*(base51) + (16149813/50000000000000 : ℝ)*(base59) + (1484927/50000000000000 : ℝ)*(upper3) + (997195128855441/100000000000000 : ℝ)*(major0) + (997195128855441/100000000000000 : ℝ)*(major1) + (997195128855441/100000000000000 : ℝ)*(major2) + (814514399/100000000000000 : ℝ)*(sp1) + (74990119/50000000000000 : ℝ)*(sp2) + (186536124587033/12500000000000 : ℝ)*(sp4) + (298457636436373/20000000000000 : ℝ)*(sp5) + (746144423358013/50000000000000 : ℝ)*(sp6) + (502100885921801/100000000000000 : ℝ)*(sp7) + (251050542606013/50000000000000 : ℝ)*(f.failure) + (186536124587033/12500000000000 : ℝ)*(f.sum) + (291971820505597/100000000000000000000000000000 : ℝ)*base65 + (1856915580594403/200000000000000000000000000000 : ℝ)*base68 + (1839631915994403/200000000000000000000000000000 : ℝ)*base70 + (1443914993994403/200000000000000000000000000000 : ℝ)*base72 + (338440757594403/100000000000000000000000000000 : ℝ)*base74 + (1271392247394403/200000000000000000000000000000 : ℝ)*base76 + (525829728394403/200000000000000000000000000000 : ℝ)*base78 + (1058350420194403/200000000000000000000000000000 : ℝ)*base80 + (502284685094403/100000000000000000000000000000 : ℝ)*base82 + (1975759/625000000000000000000 : ℝ)*base90 + (1975759/625000000000000000000 : ℝ)*base92 + (1975759/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1721_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (159/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21531/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1721_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1721_s1_0 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-685227527/5000000000 : ℝ)*x 0 + (171089301/312500000 : ℝ)*x 1 + (5129684211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685227527/5000000000 : ℝ)^5391 ≤ (8599471214719/100000000000000 : ℝ)^4367 := by
    have hnat : (685227527 : ℕ)^5391*100000000000000^4367 ≤ 8599471214719^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685227527 5000000000 8599471214719 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171089301/312500000 : ℝ)^5391 ≤ (11884063183191/25000000000000 : ℝ)^4367 := by
    have hnat : (171089301 : ℕ)^5391*25000000000000^4367 ≤ 11884063183191^4367*312500000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171089301 312500000 11884063183191 25000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129684211/10000000000 : ℝ)^5391 ≤ (43864276033397/100000000000000 : ℝ)^4367 := by
    have hnat : (5129684211 : ℕ)^5391*100000000000000^4367 ≤ 43864276033397^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129684211 10000000000 43864276033397 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-685227527/5000000000 : ℝ), (171089301/312500000 : ℝ), (5129684211/10000000000 : ℝ)] ![(8599471214719/100000000000000 : ℝ), (11884063183191/25000000000000 : ℝ), (43864276033397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-685227527/5000000000 : ℝ)|^5391 ≤ (8599471214719/100000000000000 : ℝ)^4367
        have hw : |(-685227527/5000000000 : ℝ)|=(685227527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171089301/312500000 : ℝ)|^5391 ≤ (11884063183191/25000000000000 : ℝ)^4367
        have hw : |(171089301/312500000 : ℝ)|=(171089301/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129684211/10000000000 : ℝ)|^5391 ≤ (43864276033397/100000000000000 : ℝ)^4367
        have hw : |(5129684211/10000000000 : ℝ)|=(5129684211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s1_1 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335756183/2500000000 : ℝ)*x 0 + (-774847523/5000000000 : ℝ)*x 1 + (2564841613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335756183/2500000000 : ℝ)^5391 ≤ (576590026259/1250000000000 : ℝ)^4367 := by
    have hnat : (1335756183 : ℕ)^5391*1250000000000^4367 ≤ 576590026259^4367*2500000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335756183 2500000000 576590026259 1250000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (774847523/5000000000 : ℝ)^5391 ≤ (2001706449303/20000000000000 : ℝ)^4367 := by
    have hnat : (774847523 : ℕ)^5391*20000000000000^4367 ≤ 2001706449303^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774847523 5000000000 2001706449303 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564841613/5000000000 : ℝ)^5391 ≤ (43864265635567/100000000000000 : ℝ)^4367 := by
    have hnat : (2564841613 : ℕ)^5391*100000000000000^4367 ≤ 43864265635567^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564841613 5000000000 43864265635567 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335756183/2500000000 : ℝ), (-774847523/5000000000 : ℝ), (2564841613/5000000000 : ℝ)] ![(576590026259/1250000000000 : ℝ), (2001706449303/20000000000000 : ℝ), (43864265635567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335756183/2500000000 : ℝ)|^5391 ≤ (576590026259/1250000000000 : ℝ)^4367
        have hw : |(1335756183/2500000000 : ℝ)|=(1335756183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-774847523/5000000000 : ℝ)|^5391 ≤ (2001706449303/20000000000000 : ℝ)^4367
        have hw : |(-774847523/5000000000 : ℝ)|=(774847523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564841613/5000000000 : ℝ)|^5391 ≤ (43864265635567/100000000000000 : ℝ)^4367
        have hw : |(2564841613/5000000000 : ℝ)|=(2564841613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s1_2 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667877943/1250000000 : ℝ)*x 0 + (5129684073/10000000000 : ℝ)*x 1 + (-1549695513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667877943/1250000000 : ℝ)^5391 ≤ (4612718943959/10000000000000 : ℝ)^4367 := by
    have hnat : (667877943 : ℕ)^5391*10000000000000^4367 ≤ 4612718943959^4367*1250000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667877943 1250000000 4612718943959 10000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129684073/10000000000 : ℝ)^5391 ≤ (8772854915329/20000000000000 : ℝ)^4367 := by
    have hnat : (5129684073 : ℕ)^5391*20000000000000^4367 ≤ 8772854915329^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129684073 10000000000 8772854915329 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1549695513/10000000000 : ℝ)^5391 ≤ (625533498113/6250000000000 : ℝ)^4367 := by
    have hnat : (1549695513 : ℕ)^5391*6250000000000^4367 ≤ 625533498113^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549695513 10000000000 625533498113 6250000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667877943/1250000000 : ℝ), (5129684073/10000000000 : ℝ), (-1549695513/10000000000 : ℝ)] ![(4612718943959/10000000000000 : ℝ), (8772854915329/20000000000000 : ℝ), (625533498113/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667877943/1250000000 : ℝ)|^5391 ≤ (4612718943959/10000000000000 : ℝ)^4367
        have hw : |(667877943/1250000000 : ℝ)|=(667877943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129684073/10000000000 : ℝ)|^5391 ≤ (8772854915329/20000000000000 : ℝ)^4367
        have hw : |(5129684073/10000000000 : ℝ)|=(5129684073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1549695513/10000000000 : ℝ)|^5391 ≤ (625533498113/6250000000000 : ℝ)^4367
        have hw : |(-1549695513/10000000000 : ℝ)|=(1549695513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s1_3 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4088625091/10000000000 : ℝ)*x 0 + (3595455783/10000000000 : ℝ)*x 1 + (4621337551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4088625091/10000000000 : ℝ)^5391 ≤ (33151076374767/100000000000000 : ℝ)^4367 := by
    have hnat : (4088625091 : ℕ)^5391*100000000000000^4367 ≤ 33151076374767^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4088625091 10000000000 33151076374767 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3595455783/10000000000 : ℝ)^5391 ≤ (7071711241813/25000000000000 : ℝ)^4367 := by
    have hnat : (3595455783 : ℕ)^5391*25000000000000^4367 ≤ 7071711241813^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3595455783 10000000000 7071711241813 25000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4621337551/10000000000 : ℝ)^5391 ≤ (19281039322291/50000000000000 : ℝ)^4367 := by
    have hnat : (4621337551 : ℕ)^5391*50000000000000^4367 ≤ 19281039322291^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4621337551 10000000000 19281039322291 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4088625091/10000000000 : ℝ), (3595455783/10000000000 : ℝ), (4621337551/10000000000 : ℝ)] ![(33151076374767/100000000000000 : ℝ), (7071711241813/25000000000000 : ℝ), (19281039322291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4088625091/10000000000 : ℝ)|^5391 ≤ (33151076374767/100000000000000 : ℝ)^4367
        have hw : |(4088625091/10000000000 : ℝ)|=(4088625091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3595455783/10000000000 : ℝ)|^5391 ≤ (7071711241813/25000000000000 : ℝ)^4367
        have hw : |(3595455783/10000000000 : ℝ)|=(3595455783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4621337551/10000000000 : ℝ)|^5391 ≤ (19281039322291/50000000000000 : ℝ)^4367
        have hw : |(4621337551/10000000000 : ℝ)|=(4621337551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s1_4 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1370632417/10000000000 : ℝ)*x 0 + (5133798481/10000000000 : ℝ)*x 1 + (2735338387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370632417/10000000000 : ℝ)^5391 ≤ (4300422569353/50000000000000 : ℝ)^4367 := by
    have hnat : (1370632417 : ℕ)^5391*50000000000000^4367 ≤ 4300422569353^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370632417 10000000000 4300422569353 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133798481/10000000000 : ℝ)^5391 ≤ (10976927765029/25000000000000 : ℝ)^4367 := by
    have hnat : (5133798481 : ℕ)^5391*25000000000000^4367 ≤ 10976927765029^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133798481 10000000000 10976927765029 25000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735338387/5000000000 : ℝ)^5391 ≤ (47491443781691/100000000000000 : ℝ)^4367 := by
    have hnat : (2735338387 : ℕ)^5391*100000000000000^4367 ≤ 47491443781691^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735338387 5000000000 47491443781691 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1370632417/10000000000 : ℝ), (5133798481/10000000000 : ℝ), (2735338387/5000000000 : ℝ)] ![(4300422569353/50000000000000 : ℝ), (10976927765029/25000000000000 : ℝ), (47491443781691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1370632417/10000000000 : ℝ)|^5391 ≤ (4300422569353/50000000000000 : ℝ)^4367
        have hw : |(-1370632417/10000000000 : ℝ)|=(1370632417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133798481/10000000000 : ℝ)|^5391 ≤ (10976927765029/25000000000000 : ℝ)^4367
        have hw : |(5133798481/10000000000 : ℝ)|=(5133798481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735338387/5000000000 : ℝ)|^5391 ≤ (47491443781691/100000000000000 : ℝ)^4367
        have hw : |(2735338387/5000000000 : ℝ)|=(2735338387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s1_5 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210023959/400000000 : ℝ)*x 0 + (-604351191/5000000000 : ℝ)*x 1 + (109413529/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210023959/400000000 : ℝ)^5391 ≤ (45144179585507/100000000000000 : ℝ)^4367 := by
    have hnat : (210023959 : ℕ)^5391*100000000000000^4367 ≤ 45144179585507^4367*400000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210023959 400000000 45144179585507 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604351191/5000000000 : ℝ)^5391 ≤ (460273756173/6250000000000 : ℝ)^4367 := by
    have hnat : (604351191 : ℕ)^5391*6250000000000^4367 ≤ 460273756173^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604351191 5000000000 460273756173 6250000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109413529/200000000 : ℝ)^5391 ≤ (9498288061897/20000000000000 : ℝ)^4367 := by
    have hnat : (109413529 : ℕ)^5391*20000000000000^4367 ≤ 9498288061897^4367*200000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109413529 200000000 9498288061897 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210023959/400000000 : ℝ), (-604351191/5000000000 : ℝ), (109413529/200000000 : ℝ)] ![(45144179585507/100000000000000 : ℝ), (460273756173/6250000000000 : ℝ), (9498288061897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210023959/400000000 : ℝ)|^5391 ≤ (45144179585507/100000000000000 : ℝ)^4367
        have hw : |(210023959/400000000 : ℝ)|=(210023959/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-604351191/5000000000 : ℝ)|^5391 ≤ (460273756173/6250000000000 : ℝ)^4367
        have hw : |(-604351191/5000000000 : ℝ)|=(604351191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109413529/200000000 : ℝ)|^5391 ≤ (9498288061897/20000000000000 : ℝ)^4367
        have hw : |(109413529/200000000 : ℝ)|=(109413529/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s1_6 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250599349/10000000000 : ℝ)*x 0 + (1094135259/2000000000 : ℝ)*x 1 + (-1208702073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250599349/10000000000 : ℝ)^5391 ≤ (22572091777571/50000000000000 : ℝ)^4367 := by
    have hnat : (5250599349 : ℕ)^5391*50000000000000^4367 ≤ 22572091777571^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250599349 10000000000 22572091777571 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094135259/2000000000 : ℝ)^5391 ≤ (47491438648399/100000000000000 : ℝ)^4367 := by
    have hnat : (1094135259 : ℕ)^5391*100000000000000^4367 ≤ 47491438648399^4367*2000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094135259 2000000000 47491438648399 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208702073/10000000000 : ℝ)^5391 ≤ (920547221829/12500000000000 : ℝ)^4367 := by
    have hnat : (1208702073 : ℕ)^5391*12500000000000^4367 ≤ 920547221829^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208702073 10000000000 920547221829 12500000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250599349/10000000000 : ℝ), (1094135259/2000000000 : ℝ), (-1208702073/10000000000 : ℝ)] ![(22572091777571/50000000000000 : ℝ), (47491438648399/100000000000000 : ℝ), (920547221829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250599349/10000000000 : ℝ)|^5391 ≤ (22572091777571/50000000000000 : ℝ)^4367
        have hw : |(5250599349/10000000000 : ℝ)|=(5250599349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094135259/2000000000 : ℝ)|^5391 ≤ (47491438648399/100000000000000 : ℝ)^4367
        have hw : |(1094135259/2000000000 : ℝ)|=(1094135259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1208702073/10000000000 : ℝ)|^5391 ≤ (920547221829/12500000000000 : ℝ)^4367
        have hw : |(-1208702073/10000000000 : ℝ)|=(1208702073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s1_7 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4089147709/10000000000 : ℝ)*x 0 + (4609108707/10000000000 : ℝ)*x 1 + (3607878339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4089147709/10000000000 : ℝ)^5391 ≤ (3315630752697/10000000000000 : ℝ)^4367 := by
    have hnat : (4089147709 : ℕ)^5391*10000000000000^4367 ≤ 3315630752697^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089147709 10000000000 3315630752697 10000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4609108707/10000000000 : ℝ)^5391 ≤ (38436148576019/100000000000000 : ℝ)^4367 := by
    have hnat : (4609108707 : ℕ)^5391*100000000000000^4367 ≤ 38436148576019^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609108707 10000000000 38436148576019 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3607878339/10000000000 : ℝ)^5391 ≤ (28407543890543/100000000000000 : ℝ)^4367 := by
    have hnat : (3607878339 : ℕ)^5391*100000000000000^4367 ≤ 28407543890543^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3607878339 10000000000 28407543890543 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4089147709/10000000000 : ℝ), (4609108707/10000000000 : ℝ), (3607878339/10000000000 : ℝ)] ![(3315630752697/10000000000000 : ℝ), (38436148576019/100000000000000 : ℝ), (28407543890543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4089147709/10000000000 : ℝ)|^5391 ≤ (3315630752697/10000000000000 : ℝ)^4367
        have hw : |(4089147709/10000000000 : ℝ)|=(4089147709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4609108707/10000000000 : ℝ)|^5391 ≤ (38436148576019/100000000000000 : ℝ)^4367
        have hw : |(4609108707/10000000000 : ℝ)|=(4609108707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3607878339/10000000000 : ℝ)|^5391 ≤ (28407543890543/100000000000000 : ℝ)^4367
        have hw : |(3607878339/10000000000 : ℝ)|=(3607878339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1721_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21531/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (159/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (9879/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8631/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21531/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (159/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21531/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (159/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21531/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (159/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21531/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (159/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21531/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (159/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21531/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (159/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (159/2500 : ℝ) ^ (5383/1024 : ℝ) ≤ (5128263887481/10000000000000000000 : ℝ) := by
    have hpowers : (159/2500 : ℝ)^5383 ≤ (5128263887481/10000000000000000000 : ℝ)^1024 := by
      have hnat : (159 : ℕ)^5383*10000000000000000000^1024 ≤ 5128263887481^1024*2500^5383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        159 2500 5128263887481 10000000000000000000 5383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (159/2500 : ℝ)) (X := (5128263887481/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21531/100000 : ℝ) ^ (5383/1024 : ℝ) ≤ (3119090123822307/10000000000000000000 : ℝ) := by
    have hpowers : (21531/100000 : ℝ)^5383 ≤ (3119090123822307/10000000000000000000 : ℝ)^1024 := by
      have hnat : (21531 : ℕ)^5383*10000000000000000000^1024 ≤ 3119090123822307^1024*100000^5383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21531 100000 3119090123822307 10000000000000000000 5383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21531/100000 : ℝ)) (X := (3119090123822307/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000005128263887481/5000000000000000000 : ℝ) ≤ (2000000390216611/2000000000000000 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (5000005128263887481/5000000000000000000 : ℝ)^1024 ≤ (2000000390216611/2000000000000000 : ℝ)^5383 := by
      have hnat : (5000005128263887481 : ℕ)^1024*2000000000000000^5383 ≤ 2000000390216611^5383*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000005128263887481 5000000000000000000 2000000390216611 2000000000000000 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000390216611/2000000000000000 : ℝ)) (X := (5000005128263887481/5000000000000000000 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500781054596927447/2500000000000000000 : ℝ) ≤ (2500148560051181/2500000000000000 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (2500781054596927447/2500000000000000000 : ℝ)^1024 ≤ (2500148560051181/2500000000000000 : ℝ)^5383 := by
      have hnat : (2500781054596927447 : ℕ)^1024*2500000000000000^5383 ≤ 2500148560051181^5383*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500781054596927447 2500000000000000000 2500148560051181 2500000000000000 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500148560051181/2500000000000000 : ℝ)) (X := (2500781054596927447/2500000000000000000 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003119090123822307/5000000000000000000 : ℝ) ≤ (10001186529326393/10000000000000000 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (5003119090123822307/5000000000000000000 : ℝ)^1024 ≤ (10001186529326393/10000000000000000 : ℝ)^5383 := by
      have hnat : (5003119090123822307 : ℕ)^1024*10000000000000000^5383 ≤ 10001186529326393^5383*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003119090123822307 5000000000000000000 10001186529326393 10000000000000000 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001186529326393/10000000000000000 : ℝ)) (X := (5003119090123822307/5000000000000000000 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5128263887481/10000000000000000000 : ℝ) ≤ ((2022699942430045303/2022800000000000000 : ℝ)+2*(197429707223/505700000000000 : ℝ)*(159/2500 : ℝ))^(5383/1024 : ℝ) := by
    rw [show (2022699942430045303/2022800000000000000 : ℝ)+2*(197429707223/505700000000000 : ℝ)*(159/2500 : ℝ)=(2000000390216611/2000000000000000 : ℝ) by norm_num, show 1+2*(5128263887481/10000000000000000000 : ℝ)=(5000005128263887481/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3119090123822307/10000000000000000000 : ℝ)+(5128263887481/10000000000000000000 : ℝ) ≤ ((2022699942430045303/2022800000000000000 : ℝ)+(197429707223/505700000000000 : ℝ)*((21531/100000 : ℝ)+(159/2500 : ℝ)))^(5383/1024 : ℝ) := by
    rw [show (2022699942430045303/2022800000000000000 : ℝ)+(197429707223/505700000000000 : ℝ)*((21531/100000 : ℝ)+(159/2500 : ℝ))=(2500148560051181/2500000000000000 : ℝ) by norm_num, show 1+(3119090123822307/10000000000000000000 : ℝ)+(5128263887481/10000000000000000000 : ℝ)=(2500781054596927447/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3119090123822307/10000000000000000000 : ℝ) ≤ ((2022699942430045303/2022800000000000000 : ℝ)+2*(197429707223/505700000000000 : ℝ)*(21531/100000 : ℝ))^(5383/1024 : ℝ) := by
    rw [show (2022699942430045303/2022800000000000000 : ℝ)+2*(197429707223/505700000000000 : ℝ)*(21531/100000 : ℝ)=(10001186529326393/10000000000000000 : ℝ) by norm_num, show 1+2*(3119090123822307/10000000000000000000 : ℝ)=(5003119090123822307/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2022699942430045303/2022800000000000000 : ℝ)*(X 1 0+X 2 0)+(197429707223/505700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (159/2500 : ℝ)) (hi := (21531/100000 : ℝ)) (c := (2022699942430045303/2022800000000000000 : ℝ)) (alpha := (197429707223/505700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2022699942430045303/2022800000000000000 : ℝ)*(X 0 1+X 2 1)+(197429707223/505700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (159/2500 : ℝ)) (hi := (21531/100000 : ℝ)) (c := (2022699942430045303/2022800000000000000 : ℝ)) (alpha := (197429707223/505700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2022699942430045303/2022800000000000000 : ℝ)*(X 0 2+X 1 2)+(197429707223/505700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (159/2500 : ℝ)) (hi := (21531/100000 : ℝ)) (c := (2022699942430045303/2022800000000000000 : ℝ)) (alpha := (197429707223/505700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-685227527/5000000000 : ℝ)*X 0 0+(171089301/312500000 : ℝ)*X 0 1+(5129684211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1335756183/2500000000 : ℝ)*X 1 0+(-774847523/5000000000 : ℝ)*X 1 1+(2564841613/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((667877943/1250000000 : ℝ)*X 2 0+(5129684073/10000000000 : ℝ)*X 2 1+(-1549695513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4088625091/10000000000 : ℝ)*X 0 0+(3595455783/10000000000 : ℝ)*X 0 1+(4621337551/10000000000 : ℝ)*X 0 2+(4088625091/10000000000 : ℝ)*X 1 0+(3595455783/10000000000 : ℝ)*X 1 1+(4621337551/10000000000 : ℝ)*X 1 2+(4088625091/10000000000 : ℝ)*X 2 0+(3595455783/10000000000 : ℝ)*X 2 1+(4621337551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1370632417/10000000000 : ℝ)*X 0 0+(5133798481/10000000000 : ℝ)*X 0 1+(2735338387/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210023959/400000000 : ℝ)*X 1 0+(-604351191/5000000000 : ℝ)*X 1 1+(109413529/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5250599349/10000000000 : ℝ)*X 2 0+(1094135259/2000000000 : ℝ)*X 2 1+(-1208702073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4089147709/10000000000 : ℝ)*X 0 0+(4609108707/10000000000 : ℝ)*X 0 1+(3607878339/10000000000 : ℝ)*X 0 2+(4089147709/10000000000 : ℝ)*X 1 0+(4609108707/10000000000 : ℝ)*X 1 1+(3607878339/10000000000 : ℝ)*X 1 2+(4089147709/10000000000 : ℝ)*X 2 0+(4609108707/10000000000 : ℝ)*X 2 1+(3607878339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42860454484722238870411509/6321250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (640564021/100000000000000 : ℝ)*(base19) + (38102053/25000000000000 : ℝ)*(lower2) + (92857679/50000000000000 : ℝ)*(lower4) + (19135987/25000000000000 : ℝ)*(lower5) + (241992481549849/12500000000000 : ℝ)*(major0) + (241992481549849/12500000000000 : ℝ)*(major1) + (241992481549849/12500000000000 : ℝ)*(major2) + (289710291840747/10000000000000 : ℝ)*(sp0) + (289710305821591/10000000000000 : ℝ)*(sp1) + (2897100302881027/100000000000000 : ℝ)*(sp2) + (974771609554819/100000000000000 : ℝ)*(sp3) + (4950822743/100000000000000 : ℝ)*(sp4) + (2085225141/50000000000000 : ℝ)*(sp5) + (3783174593/50000000000000 : ℝ)*(sp6) + (974771609554819/100000000000000 : ℝ)*(f.failure) + (2897107869230213/100000000000000 : ℝ)*(f.sum) + (13266053208007/12642500000000000000000000000 : ℝ)*base66 + (213327007340617247/25285000000000000000000000000000 : ℝ)*base67 + (124622099011632247/25285000000000000000000000000000 : ℝ)*base69 + (107208949664402247/25285000000000000000000000000000 : ℝ)*base71 + (28997182862111/25285000000000000000000000000 : ℝ)*base73 + (220653079978852247/25285000000000000000000000000000 : ℝ)*base75 + (138728953907217753/25285000000000000000000000000000 : ℝ)*base78 + (121553471031487247/25285000000000000000000000000000 : ℝ)*base79 + (8781434696223/3160625000000000000000000000 : ℝ)*base82 + (3709183/1250000000000000000000 : ℝ)*base89 + (3709183/1250000000000000000000 : ℝ)*base91 + (3709183/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (559990221368005221994345413/50570000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (530220279/25000000000000 : ℝ)*(base19) + (632675819/25000000000000 : ℝ)*(base23) + (4305711/5000000000000 : ℝ)*(upper2) + (256565377/100000000000000 : ℝ)*(upper3) + (105284477/25000000000000 : ℝ)*(upper5) + (991801106829457/50000000000000 : ℝ)*(major0) + (991801106829457/50000000000000 : ℝ)*(major1) + (991801106829457/50000000000000 : ℝ)*(major2) + (713061731/4000000000000 : ℝ)*(sp1) + (9889770101/50000000000000 : ℝ)*(sp2) + (1484216906124467/50000000000000 : ℝ)*(sp4) + (1484206932412271/50000000000000 : ℝ)*(sp5) + (593682300401091/20000000000000 : ℝ)*(sp6) + (249692561487507/25000000000000 : ℝ)*(sp7) + (249692561487507/25000000000000 : ℝ)*(f.failure) + (1484216906124467/50000000000000 : ℝ)*(f.sum) + (2639245688137/395078125000000000000000000 : ℝ)*base66 + (277404025400465529/101140000000000000000000000000000 : ℝ)*base68 + (977175438068585529/101140000000000000000000000000000 : ℝ)*base70 + (239022422610254471/101140000000000000000000000000000 : ℝ)*base71 + (3755327830219/3160625000000000000000000000 : ℝ)*base73 + (35762511101345529/101140000000000000000000000000000 : ℝ)*base76 + (754641963633365529/101140000000000000000000000000000 : ℝ)*base78 + (73680959002154471/101140000000000000000000000000000 : ℝ)*base79 + (124125143809713/25285000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3566399/312500000000000000000 : ℝ)*base89 + (3566399/312500000000000000000 : ℝ)*base91 + (3566399/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1721_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21531/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (159/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9879/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8631/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1721_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1721_s2_0 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-686606417/5000000000 : ℝ)*x 0 + (5463453241/10000000000 : ℝ)*x 1 + (1027846999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686606417/5000000000 : ℝ)^5391 ≤ (1077604847909/12500000000000 : ℝ)^4367 := by
    have hnat : (686606417 : ℕ)^5391*12500000000000^4367 ≤ 1077604847909^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686606417 5000000000 1077604847909 12500000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463453241/10000000000 : ℝ)^5391 ≤ (47414043443659/100000000000000 : ℝ)^4367 := by
    have hnat : (5463453241 : ℕ)^5391*100000000000000^4367 ≤ 47414043443659^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463453241 10000000000 47414043443659 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027846999/2000000000 : ℝ)^5391 ≤ (43965117753671/100000000000000 : ℝ)^4367 := by
    have hnat : (1027846999 : ℕ)^5391*100000000000000^4367 ≤ 43965117753671^4367*2000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027846999 2000000000 43965117753671 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-686606417/5000000000 : ℝ), (5463453241/10000000000 : ℝ), (1027846999/2000000000 : ℝ)] ![(1077604847909/12500000000000 : ℝ), (47414043443659/100000000000000 : ℝ), (43965117753671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-686606417/5000000000 : ℝ)|^5391 ≤ (1077604847909/12500000000000 : ℝ)^4367
        have hw : |(-686606417/5000000000 : ℝ)|=(686606417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463453241/10000000000 : ℝ)|^5391 ≤ (47414043443659/100000000000000 : ℝ)^4367
        have hw : |(5463453241/10000000000 : ℝ)|=(5463453241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027846999/2000000000 : ℝ)|^5391 ≤ (43965117753671/100000000000000 : ℝ)^4367
        have hw : |(1027846999/2000000000 : ℝ)|=(1027846999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s2_1 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533991931/1000000000 : ℝ)*x 0 + (-1541191031/10000000000 : ℝ)*x 1 + (2569617439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533991931/1000000000 : ℝ)^5391 ≤ (23047054132979/50000000000000 : ℝ)^4367 := by
    have hnat : (533991931 : ℕ)^5391*50000000000000^4367 ≤ 23047054132979^4367*1000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533991931 1000000000 23047054132979 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1541191031/10000000000 : ℝ)^5391 ≤ (1988155041823/20000000000000 : ℝ)^4367 := by
    have hnat : (1541191031 : ℕ)^5391*20000000000000^4367 ≤ 1988155041823^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541191031 10000000000 1988155041823 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569617439/5000000000 : ℝ)^5391 ≤ (2198255825903/5000000000000 : ℝ)^4367 := by
    have hnat : (2569617439 : ℕ)^5391*5000000000000^4367 ≤ 2198255825903^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569617439 5000000000 2198255825903 5000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533991931/1000000000 : ℝ), (-1541191031/10000000000 : ℝ), (2569617439/5000000000 : ℝ)] ![(23047054132979/50000000000000 : ℝ), (1988155041823/20000000000000 : ℝ), (2198255825903/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533991931/1000000000 : ℝ)|^5391 ≤ (23047054132979/50000000000000 : ℝ)^4367
        have hw : |(533991931/1000000000 : ℝ)|=(533991931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1541191031/10000000000 : ℝ)|^5391 ≤ (1988155041823/20000000000000 : ℝ)^4367
        have hw : |(-1541191031/10000000000 : ℝ)|=(1541191031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569617439/5000000000 : ℝ)|^5391 ≤ (2198255825903/5000000000000 : ℝ)^4367
        have hw : |(2569617439/5000000000 : ℝ)|=(2569617439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s2_2 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667489893/1250000000 : ℝ)*x 0 + (5139235017/10000000000 : ℝ)*x 1 + (-385297767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667489893/1250000000 : ℝ)^5391 ≤ (46094106497051/100000000000000 : ℝ)^4367 := by
    have hnat : (667489893 : ℕ)^5391*100000000000000^4367 ≤ 46094106497051^4367*1250000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667489893 1250000000 46094106497051 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139235017/10000000000 : ℝ)^5391 ≤ (5495639748251/12500000000000 : ℝ)^4367 := by
    have hnat : (5139235017 : ℕ)^5391*12500000000000^4367 ≤ 5495639748251^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139235017 10000000000 5495639748251 12500000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385297767/2500000000 : ℝ)^5391 ≤ (621298468983/6250000000000 : ℝ)^4367 := by
    have hnat : (385297767 : ℕ)^5391*6250000000000^4367 ≤ 621298468983^4367*2500000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385297767 2500000000 621298468983 6250000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667489893/1250000000 : ℝ), (5139235017/10000000000 : ℝ), (-385297767/2500000000 : ℝ)] ![(46094106497051/100000000000000 : ℝ), (5495639748251/12500000000000 : ℝ), (621298468983/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667489893/1250000000 : ℝ)|^5391 ≤ (46094106497051/100000000000000 : ℝ)^4367
        have hw : |(667489893/1250000000 : ℝ)|=(667489893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139235017/10000000000 : ℝ)|^5391 ≤ (5495639748251/12500000000000 : ℝ)^4367
        have hw : |(5139235017/10000000000 : ℝ)|=(5139235017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-385297767/2500000000 : ℝ)|^5391 ≤ (621298468983/6250000000000 : ℝ)^4367
        have hw : |(-385297767/2500000000 : ℝ)|=(385297767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s2_3 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4090769107/10000000000 : ℝ)*x 0 + (3626409223/10000000000 : ℝ)*x 1 + (91800313/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4090769107/10000000000 : ℝ)^5391 ≤ (33172537930609/100000000000000 : ℝ)^4367 := by
    have hnat : (4090769107 : ℕ)^5391*100000000000000^4367 ≤ 33172537930609^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090769107 10000000000 33172537930609 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3626409223/10000000000 : ℝ)^5391 ≤ (2858777310309/10000000000000 : ℝ)^4367 := by
    have hnat : (3626409223 : ℕ)^5391*10000000000000^4367 ≤ 2858777310309^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3626409223 10000000000 2858777310309 10000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91800313/200000000 : ℝ)^5391 ≤ (38239688946447/100000000000000 : ℝ)^4367 := by
    have hnat : (91800313 : ℕ)^5391*100000000000000^4367 ≤ 38239688946447^4367*200000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91800313 200000000 38239688946447 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4090769107/10000000000 : ℝ), (3626409223/10000000000 : ℝ), (91800313/200000000 : ℝ)] ![(33172537930609/100000000000000 : ℝ), (2858777310309/10000000000000 : ℝ), (38239688946447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4090769107/10000000000 : ℝ)|^5391 ≤ (33172537930609/100000000000000 : ℝ)^4367
        have hw : |(4090769107/10000000000 : ℝ)|=(4090769107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3626409223/10000000000 : ℝ)|^5391 ≤ (2858777310309/10000000000000 : ℝ)^4367
        have hw : |(3626409223/10000000000 : ℝ)|=(3626409223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91800313/200000000 : ℝ)|^5391 ≤ (38239688946447/100000000000000 : ℝ)^4367
        have hw : |(91800313/200000000 : ℝ)|=(91800313/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s2_4 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-686679211/5000000000 : ℝ)*x 0 + (5142867329/10000000000 : ℝ)*x 1 + (1091953347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686679211/5000000000 : ℝ)^5391 ≤ (8621967094183/100000000000000 : ℝ)^4367 := by
    have hnat : (686679211 : ℕ)^5391*100000000000000^4367 ≤ 8621967094183^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686679211 5000000000 8621967094183 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142867329/10000000000 : ℝ)^5391 ≤ (22001740602009/50000000000000 : ℝ)^4367 := by
    have hnat : (5142867329 : ℕ)^5391*50000000000000^4367 ≤ 22001740602009^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142867329 10000000000 22001740602009 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091953347/2000000000 : ℝ)^5391 ≤ (47374551684191/100000000000000 : ℝ)^4367 := by
    have hnat : (1091953347 : ℕ)^5391*100000000000000^4367 ≤ 47374551684191^4367*2000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091953347 2000000000 47374551684191 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-686679211/5000000000 : ℝ), (5142867329/10000000000 : ℝ), (1091953347/2000000000 : ℝ)] ![(8621967094183/100000000000000 : ℝ), (22001740602009/50000000000000 : ℝ), (47374551684191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-686679211/5000000000 : ℝ)|^5391 ≤ (8621967094183/100000000000000 : ℝ)^4367
        have hw : |(-686679211/5000000000 : ℝ)|=(686679211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142867329/10000000000 : ℝ)|^5391 ≤ (22001740602009/50000000000000 : ℝ)^4367
        have hw : |(5142867329/10000000000 : ℝ)|=(5142867329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091953347/2000000000 : ℝ)|^5391 ≤ (47374551684191/100000000000000 : ℝ)^4367
        have hw : |(1091953347/2000000000 : ℝ)|=(1091953347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s2_5 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253128663/10000000000 : ℝ)*x 0 + (-122065919/1000000000 : ℝ)*x 1 + (5459766747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253128663/10000000000 : ℝ)^5391 ≤ (9034206241739/20000000000000 : ℝ)^4367 := by
    have hnat : (5253128663 : ℕ)^5391*20000000000000^4367 ≤ 9034206241739^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253128663 10000000000 9034206241739 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122065919/1000000000 : ℝ)^5391 ≤ (7454416960899/100000000000000 : ℝ)^4367 := by
    have hnat : (122065919 : ℕ)^5391*100000000000000^4367 ≤ 7454416960899^4367*1000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122065919 1000000000 7454416960899 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459766747/10000000000 : ℝ)^5391 ≤ (47374551812731/100000000000000 : ℝ)^4367 := by
    have hnat : (5459766747 : ℕ)^5391*100000000000000^4367 ≤ 47374551812731^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459766747 10000000000 47374551812731 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253128663/10000000000 : ℝ), (-122065919/1000000000 : ℝ), (5459766747/10000000000 : ℝ)] ![(9034206241739/20000000000000 : ℝ), (7454416960899/100000000000000 : ℝ), (47374551812731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253128663/10000000000 : ℝ)|^5391 ≤ (9034206241739/20000000000000 : ℝ)^4367
        have hw : |(5253128663/10000000000 : ℝ)|=(5253128663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122065919/1000000000 : ℝ)|^5391 ≤ (7454416960899/100000000000000 : ℝ)^4367
        have hw : |(-122065919/1000000000 : ℝ)|=(122065919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459766747/10000000000 : ℝ)|^5391 ≤ (47374551812731/100000000000000 : ℝ)^4367
        have hw : |(5459766747/10000000000 : ℝ)|=(5459766747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s2_6 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253128683/10000000000 : ℝ)*x 0 + (2729883369/5000000000 : ℝ)*x 1 + (-152582397/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253128683/10000000000 : ℝ)^5391 ≤ (45171031420999/100000000000000 : ℝ)^4367 := by
    have hnat : (5253128683 : ℕ)^5391*100000000000000^4367 ≤ 45171031420999^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253128683 10000000000 45171031420999 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729883369/5000000000 : ℝ)^5391 ≤ (23687275858163/50000000000000 : ℝ)^4367 := by
    have hnat : (2729883369 : ℕ)^5391*50000000000000^4367 ≤ 23687275858163^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729883369 5000000000 23687275858163 50000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152582397/1250000000 : ℝ)^5391 ≤ (1490883371071/20000000000000 : ℝ)^4367 := by
    have hnat : (152582397 : ℕ)^5391*20000000000000^4367 ≤ 1490883371071^4367*1250000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152582397 1250000000 1490883371071 20000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253128683/10000000000 : ℝ), (2729883369/5000000000 : ℝ), (-152582397/1250000000 : ℝ)] ![(45171031420999/100000000000000 : ℝ), (23687275858163/50000000000000 : ℝ), (1490883371071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253128683/10000000000 : ℝ)|^5391 ≤ (45171031420999/100000000000000 : ℝ)^4367
        have hw : |(5253128683/10000000000 : ℝ)|=(5253128683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729883369/5000000000 : ℝ)|^5391 ≤ (23687275858163/50000000000000 : ℝ)^4367
        have hw : |(2729883369/5000000000 : ℝ)|=(2729883369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-152582397/1250000000 : ℝ)|^5391 ≤ (1490883371071/20000000000000 : ℝ)^4367
        have hw : |(-152582397/1250000000 : ℝ)|=(152582397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1721_s2_7 (p : ℝ) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (255700123/625000000 : ℝ)*x 0 + (4579219637/10000000000 : ℝ)*x 1 + (1818683127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255700123/625000000 : ℝ)^5391 ≤ (3317687118033/10000000000000 : ℝ)^4367 := by
    have hnat : (255700123 : ℕ)^5391*10000000000000^4367 ≤ 3317687118033^4367*625000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255700123 625000000 3317687118033 10000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4579219637/10000000000 : ℝ)^5391 ≤ (238304294903/625000000000 : ℝ)^4367 := by
    have hnat : (4579219637 : ℕ)^5391*625000000000^4367 ≤ 238304294903^4367*10000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579219637 10000000000 238304294903 625000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1818683127/5000000000 : ℝ)^5391 ≤ (28694441617559/100000000000000 : ℝ)^4367 := by
    have hnat : (1818683127 : ℕ)^5391*100000000000000^4367 ≤ 28694441617559^4367*5000000000^5391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818683127 5000000000 28694441617559 100000000000000 5391 4367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5391/1024 : ℝ)) 5391 4367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(255700123/625000000 : ℝ), (4579219637/10000000000 : ℝ), (1818683127/5000000000 : ℝ)] ![(3317687118033/10000000000000 : ℝ), (238304294903/625000000000 : ℝ), (28694441617559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(255700123/625000000 : ℝ)|^5391 ≤ (3317687118033/10000000000000 : ℝ)^4367
        have hw : |(255700123/625000000 : ℝ)|=(255700123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4579219637/10000000000 : ℝ)|^5391 ≤ (238304294903/625000000000 : ℝ)^4367
        have hw : |(4579219637/10000000000 : ℝ)|=(4579219637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1818683127/5000000000 : ℝ)|^5391 ≤ (28694441617559/100000000000000 : ℝ)^4367
        have hw : |(1818683127/5000000000 : ℝ)|=(1818683127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1721_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8631/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9879/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10087/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8511/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8631/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9879/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8631/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9879/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8631/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9879/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8631/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9879/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8631/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9879/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8631/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9879/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9879/100000 : ℝ) ^ (5383/1024 : ℝ) ≤ (103848706136703/20000000000000000000 : ℝ) := by
    have hpowers : (9879/100000 : ℝ)^5383 ≤ (103848706136703/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9879 : ℕ)^5383*20000000000000000000^1024 ≤ 103848706136703^1024*100000^5383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9879 100000 103848706136703 20000000000000000000 5383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9879/100000 : ℝ)) (X := (103848706136703/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8631/50000 : ℝ) ^ (5383/1024 : ℝ) ≤ (4880711602639131/50000000000000000000 : ℝ) := by
    have hpowers : (8631/50000 : ℝ)^5383 ≤ (4880711602639131/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8631 : ℕ)^5383*50000000000000000000^1024 ≤ 4880711602639131^1024*50000^5383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8631 50000 4880711602639131 50000000000000000000 5383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8631/50000 : ℝ)) (X := (4880711602639131/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000103848706136703/10000000000000000000 : ℝ) ≤ (5000009877450117/5000000000000000 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (10000103848706136703/10000000000000000000 : ℝ)^1024 ≤ (5000009877450117/5000000000000000 : ℝ)^5383 := by
      have hnat : (10000103848706136703 : ℕ)^1024*5000000000000000^5383 ≤ 5000009877450117^5383*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000103848706136703 10000000000000000000 5000009877450117 5000000000000000 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000009877450117/5000000000000000 : ℝ)) (X := (10000103848706136703/10000000000000000000 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010280666735961777/100000000000000000000 : ℝ) ≤ (156253055616223/156250000000000 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (100010280666735961777/100000000000000000000 : ℝ)^1024 ≤ (156253055616223/156250000000000 : ℝ)^5383 := by
      have hnat : (100010280666735961777 : ℕ)^1024*156250000000000^5383 ≤ 156253055616223^5383*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010280666735961777 100000000000000000000 156253055616223 156250000000000 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156253055616223/156250000000000 : ℝ)) (X := (100010280666735961777/100000000000000000000 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004880711602639131/25000000000000000000 : ℝ) ≤ (1000037136397631/1000000000000000 : ℝ) ^ (5383/1024 : ℝ) := by
    have hpowers : (25004880711602639131/25000000000000000000 : ℝ)^1024 ≤ (1000037136397631/1000000000000000 : ℝ)^5383 := by
      have hnat : (25004880711602639131 : ℕ)^1024*1000000000000000^5383 ≤ 1000037136397631^5383*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004880711602639131 25000000000000000000 1000037136397631 1000000000000000 1024 5383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000037136397631/1000000000000000 : ℝ)) (X := (25004880711602639131/25000000000000000000 : ℝ)) (by norm_num) 5383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103848706136703/20000000000000000000 : ℝ) ≤ ((12304445384060978803/12305000000000000000 : ℝ)+2*(87902269019/369150000000000 : ℝ)*(9879/100000 : ℝ))^(5383/1024 : ℝ) := by
    rw [show (12304445384060978803/12305000000000000000 : ℝ)+2*(87902269019/369150000000000 : ℝ)*(9879/100000 : ℝ)=(5000009877450117/5000000000000000 : ℝ) by norm_num, show 1+2*(103848706136703/20000000000000000000 : ℝ)=(10000103848706136703/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4880711602639131/50000000000000000000 : ℝ)+(103848706136703/20000000000000000000 : ℝ) ≤ ((12304445384060978803/12305000000000000000 : ℝ)+(87902269019/369150000000000 : ℝ)*((8631/50000 : ℝ)+(9879/100000 : ℝ)))^(5383/1024 : ℝ) := by
    rw [show (12304445384060978803/12305000000000000000 : ℝ)+(87902269019/369150000000000 : ℝ)*((8631/50000 : ℝ)+(9879/100000 : ℝ))=(156253055616223/156250000000000 : ℝ) by norm_num, show 1+(4880711602639131/50000000000000000000 : ℝ)+(103848706136703/20000000000000000000 : ℝ)=(100010280666735961777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4880711602639131/50000000000000000000 : ℝ) ≤ ((12304445384060978803/12305000000000000000 : ℝ)+2*(87902269019/369150000000000 : ℝ)*(8631/50000 : ℝ))^(5383/1024 : ℝ) := by
    rw [show (12304445384060978803/12305000000000000000 : ℝ)+2*(87902269019/369150000000000 : ℝ)*(8631/50000 : ℝ)=(1000037136397631/1000000000000000 : ℝ) by norm_num, show 1+2*(4880711602639131/50000000000000000000 : ℝ)=(25004880711602639131/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12304445384060978803/12305000000000000000 : ℝ)*(X 1 0+X 2 0)+(87902269019/369150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (9879/100000 : ℝ)) (hi := (8631/50000 : ℝ)) (c := (12304445384060978803/12305000000000000000 : ℝ)) (alpha := (87902269019/369150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12304445384060978803/12305000000000000000 : ℝ)*(X 0 1+X 2 1)+(87902269019/369150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (9879/100000 : ℝ)) (hi := (8631/50000 : ℝ)) (c := (12304445384060978803/12305000000000000000 : ℝ)) (alpha := (87902269019/369150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12304445384060978803/12305000000000000000 : ℝ)*(X 0 2+X 1 2)+(87902269019/369150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5383/1024 : ℝ)) (lo := (9879/100000 : ℝ)) (hi := (8631/50000 : ℝ)) (c := (12304445384060978803/12305000000000000000 : ℝ)) (alpha := (87902269019/369150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-686606417/5000000000 : ℝ)*X 0 0+(5463453241/10000000000 : ℝ)*X 0 1+(1027846999/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((533991931/1000000000 : ℝ)*X 1 0+(-1541191031/10000000000 : ℝ)*X 1 1+(2569617439/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((667489893/1250000000 : ℝ)*X 2 0+(5139235017/10000000000 : ℝ)*X 2 1+(-385297767/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4090769107/10000000000 : ℝ)*X 0 0+(3626409223/10000000000 : ℝ)*X 0 1+(91800313/200000000 : ℝ)*X 0 2+(4090769107/10000000000 : ℝ)*X 1 0+(3626409223/10000000000 : ℝ)*X 1 1+(91800313/200000000 : ℝ)*X 1 2+(4090769107/10000000000 : ℝ)*X 2 0+(3626409223/10000000000 : ℝ)*X 2 1+(91800313/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-686679211/5000000000 : ℝ)*X 0 0+(5142867329/10000000000 : ℝ)*X 0 1+(1091953347/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253128663/10000000000 : ℝ)*X 1 0+(-122065919/1000000000 : ℝ)*X 1 1+(5459766747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253128683/10000000000 : ℝ)*X 2 0+(2729883369/5000000000 : ℝ)*X 2 1+(-152582397/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((255700123/625000000 : ℝ)*X 0 0+(4579219637/10000000000 : ℝ)*X 0 1+(1818683127/5000000000 : ℝ)*X 0 2+(255700123/625000000 : ℝ)*X 1 0+(4579219637/10000000000 : ℝ)*X 1 1+(1818683127/5000000000 : ℝ)*X 1 2+(255700123/625000000 : ℝ)*X 2 0+(4579219637/10000000000 : ℝ)*X 2 1+(1818683127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1721_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49557746898854201253303/6152500000000000000000000000 : ℝ) := by norm_num
    linear_combination (580674119/50000000000000 : ℝ)*(base19) + (516067383/50000000000000 : ℝ)*(base23) + (2224817/12500000000000 : ℝ)*(lower2) + (25343081/12500000000000 : ℝ)*(upper3) + (28582703/20000000000000 : ℝ)*(upper5) + (64408438481199/3125000000000 : ℝ)*(major0) + (64408438481199/3125000000000 : ℝ)*(major1) + (64408438481199/3125000000000 : ℝ)*(major2) + (77108832639503/2500000000000 : ℝ)*(sp0) + (616872460922197/20000000000000 : ℝ)*(sp1) + (385545304228057/12500000000000 : ℝ)*(sp2) + (16215187685771/1562500000000 : ℝ)*(sp3) + (10160379103/100000000000000 : ℝ)*(sp4) + (4316451631/100000000000000 : ℝ)*(sp7) + (64861020521311/6250000000000 : ℝ)*(f.failure) + (1542181732979611/50000000000000 : ℝ)*(f.sum) + (44162057447989/6152500000000000000000000000 : ℝ)*base65 + (190886929285931453/38453125000000000000000000000000 : ℝ)*base68 + (37126769407870211/19226562500000000000000000000000 : ℝ)*base69 + (133954520590618953/38453125000000000000000000000000 : ℝ)*base72 + (382462632123/3076250000000000000000000000 : ℝ)*base74 + (360462758687775203/38453125000000000000000000000000 : ℝ)*base76 + (447065841319474797/38453125000000000000000000000000 : ℝ)*base77 + (88478198594182711/19226562500000000000000000000000 : ℝ)*base79 + (8851969090599/6152500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (945227/78125000000000000000 : ℝ)*base89 + (945227/78125000000000000000 : ℝ)*base91 + (945227/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8828882379226002096762315373/615250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1962309701/100000000000000 : ℝ)*(base19) + (2120563051/100000000000000 : ℝ)*(base23) + (156169383/50000000000000 : ℝ)*(upper3) + (6318047/10000000000000 : ℝ)*(lower4) + (73777597/25000000000000 : ℝ)*(upper5) + (2108655560240201/100000000000000 : ℝ)*(major0) + (2108655560240201/100000000000000 : ℝ)*(major1) + (2108655560240201/100000000000000 : ℝ)*(major2) + (18169247909/100000000000000 : ℝ)*(sp1) + (1233812037/6250000000000 : ℝ)*(sp2) + (1577787181779359/50000000000000 : ℝ)*(sp4) + (788888558000277/25000000000000 : ℝ)*(sp5) + (126222100080123/4000000000000 : ℝ)*(sp6) + (212347255717183/20000000000000 : ℝ)*(sp7) + (212347255717183/20000000000000 : ℝ)*(f.failure) + (1577787181779359/50000000000000 : ℝ)*(f.sum) + (19314843692089/18457500000000000000000000000 : ℝ)*base65 + (16888842421084778209/3691500000000000000000000000000000 : ℝ)*base67 + (3237597667020278209/3691500000000000000000000000000000 : ℝ)*base69 + (32510808846999278209/3691500000000000000000000000000000 : ℝ)*base71 + (94654098891551/18457500000000000000000000000 : ℝ)*base74 + (7182777369828278209/3691500000000000000000000000000000 : ℝ)*base75 + (24792251205370778209/3691500000000000000000000000000000 : ℝ)*base77 + (26385635218816778209/3691500000000000000000000000000000 : ℝ)*base79 + (5124806340821/1153593750000000000000000000 : ℝ)*base82 + (54069/250000000000000000000 : ℝ)*base90 + (54069/250000000000000000000 : ℝ)*base92 + (54069/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1721_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8631/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9879/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8511/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1721_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1721_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8511/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1721_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1721_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1721_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8511/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1721_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

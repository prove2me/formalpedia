-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1757_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:24:23.189995+00:00
-- url     : https://prove2.me/submissions/f10f9d1a-dfe9-4afb-8cec-b722ccc71dd6

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
theorem support_rectangle_w1757_s3_0 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-592115453/5000000000 : ℝ)*x 0 + (5487738117/10000000000 : ℝ)*x 1 + (1016604263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592115453/5000000000 : ℝ)^5887 ≤ (1889166625227/25000000000000 : ℝ)^4863 := by
    have hnat : (592115453 : ℕ)^5887*25000000000000^4863 ≤ 1889166625227^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592115453 5000000000 1889166625227 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487738117/10000000000 : ℝ)^5887 ≤ (24181740053299/50000000000000 : ℝ)^4863 := by
    have hnat : (5487738117 : ℕ)^5887*50000000000000^4863 ≤ 24181740053299^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487738117 10000000000 24181740053299 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016604263/2000000000 : ℝ)^5887 ≤ (4407985337909/10000000000000 : ℝ)^4863 := by
    have hnat : (1016604263 : ℕ)^5887*10000000000000^4863 ≤ 4407985337909^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016604263 2000000000 4407985337909 10000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-592115453/5000000000 : ℝ), (5487738117/10000000000 : ℝ), (1016604263/2000000000 : ℝ)] ![(1889166625227/25000000000000 : ℝ), (24181740053299/50000000000000 : ℝ), (4407985337909/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-592115453/5000000000 : ℝ)|^5887 ≤ (1889166625227/25000000000000 : ℝ)^4863
        have hw : |(-592115453/5000000000 : ℝ)|=(592115453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487738117/10000000000 : ℝ)|^5887 ≤ (24181740053299/50000000000000 : ℝ)^4863
        have hw : |(5487738117/10000000000 : ℝ)|=(5487738117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016604263/2000000000 : ℝ)|^5887 ≤ (4407985337909/10000000000000 : ℝ)^4863
        have hw : |(1016604263/2000000000 : ℝ)|=(1016604263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s3_1 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2665703339/5000000000 : ℝ)*x 0 + (-1395687941/10000000000 : ℝ)*x 1 + (5083021507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2665703339/5000000000 : ℝ)^5887 ≤ (46700657945189/100000000000000 : ℝ)^4863 := by
    have hnat : (2665703339 : ℕ)^5887*100000000000000^4863 ≤ 46700657945189^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2665703339 5000000000 46700657945189 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395687941/10000000000 : ℝ)^5887 ≤ (9219486651497/100000000000000 : ℝ)^4863 := by
    have hnat : (1395687941 : ℕ)^5887*100000000000000^4863 ≤ 9219486651497^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395687941 10000000000 9219486651497 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083021507/10000000000 : ℝ)^5887 ≤ (5509981924339/12500000000000 : ℝ)^4863 := by
    have hnat : (5083021507 : ℕ)^5887*12500000000000^4863 ≤ 5509981924339^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083021507 10000000000 5509981924339 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2665703339/5000000000 : ℝ), (-1395687941/10000000000 : ℝ), (5083021507/10000000000 : ℝ)] ![(46700657945189/100000000000000 : ℝ), (9219486651497/100000000000000 : ℝ), (5509981924339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2665703339/5000000000 : ℝ)|^5887 ≤ (46700657945189/100000000000000 : ℝ)^4863
        have hw : |(2665703339/5000000000 : ℝ)|=(2665703339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1395687941/10000000000 : ℝ)|^5887 ≤ (9219486651497/100000000000000 : ℝ)^4863
        have hw : |(-1395687941/10000000000 : ℝ)|=(1395687941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083021507/10000000000 : ℝ)|^5887 ≤ (5509981924339/12500000000000 : ℝ)^4863
        have hw : |(5083021507/10000000000 : ℝ)|=(5083021507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s3_2 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166606447/312500000 : ℝ)*x 0 + (2541510809/5000000000 : ℝ)*x 1 + (-139568829/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166606447/312500000 : ℝ)^5887 ≤ (23350326989641/50000000000000 : ℝ)^4863 := by
    have hnat : (166606447 : ℕ)^5887*50000000000000^4863 ≤ 23350326989641^4863*312500000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166606447 312500000 23350326989641 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541510809/5000000000 : ℝ)^5887 ≤ (22039928279997/50000000000000 : ℝ)^4863 := by
    have hnat : (2541510809 : ℕ)^5887*50000000000000^4863 ≤ 22039928279997^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541510809 5000000000 22039928279997 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139568829/1000000000 : ℝ)^5887 ≤ (9219489442329/100000000000000 : ℝ)^4863 := by
    have hnat : (139568829 : ℕ)^5887*100000000000000^4863 ≤ 9219489442329^4863*1000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139568829 1000000000 9219489442329 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166606447/312500000 : ℝ), (2541510809/5000000000 : ℝ), (-139568829/1000000000 : ℝ)] ![(23350326989641/50000000000000 : ℝ), (22039928279997/50000000000000 : ℝ), (9219489442329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166606447/312500000 : ℝ)|^5887 ≤ (23350326989641/50000000000000 : ℝ)^4863
        have hw : |(166606447/312500000 : ℝ)|=(166606447/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541510809/5000000000 : ℝ)|^5887 ≤ (22039928279997/50000000000000 : ℝ)^4863
        have hw : |(2541510809/5000000000 : ℝ)|=(2541510809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139568829/1000000000 : ℝ)|^5887 ≤ (9219489442329/100000000000000 : ℝ)^4863
        have hw : |(-139568829/1000000000 : ℝ)|=(139568829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s3_3 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4006582213/10000000000 : ℝ)*x 0 + (3353446569/10000000000 : ℝ)*x 1 + (4721220459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4006582213/10000000000 : ℝ)^5887 ≤ (16523435616263/50000000000000 : ℝ)^4863 := by
    have hnat : (4006582213 : ℕ)^5887*50000000000000^4863 ≤ 16523435616263^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006582213 10000000000 16523435616263 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3353446569/10000000000 : ℝ)^5887 ≤ (26642458602147/100000000000000 : ℝ)^4863 := by
    have hnat : (3353446569 : ℕ)^5887*100000000000000^4863 ≤ 26642458602147^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3353446569 10000000000 26642458602147 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4721220459/10000000000 : ℝ)^5887 ≤ (8062134031583/20000000000000 : ℝ)^4863 := by
    have hnat : (4721220459 : ℕ)^5887*20000000000000^4863 ≤ 8062134031583^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4721220459 10000000000 8062134031583 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4006582213/10000000000 : ℝ), (3353446569/10000000000 : ℝ), (4721220459/10000000000 : ℝ)] ![(16523435616263/50000000000000 : ℝ), (26642458602147/100000000000000 : ℝ), (8062134031583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4006582213/10000000000 : ℝ)|^5887 ≤ (16523435616263/50000000000000 : ℝ)^4863
        have hw : |(4006582213/10000000000 : ℝ)|=(4006582213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3353446569/10000000000 : ℝ)|^5887 ≤ (26642458602147/100000000000000 : ℝ)^4863
        have hw : |(3353446569/10000000000 : ℝ)|=(3353446569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4721220459/10000000000 : ℝ)|^5887 ≤ (8062134031583/20000000000000 : ℝ)^4863
        have hw : |(4721220459/10000000000 : ℝ)|=(4721220459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s3_4 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-592283781/5000000000 : ℝ)*x 0 + (2544839191/5000000000 : ℝ)*x 1 + (2740471013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592283781/5000000000 : ℝ)^5887 ≤ (7559267157373/100000000000000 : ℝ)^4863 := by
    have hnat : (592283781 : ℕ)^5887*100000000000000^4863 ≤ 7559267157373^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592283781 5000000000 7559267157373 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544839191/5000000000 : ℝ)^5887 ≤ (22074874564103/50000000000000 : ℝ)^4863 := by
    have hnat : (2544839191 : ℕ)^5887*50000000000000^4863 ≤ 22074874564103^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544839191 5000000000 22074874564103 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740471013/5000000000 : ℝ)^5887 ≤ (48290983701849/100000000000000 : ℝ)^4863 := by
    have hnat : (2740471013 : ℕ)^5887*100000000000000^4863 ≤ 48290983701849^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740471013 5000000000 48290983701849 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-592283781/5000000000 : ℝ), (2544839191/5000000000 : ℝ), (2740471013/5000000000 : ℝ)] ![(7559267157373/100000000000000 : ℝ), (22074874564103/50000000000000 : ℝ), (48290983701849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-592283781/5000000000 : ℝ)|^5887 ≤ (7559267157373/100000000000000 : ℝ)^4863
        have hw : |(-592283781/5000000000 : ℝ)|=(592283781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544839191/5000000000 : ℝ)|^5887 ≤ (22074874564103/50000000000000 : ℝ)^4863
        have hw : |(2544839191/5000000000 : ℝ)|=(2544839191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740471013/5000000000 : ℝ)|^5887 ≤ (48290983701849/100000000000000 : ℝ)^4863
        have hw : |(2740471013/5000000000 : ℝ)|=(2740471013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s3_5 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044868861/2000000000 : ℝ)*x 0 + (1370235593/2500000000 : ℝ)*x 1 + (-249442017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044868861/2000000000 : ℝ)^5887 ≤ (45567778430181/100000000000000 : ℝ)^4863 := by
    have hnat : (1044868861 : ℕ)^5887*100000000000000^4863 ≤ 45567778430181^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044868861 2000000000 45567778430181 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370235593/2500000000 : ℝ)^5887 ≤ (12072746848069/25000000000000 : ℝ)^4863 := by
    have hnat : (1370235593 : ℕ)^5887*25000000000000^4863 ≤ 12072746848069^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370235593 2500000000 12072746848069 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249442017/2500000000 : ℝ)^5887 ≤ (6141234162053/100000000000000 : ℝ)^4863 := by
    have hnat : (249442017 : ℕ)^5887*100000000000000^4863 ≤ 6141234162053^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249442017 2500000000 6141234162053 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044868861/2000000000 : ℝ), (1370235593/2500000000 : ℝ), (-249442017/2500000000 : ℝ)] ![(45567778430181/100000000000000 : ℝ), (12072746848069/25000000000000 : ℝ), (6141234162053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044868861/2000000000 : ℝ)|^5887 ≤ (45567778430181/100000000000000 : ℝ)^4863
        have hw : |(1044868861/2000000000 : ℝ)|=(1044868861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370235593/2500000000 : ℝ)|^5887 ≤ (12072746848069/25000000000000 : ℝ)^4863
        have hw : |(1370235593/2500000000 : ℝ)|=(1370235593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249442017/2500000000 : ℝ)|^5887 ≤ (6141234162053/100000000000000 : ℝ)^4863
        have hw : |(-249442017/2500000000 : ℝ)|=(249442017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s3_6 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4007720429/10000000000 : ℝ)*x 0 + (4698722099/10000000000 : ℝ)*x 1 + (3376414919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4007720429/10000000000 : ℝ)^5887 ≤ (33058236606499/100000000000000 : ℝ)^4863 := by
    have hnat : (4007720429 : ℕ)^5887*100000000000000^4863 ≤ 33058236606499^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007720429 10000000000 33058236606499 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4698722099/10000000000 : ℝ)^5887 ≤ (40078242319909/100000000000000 : ℝ)^4863 := by
    have hnat : (4698722099 : ℕ)^5887*100000000000000^4863 ≤ 40078242319909^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698722099 10000000000 40078242319909 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3376414919/10000000000 : ℝ)^5887 ≤ (1678970065573/6250000000000 : ℝ)^4863 := by
    have hnat : (3376414919 : ℕ)^5887*6250000000000^4863 ≤ 1678970065573^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3376414919 10000000000 1678970065573 6250000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4007720429/10000000000 : ℝ), (4698722099/10000000000 : ℝ), (3376414919/10000000000 : ℝ)] ![(33058236606499/100000000000000 : ℝ), (40078242319909/100000000000000 : ℝ), (1678970065573/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4007720429/10000000000 : ℝ)|^5887 ≤ (33058236606499/100000000000000 : ℝ)^4863
        have hw : |(4007720429/10000000000 : ℝ)|=(4007720429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4698722099/10000000000 : ℝ)|^5887 ≤ (40078242319909/100000000000000 : ℝ)^4863
        have hw : |(4698722099/10000000000 : ℝ)|=(4698722099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3376414919/10000000000 : ℝ)|^5887 ≤ (1678970065573/6250000000000 : ℝ)^4863
        have hw : |(3376414919/10000000000 : ℝ)|=(3376414919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1757_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (223/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2281/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (223/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (223/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9123/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (223/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9123/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (223/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9123/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (223/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9123/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (223/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9123/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (223/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9123/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9123/100000 : ℝ) ^ (5871/1024 : ℝ) ≤ (545789245901/500000000000000000 : ℝ) := by
    have hpowers : (9123/100000 : ℝ)^5871 ≤ (545789245901/500000000000000000 : ℝ)^1024 := by
      have hnat : (9123 : ℕ)^5871*500000000000000000^1024 ≤ 545789245901^1024*100000^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9123 100000 545789245901 500000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9123/100000 : ℝ)) (X := (545789245901/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (223/1250 : ℝ) ^ (5871/1024 : ℝ) ≤ (2552221760875927/50000000000000000000 : ℝ) := by
    have hpowers : (223/1250 : ℝ)^5871 ≤ (2552221760875927/50000000000000000000 : ℝ)^1024 := by
      have hnat : (223 : ℕ)^5871*50000000000000000000^1024 ≤ 2552221760875927^1024*1250^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 1250 2552221760875927 50000000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/1250 : ℝ)) (X := (2552221760875927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250000545789245901/250000000000000000 : ℝ) ≤ (5000001903892639/5000000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (250000545789245901/250000000000000000 : ℝ)^1024 ≤ (5000001903892639/5000000000000000 : ℝ)^5871 := by
      have hnat : (250000545789245901 : ℕ)^1024*5000000000000000^5871 ≤ 5000001903892639^5871*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250000545789245901 250000000000000000 5000001903892639 5000000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001903892639/5000000000000000 : ℝ)) (X := (250000545789245901/250000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50002606800685466027/50000000000000000000 : ℝ) ≤ (1000009093191809/1000000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (50002606800685466027/50000000000000000000 : ℝ)^1024 ≤ (1000009093191809/1000000000000000 : ℝ)^5871 := by
      have hnat : (50002606800685466027 : ℕ)^1024*1000000000000000^5871 ≤ 1000009093191809^5871*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002606800685466027 50000000000000000000 1000009093191809 1000000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000009093191809/1000000000000000 : ℝ)) (X := (50002606800685466027/50000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002552221760875927/25000000000000000000 : ℝ) ≤ (5000089028025451/5000000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (25002552221760875927/25000000000000000000 : ℝ)^1024 ≤ (5000089028025451/5000000000000000 : ℝ)^5871 := by
      have hnat : (25002552221760875927 : ℕ)^1024*5000000000000000^5871 ≤ 5000089028025451^5871*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002552221760875927 25000000000000000000 5000089028025451 5000000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000089028025451/5000000000000000 : ℝ)) (X := (25002552221760875927/25000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(545789245901/500000000000000000 : ℝ) ≤ ((43584221762768490287/43585000000000000000 : ℝ)+2*(21781033203/217925000000000 : ℝ)*(9123/100000 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (43584221762768490287/43585000000000000000 : ℝ)+2*(21781033203/217925000000000 : ℝ)*(9123/100000 : ℝ)=(5000001903892639/5000000000000000 : ℝ) by norm_num, show 1+2*(545789245901/500000000000000000 : ℝ)=(250000545789245901/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2552221760875927/50000000000000000000 : ℝ)+(545789245901/500000000000000000 : ℝ) ≤ ((43584221762768490287/43585000000000000000 : ℝ)+(21781033203/217925000000000 : ℝ)*((223/1250 : ℝ)+(9123/100000 : ℝ)))^(5871/1024 : ℝ) := by
    rw [show (43584221762768490287/43585000000000000000 : ℝ)+(21781033203/217925000000000 : ℝ)*((223/1250 : ℝ)+(9123/100000 : ℝ))=(1000009093191809/1000000000000000 : ℝ) by norm_num, show 1+(2552221760875927/50000000000000000000 : ℝ)+(545789245901/500000000000000000 : ℝ)=(50002606800685466027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2552221760875927/50000000000000000000 : ℝ) ≤ ((43584221762768490287/43585000000000000000 : ℝ)+2*(21781033203/217925000000000 : ℝ)*(223/1250 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (43584221762768490287/43585000000000000000 : ℝ)+2*(21781033203/217925000000000 : ℝ)*(223/1250 : ℝ)=(5000089028025451/5000000000000000 : ℝ) by norm_num, show 1+2*(2552221760875927/50000000000000000000 : ℝ)=(25002552221760875927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43584221762768490287/43585000000000000000 : ℝ)*(X 1 0+X 2 0)+(21781033203/217925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (9123/100000 : ℝ)) (hi := (223/1250 : ℝ)) (c := (43584221762768490287/43585000000000000000 : ℝ)) (alpha := (21781033203/217925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43584221762768490287/43585000000000000000 : ℝ)*(X 0 1+X 2 1)+(21781033203/217925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (9123/100000 : ℝ)) (hi := (223/1250 : ℝ)) (c := (43584221762768490287/43585000000000000000 : ℝ)) (alpha := (21781033203/217925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43584221762768490287/43585000000000000000 : ℝ)*(X 0 2+X 1 2)+(21781033203/217925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (9123/100000 : ℝ)) (hi := (223/1250 : ℝ)) (c := (43584221762768490287/43585000000000000000 : ℝ)) (alpha := (21781033203/217925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-592115453/5000000000 : ℝ)*X 0 0+(5487738117/10000000000 : ℝ)*X 0 1+(1016604263/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2665703339/5000000000 : ℝ)*X 1 0+(-1395687941/10000000000 : ℝ)*X 1 1+(5083021507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((166606447/312500000 : ℝ)*X 2 0+(2541510809/5000000000 : ℝ)*X 2 1+(-139568829/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4006582213/10000000000 : ℝ)*X 0 0+(3353446569/10000000000 : ℝ)*X 0 1+(4721220459/10000000000 : ℝ)*X 0 2+(4006582213/10000000000 : ℝ)*X 1 0+(3353446569/10000000000 : ℝ)*X 1 1+(4721220459/10000000000 : ℝ)*X 1 2+(4006582213/10000000000 : ℝ)*X 2 0+(3353446569/10000000000 : ℝ)*X 2 1+(4721220459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-592283781/5000000000 : ℝ)*X 0 0+(2544839191/5000000000 : ℝ)*X 0 1+(2740471013/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1044868861/2000000000 : ℝ)*X 2 0+(1370235593/2500000000 : ℝ)*X 2 1+(-249442017/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s3_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4007720429/10000000000 : ℝ)*X 0 0+(4698722099/10000000000 : ℝ)*X 0 1+(3376414919/10000000000 : ℝ)*X 0 2+(4007720429/10000000000 : ℝ)*X 1 0+(4698722099/10000000000 : ℝ)*X 1 1+(3376414919/10000000000 : ℝ)*X 1 2+(4007720429/10000000000 : ℝ)*X 2 0+(4698722099/10000000000 : ℝ)*X 2 1+(3376414919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3716856876366991560682567839/1089625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24909693/4000000000000 : ℝ)*(base19) + (228618697/50000000000000 : ℝ)*(base23) + (79846841/50000000000000 : ℝ)*(upper3) + (8594477/100000000000000 : ℝ)*(lower4) + (800498816951699/50000000000000 : ℝ)*(major0) + (800498816951699/50000000000000 : ℝ)*(major1) + (800498816951699/50000000000000 : ℝ)*(major2) + (1235435647636891/50000000000000 : ℝ)*(sp0) + (2470875546572867/100000000000000 : ℝ)*(sp1) + (49417505982537/2000000000000 : ℝ)*(sp2) + (91389588450621/12500000000000 : ℝ)*(sp3) + (487404141/10000000000000 : ℝ)*(sp4) + (103237737/25000000000000 : ℝ)*(sp5) + (2277182167/100000000000000 : ℝ)*(sp6) + (146223796957427/20000000000000 : ℝ)*(f.failure) + (308859521164399/12500000000000 : ℝ)*(f.sum) + (13611918424901/43585000000000000000000000000 : ℝ)*base65 + (6678879112181702387/2179250000000000000000000000000000 : ℝ)*base68 + (7650256560159702387/2179250000000000000000000000000000 : ℝ)*base70 + (4770987609291202387/2179250000000000000000000000000000 : ℝ)*base72 + (7331342325773/21792500000000000000000000000 : ℝ)*base73 + (7440374254445452387/2179250000000000000000000000000000 : ℝ)*base76 + (8138000879974297613/2179250000000000000000000000000000 : ℝ)*base77 + (13712221830889797613/2179250000000000000000000000000000 : ℝ)*base79 + (119928158978109/43585000000000000000000000000 : ℝ)*base82 + (584587/2000000000000000000000 : ℝ)*base89 + (584587/2000000000000000000000 : ℝ)*base91 + (584587/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1757_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (223/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (223/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1757_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1757_box_0 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16175521/200000000 : ℝ)*x 0 + (1354457911/2500000000 : ℝ)*x 1 + (2708915697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16175521/200000000 : ℝ)^5887 ≤ (952533170323/20000000000000 : ℝ)^4863 := by
    have hnat : (16175521 : ℕ)^5887*20000000000000^4863 ≤ 952533170323^4863*200000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16175521 200000000 952533170323 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354457911/2500000000 : ℝ)^5887 ≤ (47618668397583/100000000000000 : ℝ)^4863 := by
    have hnat : (1354457911 : ℕ)^5887*100000000000000^4863 ≤ 47618668397583^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354457911 2500000000 47618668397583 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708915697/5000000000 : ℝ)^5887 ≤ (2976166608599/6250000000000 : ℝ)^4863 := by
    have hnat : (2708915697 : ℕ)^5887*6250000000000^4863 ≤ 2976166608599^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708915697 5000000000 2976166608599 6250000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16175521/200000000 : ℝ), (1354457911/2500000000 : ℝ), (2708915697/5000000000 : ℝ)] ![(952533170323/20000000000000 : ℝ), (47618668397583/100000000000000 : ℝ), (2976166608599/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16175521/200000000 : ℝ)|^5887 ≤ (952533170323/20000000000000 : ℝ)^4863
        have hw : |(-16175521/200000000 : ℝ)|=(16175521/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354457911/2500000000 : ℝ)|^5887 ≤ (47618668397583/100000000000000 : ℝ)^4863
        have hw : |(1354457911/2500000000 : ℝ)|=(1354457911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708915697/5000000000 : ℝ)|^5887 ≤ (2976166608599/6250000000000 : ℝ)^4863
        have hw : |(2708915697/5000000000 : ℝ)|=(2708915697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_1 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596824859/5000000000 : ℝ)*x 0 + (-112969439/1000000000 : ℝ)*x 1 + (5417831371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596824859/5000000000 : ℝ)^5887 ≤ (45243880270921/100000000000000 : ℝ)^4863 := by
    have hnat : (2596824859 : ℕ)^5887*100000000000000^4863 ≤ 45243880270921^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596824859 5000000000 45243880270921 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112969439/1000000000 : ℝ)^5887 ≤ (285498168967/4000000000000 : ℝ)^4863 := by
    have hnat : (112969439 : ℕ)^5887*4000000000000^4863 ≤ 285498168967^4863*1000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112969439 1000000000 285498168967 4000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417831371/10000000000 : ℝ)^5887 ≤ (372020824163/781250000000 : ℝ)^4863 := by
    have hnat : (5417831371 : ℕ)^5887*781250000000^4863 ≤ 372020824163^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417831371 10000000000 372020824163 781250000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596824859/5000000000 : ℝ), (-112969439/1000000000 : ℝ), (5417831371/10000000000 : ℝ)] ![(45243880270921/100000000000000 : ℝ), (285498168967/4000000000000 : ℝ), (372020824163/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596824859/5000000000 : ℝ)|^5887 ≤ (45243880270921/100000000000000 : ℝ)^4863
        have hw : |(2596824859/5000000000 : ℝ)|=(2596824859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112969439/1000000000 : ℝ)|^5887 ≤ (285498168967/4000000000000 : ℝ)^4863
        have hw : |(-112969439/1000000000 : ℝ)|=(112969439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417831371/10000000000 : ℝ)|^5887 ≤ (372020824163/781250000000 : ℝ)^4863
        have hw : |(5417831371/10000000000 : ℝ)|=(5417831371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_2 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324603091/625000000 : ℝ)*x 0 + (5417831537/10000000000 : ℝ)*x 1 + (-1129694519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324603091/625000000 : ℝ)^5887 ≤ (22621938753969/50000000000000 : ℝ)^4863 := by
    have hnat : (324603091 : ℕ)^5887*50000000000000^4863 ≤ 22621938753969^4863*625000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324603091 625000000 22621938753969 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417831537/10000000000 : ℝ)^5887 ≤ (1488083351847/3125000000000 : ℝ)^4863 := by
    have hnat : (5417831537 : ℕ)^5887*3125000000000^4863 ≤ 1488083351847^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417831537 10000000000 1488083351847 3125000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129694519/10000000000 : ℝ)^5887 ≤ (3568727605411/50000000000000 : ℝ)^4863 := by
    have hnat : (1129694519 : ℕ)^5887*50000000000000^4863 ≤ 3568727605411^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129694519 10000000000 3568727605411 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324603091/625000000 : ℝ), (5417831537/10000000000 : ℝ), (-1129694519/10000000000 : ℝ)] ![(22621938753969/50000000000000 : ℝ), (1488083351847/3125000000000 : ℝ), (3568727605411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324603091/625000000 : ℝ)|^5887 ≤ (22621938753969/50000000000000 : ℝ)^4863
        have hw : |(324603091/625000000 : ℝ)|=(324603091/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417831537/10000000000 : ℝ)|^5887 ≤ (1488083351847/3125000000000 : ℝ)^4863
        have hw : |(5417831537/10000000000 : ℝ)|=(5417831537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129694519/10000000000 : ℝ)|^5887 ≤ (3568727605411/50000000000000 : ℝ)^4863
        have hw : |(-1129694519/10000000000 : ℝ)|=(1129694519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_3 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (566477913/1250000000 : ℝ)*x 0 + (378214573/1000000000 : ℝ)*x 1 + (472768157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566477913/1250000000 : ℝ)^5887 ≤ (4795175595533/12500000000000 : ℝ)^4863 := by
    have hnat : (566477913 : ℕ)^5887*12500000000000^4863 ≤ 4795175595533^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566477913 1250000000 4795175595533 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378214573/1000000000 : ℝ)^5887 ≤ (30819299948477/100000000000000 : ℝ)^4863 := by
    have hnat : (378214573 : ℕ)^5887*100000000000000^4863 ≤ 30819299948477^4863*1000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378214573 1000000000 30819299948477 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472768157/1250000000 : ℝ)^5887 ≤ (30819295272713/100000000000000 : ℝ)^4863 := by
    have hnat : (472768157 : ℕ)^5887*100000000000000^4863 ≤ 30819295272713^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472768157 1250000000 30819295272713 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(566477913/1250000000 : ℝ), (378214573/1000000000 : ℝ), (472768157/1250000000 : ℝ)] ![(4795175595533/12500000000000 : ℝ), (30819299948477/100000000000000 : ℝ), (30819295272713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(566477913/1250000000 : ℝ)|^5887 ≤ (4795175595533/12500000000000 : ℝ)^4863
        have hw : |(566477913/1250000000 : ℝ)|=(566477913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(378214573/1000000000 : ℝ)|^5887 ≤ (30819299948477/100000000000000 : ℝ)^4863
        have hw : |(378214573/1000000000 : ℝ)|=(378214573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(472768157/1250000000 : ℝ)|^5887 ≤ (30819295272713/100000000000000 : ℝ)^4863
        have hw : |(472768157/1250000000 : ℝ)|=(472768157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_4 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1598942177/10000000000 : ℝ)*x 0 + (1025848881/2000000000 : ℝ)*x 1 + (5129244367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1598942177/10000000000 : ℝ)^5887 ≤ (2717215878841/25000000000000 : ℝ)^4863 := by
    have hnat : (1598942177 : ℕ)^5887*25000000000000^4863 ≤ 2717215878841^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598942177 10000000000 2717215878841 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025848881/2000000000 : ℝ)^5887 ≤ (22282784216971/50000000000000 : ℝ)^4863 := by
    have hnat : (1025848881 : ℕ)^5887*50000000000000^4863 ≤ 22282784216971^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025848881 2000000000 22282784216971 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129244367/10000000000 : ℝ)^5887 ≤ (2785348002141/6250000000000 : ℝ)^4863 := by
    have hnat : (5129244367 : ℕ)^5887*6250000000000^4863 ≤ 2785348002141^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129244367 10000000000 2785348002141 6250000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1598942177/10000000000 : ℝ), (1025848881/2000000000 : ℝ), (5129244367/10000000000 : ℝ)] ![(2717215878841/25000000000000 : ℝ), (22282784216971/50000000000000 : ℝ), (2785348002141/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1598942177/10000000000 : ℝ)|^5887 ≤ (2717215878841/25000000000000 : ℝ)^4863
        have hw : |(-1598942177/10000000000 : ℝ)|=(1598942177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1025848881/2000000000 : ℝ)|^5887 ≤ (22282784216971/50000000000000 : ℝ)^4863
        have hw : |(1025848881/2000000000 : ℝ)|=(1025848881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129244367/10000000000 : ℝ)|^5887 ≤ (2785348002141/6250000000000 : ℝ)^4863
        have hw : |(5129244367/10000000000 : ℝ)|=(5129244367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_5 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386270189/10000000000 : ℝ)*x 0 + (-1260706711/10000000000 : ℝ)*x 1 + (5129244263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386270189/10000000000 : ℝ)^5887 ≤ (47283060892199/100000000000000 : ℝ)^4863 := by
    have hnat : (5386270189 : ℕ)^5887*100000000000000^4863 ≤ 47283060892199^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386270189 10000000000 47283060892199 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1260706711/10000000000 : ℝ)^5887 ≤ (326054886199/4000000000000 : ℝ)^4863 := by
    have hnat : (1260706711 : ℕ)^5887*4000000000000^4863 ≤ 326054886199^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260706711 10000000000 326054886199 4000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129244263/10000000000 : ℝ)^5887 ≤ (44565566940377/100000000000000 : ℝ)^4863 := by
    have hnat : (5129244263 : ℕ)^5887*100000000000000^4863 ≤ 44565566940377^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129244263 10000000000 44565566940377 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386270189/10000000000 : ℝ), (-1260706711/10000000000 : ℝ), (5129244263/10000000000 : ℝ)] ![(47283060892199/100000000000000 : ℝ), (326054886199/4000000000000 : ℝ), (44565566940377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386270189/10000000000 : ℝ)|^5887 ≤ (47283060892199/100000000000000 : ℝ)^4863
        have hw : |(5386270189/10000000000 : ℝ)|=(5386270189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1260706711/10000000000 : ℝ)|^5887 ≤ (326054886199/4000000000000 : ℝ)^4863
        have hw : |(-1260706711/10000000000 : ℝ)|=(1260706711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129244263/10000000000 : ℝ)|^5887 ≤ (44565566940377/100000000000000 : ℝ)^4863
        have hw : |(5129244263/10000000000 : ℝ)|=(5129244263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_6 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538626989/1000000000 : ℝ)*x 0 + (2564622283/5000000000 : ℝ)*x 1 + (-126070671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538626989/1000000000 : ℝ)^5887 ≤ (47283057714751/100000000000000 : ℝ)^4863 := by
    have hnat : (538626989 : ℕ)^5887*100000000000000^4863 ≤ 47283057714751^4863*1000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538626989 1000000000 47283057714751 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564622283/5000000000 : ℝ)^5887 ≤ (44565570127351/100000000000000 : ℝ)^4863 := by
    have hnat : (2564622283 : ℕ)^5887*100000000000000^4863 ≤ 44565570127351^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564622283 5000000000 44565570127351 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126070671/1000000000 : ℝ)^5887 ≤ (2037843036787/25000000000000 : ℝ)^4863 := by
    have hnat : (126070671 : ℕ)^5887*25000000000000^4863 ≤ 2037843036787^4863*1000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126070671 1000000000 2037843036787 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538626989/1000000000 : ℝ), (2564622283/5000000000 : ℝ), (-126070671/1000000000 : ℝ)] ![(47283057714751/100000000000000 : ℝ), (44565570127351/100000000000000 : ℝ), (2037843036787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538626989/1000000000 : ℝ)|^5887 ≤ (47283057714751/100000000000000 : ℝ)^4863
        have hw : |(538626989/1000000000 : ℝ)|=(538626989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564622283/5000000000 : ℝ)|^5887 ≤ (44565570127351/100000000000000 : ℝ)^4863
        have hw : |(2564622283/5000000000 : ℝ)|=(2564622283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126070671/1000000000 : ℝ)|^5887 ≤ (2037843036787/25000000000000 : ℝ)^4863
        have hw : |(-126070671/1000000000 : ℝ)|=(126070671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_7 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3443516519/10000000000 : ℝ)*x 0 + (540527643/1250000000 : ℝ)*x 1 + (67565953/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3443516519/10000000000 : ℝ)^5887 ≤ (27511159806753/100000000000000 : ℝ)^4863 := by
    have hnat : (3443516519 : ℕ)^5887*100000000000000^4863 ≤ 27511159806753^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3443516519 10000000000 27511159806753 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540527643/1250000000 : ℝ)^5887 ≤ (18122210429967/50000000000000 : ℝ)^4863 := by
    have hnat : (540527643 : ℕ)^5887*50000000000000^4863 ≤ 18122210429967^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540527643 1250000000 18122210429967 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67565953/156250000 : ℝ)^5887 ≤ (18122209658821/50000000000000 : ℝ)^4863 := by
    have hnat : (67565953 : ℕ)^5887*50000000000000^4863 ≤ 18122209658821^4863*156250000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67565953 156250000 18122209658821 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3443516519/10000000000 : ℝ), (540527643/1250000000 : ℝ), (67565953/156250000 : ℝ)] ![(27511159806753/100000000000000 : ℝ), (18122210429967/50000000000000 : ℝ), (18122209658821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3443516519/10000000000 : ℝ)|^5887 ≤ (27511159806753/100000000000000 : ℝ)^4863
        have hw : |(3443516519/10000000000 : ℝ)|=(3443516519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540527643/1250000000 : ℝ)|^5887 ≤ (18122210429967/50000000000000 : ℝ)^4863
        have hw : |(540527643/1250000000 : ℝ)|=(540527643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67565953/156250000 : ℝ)|^5887 ≤ (18122209658821/50000000000000 : ℝ)^4863
        have hw : |(67565953/156250000 : ℝ)|=(67565953/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_8 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426925121/10000000000 : ℝ)*x 0 + (153400177/312500000 : ℝ)*x 1 + (1095842619/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426925121/10000000000 : ℝ)^5887 ≤ (9469864679561/100000000000000 : ℝ)^4863 := by
    have hnat : (1426925121 : ℕ)^5887*100000000000000^4863 ≤ 9469864679561^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426925121 10000000000 9469864679561 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153400177/312500000 : ℝ)^5887 ≤ (42257591726461/100000000000000 : ℝ)^4863 := by
    have hnat : (153400177 : ℕ)^5887*100000000000000^4863 ≤ 42257591726461^4863*312500000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153400177 312500000 42257591726461 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095842619/2000000000 : ℝ)^5887 ≤ (9654508715491/20000000000000 : ℝ)^4863 := by
    have hnat : (1095842619 : ℕ)^5887*20000000000000^4863 ≤ 9654508715491^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095842619 2000000000 9654508715491 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426925121/10000000000 : ℝ), (153400177/312500000 : ℝ), (1095842619/2000000000 : ℝ)] ![(9469864679561/100000000000000 : ℝ), (42257591726461/100000000000000 : ℝ), (9654508715491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426925121/10000000000 : ℝ)|^5887 ≤ (9469864679561/100000000000000 : ℝ)^4863
        have hw : |(-1426925121/10000000000 : ℝ)|=(1426925121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153400177/312500000 : ℝ)|^5887 ≤ (42257591726461/100000000000000 : ℝ)^4863
        have hw : |(153400177/312500000 : ℝ)|=(153400177/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095842619/2000000000 : ℝ)|^5887 ≤ (9654508715491/20000000000000 : ℝ)^4863
        have hw : |(1095842619/2000000000 : ℝ)|=(1095842619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_9 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576376047/5000000000 : ℝ)*x 0 + (-4298693/39062500 : ℝ)*x 1 + (5479213261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576376047/5000000000 : ℝ)^5887 ≤ (44812942983343/100000000000000 : ℝ)^4863 := by
    have hnat : (2576376047 : ℕ)^5887*100000000000000^4863 ≤ 44812942983343^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576376047 5000000000 44812942983343 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4298693/39062500 : ℝ)^5887 ≤ (864313957937/12500000000000 : ℝ)^4863 := by
    have hnat : (4298693 : ℕ)^5887*12500000000000^4863 ≤ 864313957937^4863*39062500^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298693 39062500 864313957937 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479213261/10000000000 : ℝ)^5887 ≤ (4827254534789/10000000000000 : ℝ)^4863 := by
    have hnat : (5479213261 : ℕ)^5887*10000000000000^4863 ≤ 4827254534789^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479213261 10000000000 4827254534789 10000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576376047/5000000000 : ℝ), (-4298693/39062500 : ℝ), (5479213261/10000000000 : ℝ)] ![(44812942983343/100000000000000 : ℝ), (864313957937/12500000000000 : ℝ), (4827254534789/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576376047/5000000000 : ℝ)|^5887 ≤ (44812942983343/100000000000000 : ℝ)^4863
        have hw : |(2576376047/5000000000 : ℝ)|=(2576376047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4298693/39062500 : ℝ)|^5887 ≤ (864313957937/12500000000000 : ℝ)^4863
        have hw : |(-4298693/39062500 : ℝ)|=(4298693/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479213261/10000000000 : ℝ)|^5887 ≤ (4827254534789/10000000000000 : ℝ)^4863
        have hw : |(5479213261/10000000000 : ℝ)|=(5479213261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_10 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152752287/10000000000 : ℝ)*x 0 + (8561271/15625000 : ℝ)*x 1 + (-137558111/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152752287/10000000000 : ℝ)^5887 ≤ (8962589003057/20000000000000 : ℝ)^4863 := by
    have hnat : (5152752287 : ℕ)^5887*20000000000000^4863 ≤ 8962589003057^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152752287 10000000000 8962589003057 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8561271/15625000 : ℝ)^5887 ≤ (48272547256973/100000000000000 : ℝ)^4863 := by
    have hnat : (8561271 : ℕ)^5887*100000000000000^4863 ≤ 48272547256973^4863*15625000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8561271 15625000 48272547256973 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137558111/1250000000 : ℝ)^5887 ≤ (6914507708207/100000000000000 : ℝ)^4863 := by
    have hnat : (137558111 : ℕ)^5887*100000000000000^4863 ≤ 6914507708207^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137558111 1250000000 6914507708207 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152752287/10000000000 : ℝ), (8561271/15625000 : ℝ), (-137558111/1250000000 : ℝ)] ![(8962589003057/20000000000000 : ℝ), (48272547256973/100000000000000 : ℝ), (6914507708207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152752287/10000000000 : ℝ)|^5887 ≤ (8962589003057/20000000000000 : ℝ)^4863
        have hw : |(5152752287/10000000000 : ℝ)|=(5152752287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8561271/15625000 : ℝ)|^5887 ≤ (48272547256973/100000000000000 : ℝ)^4863
        have hw : |(8561271/15625000 : ℝ)|=(8561271/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137558111/1250000000 : ℝ)|^5887 ≤ (6914507708207/100000000000000 : ℝ)^4863
        have hw : |(-137558111/1250000000 : ℝ)|=(137558111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_11 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1188196951/2500000000 : ℝ)*x 0 + (458302331/1250000000 : ℝ)*x 1 + (3666416437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1188196951/2500000000 : ℝ)^5887 ≤ (20318590889933/50000000000000 : ℝ)^4863 := by
    have hnat : (1188196951 : ℕ)^5887*50000000000000^4863 ≤ 20318590889933^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188196951 2500000000 20318590889933 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458302331/1250000000 : ℝ)^5887 ≤ (29681419935901/100000000000000 : ℝ)^4863 := by
    have hnat : (458302331 : ℕ)^5887*100000000000000^4863 ≤ 29681419935901^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458302331 1250000000 29681419935901 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3666416437/10000000000 : ℝ)^5887 ≤ (29681398267787/100000000000000 : ℝ)^4863 := by
    have hnat : (3666416437 : ℕ)^5887*100000000000000^4863 ≤ 29681398267787^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3666416437 10000000000 29681398267787 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1188196951/2500000000 : ℝ), (458302331/1250000000 : ℝ), (3666416437/10000000000 : ℝ)] ![(20318590889933/50000000000000 : ℝ), (29681419935901/100000000000000 : ℝ), (29681398267787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1188196951/2500000000 : ℝ)|^5887 ≤ (20318590889933/50000000000000 : ℝ)^4863
        have hw : |(1188196951/2500000000 : ℝ)|=(1188196951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458302331/1250000000 : ℝ)|^5887 ≤ (29681419935901/100000000000000 : ℝ)^4863
        have hw : |(458302331/1250000000 : ℝ)|=(458302331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3666416437/10000000000 : ℝ)|^5887 ≤ (29681398267787/100000000000000 : ℝ)^4863
        have hw : |(3666416437/10000000000 : ℝ)|=(3666416437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_12 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-966691817/10000000000 : ℝ)*x 0 + (5625604151/10000000000 : ℝ)*x 1 + (254967571/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966691817/10000000000 : ℝ)^5887 ≤ (5910449948407/100000000000000 : ℝ)^4863 := by
    have hnat : (966691817 : ℕ)^5887*100000000000000^4863 ≤ 5910449948407^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966691817 10000000000 5910449948407 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5625604151/10000000000 : ℝ)^5887 ≤ (12459551178741/25000000000000 : ℝ)^4863 := by
    have hnat : (5625604151 : ℕ)^5887*25000000000000^4863 ≤ 12459551178741^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625604151 10000000000 12459551178741 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254967571/500000000 : ℝ)^5887 ≤ (44251345315183/100000000000000 : ℝ)^4863 := by
    have hnat : (254967571 : ℕ)^5887*100000000000000^4863 ≤ 44251345315183^4863*500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254967571 500000000 44251345315183 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-966691817/10000000000 : ℝ), (5625604151/10000000000 : ℝ), (254967571/500000000 : ℝ)] ![(5910449948407/100000000000000 : ℝ), (12459551178741/25000000000000 : ℝ), (44251345315183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-966691817/10000000000 : ℝ)|^5887 ≤ (5910449948407/100000000000000 : ℝ)^4863
        have hw : |(-966691817/10000000000 : ℝ)|=(966691817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5625604151/10000000000 : ℝ)|^5887 ≤ (12459551178741/25000000000000 : ℝ)^4863
        have hw : |(5625604151/10000000000 : ℝ)|=(5625604151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(254967571/500000000 : ℝ)|^5887 ≤ (44251345315183/100000000000000 : ℝ)^4863
        have hw : |(254967571/500000000 : ℝ)|=(254967571/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_13 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406296569/10000000000 : ℝ)*x 0 + (-19900583/156250000 : ℝ)*x 1 + (1019870291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406296569/10000000000 : ℝ)^5887 ≤ (23747981380543/50000000000000 : ℝ)^4863 := by
    have hnat : (5406296569 : ℕ)^5887*50000000000000^4863 ≤ 23747981380543^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406296569 10000000000 23747981380543 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19900583/156250000 : ℝ)^5887 ≤ (330107662137/4000000000000 : ℝ)^4863 := by
    have hnat : (19900583 : ℕ)^5887*4000000000000^4863 ≤ 330107662137^4863*156250000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19900583 156250000 330107662137 4000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019870291/2000000000 : ℝ)^5887 ≤ (22125672841431/50000000000000 : ℝ)^4863 := by
    have hnat : (1019870291 : ℕ)^5887*50000000000000^4863 ≤ 22125672841431^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019870291 2000000000 22125672841431 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406296569/10000000000 : ℝ), (-19900583/156250000 : ℝ), (1019870291/2000000000 : ℝ)] ![(23747981380543/50000000000000 : ℝ), (330107662137/4000000000000 : ℝ), (22125672841431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406296569/10000000000 : ℝ)|^5887 ≤ (23747981380543/50000000000000 : ℝ)^4863
        have hw : |(5406296569/10000000000 : ℝ)|=(5406296569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19900583/156250000 : ℝ)|^5887 ≤ (330107662137/4000000000000 : ℝ)^4863
        have hw : |(-19900583/156250000 : ℝ)|=(19900583/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019870291/2000000000 : ℝ)|^5887 ≤ (22125672841431/50000000000000 : ℝ)^4863
        have hw : |(1019870291/2000000000 : ℝ)|=(1019870291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_14 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406296561/10000000000 : ℝ)*x 0 + (5099350971/10000000000 : ℝ)*x 1 + (-1273637969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406296561/10000000000 : ℝ)^5887 ≤ (11873990669001/25000000000000 : ℝ)^4863 := by
    have hnat : (5406296561 : ℕ)^5887*25000000000000^4863 ≤ 11873990669001^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406296561 10000000000 11873990669001 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5099350971/10000000000 : ℝ)^5887 ≤ (44251340598381/100000000000000 : ℝ)^4863 := by
    have hnat : (5099350971 : ℕ)^5887*100000000000000^4863 ≤ 44251340598381^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099350971 10000000000 44251340598381 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1273637969/10000000000 : ℝ)^5887 ≤ (4126348353479/50000000000000 : ℝ)^4863 := by
    have hnat : (1273637969 : ℕ)^5887*50000000000000^4863 ≤ 4126348353479^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273637969 10000000000 4126348353479 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406296561/10000000000 : ℝ), (5099350971/10000000000 : ℝ), (-1273637969/10000000000 : ℝ)] ![(11873990669001/25000000000000 : ℝ), (44251340598381/100000000000000 : ℝ), (4126348353479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406296561/10000000000 : ℝ)|^5887 ≤ (11873990669001/25000000000000 : ℝ)^4863
        have hw : |(5406296561/10000000000 : ℝ)|=(5406296561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5099350971/10000000000 : ℝ)|^5887 ≤ (44251340598381/100000000000000 : ℝ)^4863
        have hw : |(5099350971/10000000000 : ℝ)|=(5099350971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1273637969/10000000000 : ℝ)|^5887 ≤ (4126348353479/50000000000000 : ℝ)^4863
        have hw : |(-1273637969/10000000000 : ℝ)|=(1273637969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_box_15 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (665117831/2000000000 : ℝ)*x 0 + (876028421/2000000000 : ℝ)*x 1 + (547518111/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (665117831/2000000000 : ℝ)^5887 ≤ (6593692075591/25000000000000 : ℝ)^4863 := by
    have hnat : (665117831 : ℕ)^5887*25000000000000^4863 ≤ 6593692075591^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665117831 2000000000 6593692075591 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876028421/2000000000 : ℝ)^5887 ≤ (36812601684841/100000000000000 : ℝ)^4863 := by
    have hnat : (876028421 : ℕ)^5887*100000000000000^4863 ≤ 36812601684841^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876028421 2000000000 36812601684841 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547518111/1250000000 : ℝ)^5887 ≤ (36812629999499/100000000000000 : ℝ)^4863 := by
    have hnat : (547518111 : ℕ)^5887*100000000000000^4863 ≤ 36812629999499^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547518111 1250000000 36812629999499 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(665117831/2000000000 : ℝ), (876028421/2000000000 : ℝ), (547518111/1250000000 : ℝ)] ![(6593692075591/25000000000000 : ℝ), (36812601684841/100000000000000 : ℝ), (36812629999499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(665117831/2000000000 : ℝ)|^5887 ≤ (6593692075591/25000000000000 : ℝ)^4863
        have hw : |(665117831/2000000000 : ℝ)|=(665117831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876028421/2000000000 : ℝ)|^5887 ≤ (36812601684841/100000000000000 : ℝ)^4863
        have hw : |(876028421/2000000000 : ℝ)|=(876028421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547518111/1250000000 : ℝ)|^5887 ≤ (36812629999499/100000000000000 : ℝ)^4863
        have hw : |(547518111/1250000000 : ℝ)|=(547518111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1757_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (223/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(8631/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7307/12500 : ℝ) ∧ (81963/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (93027/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (223/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2281/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (223/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2281/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (223/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2281/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (223/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2281/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (223/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2281/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (223/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2281/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2281/25000 : ℝ) ^ (5871/1024 : ℝ) ≤ (13653308477099/12500000000000000000 : ℝ) := by
    have hpowers : (2281/25000 : ℝ)^5871 ≤ (13653308477099/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2281 : ℕ)^5871*12500000000000000000^1024 ≤ 13653308477099^1024*25000^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2281 25000 13653308477099 12500000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2281/25000 : ℝ)) (X := (13653308477099/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (223/1250 : ℝ) ^ (5871/1024 : ℝ) ≤ (2552221760875927/50000000000000000000 : ℝ) := by
    have hpowers : (223/1250 : ℝ)^5871 ≤ (2552221760875927/50000000000000000000 : ℝ)^1024 := by
      have hnat : (223 : ℕ)^5871*50000000000000000000^1024 ≤ 2552221760875927^1024*1250^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 1250 2552221760875927 50000000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/1250 : ℝ)) (X := (2552221760875927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250013653308477099/6250000000000000000 : ℝ) ≤ (250000095254473/250000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (6250013653308477099/6250000000000000000 : ℝ)^1024 ≤ (250000095254473/250000000000000 : ℝ)^5871 := by
      have hnat : (6250013653308477099 : ℕ)^1024*250000000000000^5871 ≤ 250000095254473^5871*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250013653308477099 6250000000000000000 250000095254473 250000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000095254473/250000000000000 : ℝ)) (X := (6250013653308477099/6250000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50002606834994784323/50000000000000000000 : ℝ) ≤ (5000045466557431/5000000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (50002606834994784323/50000000000000000000 : ℝ)^1024 ≤ (5000045466557431/5000000000000000 : ℝ)^5871 := by
      have hnat : (50002606834994784323 : ℕ)^1024*5000000000000000^5871 ≤ 5000045466557431^5871*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002606834994784323 50000000000000000000 5000045466557431 5000000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000045466557431/5000000000000000 : ℝ)) (X := (50002606834994784323/50000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002552221760875927/25000000000000000000 : ℝ) ≤ (2500044514012701/2500000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (25002552221760875927/25000000000000000000 : ℝ)^1024 ≤ (2500044514012701/2500000000000000 : ℝ)^5871 := by
      have hnat : (25002552221760875927 : ℕ)^1024*2500000000000000^5871 ≤ 2500044514012701^5871*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002552221760875927 25000000000000000000 2500044514012701 2500000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500044514012701/2500000000000000 : ℝ)) (X := (25002552221760875927/25000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13653308477099/12500000000000000000 : ℝ) ≤ ((5447402711886524819/5447500000000000000 : ℝ)+2*(43561467971/435800000000000 : ℝ)*(2281/25000 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (5447402711886524819/5447500000000000000 : ℝ)+2*(43561467971/435800000000000 : ℝ)*(2281/25000 : ℝ)=(250000095254473/250000000000000 : ℝ) by norm_num, show 1+2*(13653308477099/12500000000000000000 : ℝ)=(6250013653308477099/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2552221760875927/50000000000000000000 : ℝ)+(13653308477099/12500000000000000000 : ℝ) ≤ ((5447402711886524819/5447500000000000000 : ℝ)+(43561467971/435800000000000 : ℝ)*((223/1250 : ℝ)+(2281/25000 : ℝ)))^(5871/1024 : ℝ) := by
    rw [show (5447402711886524819/5447500000000000000 : ℝ)+(43561467971/435800000000000 : ℝ)*((223/1250 : ℝ)+(2281/25000 : ℝ))=(5000045466557431/5000000000000000 : ℝ) by norm_num, show 1+(2552221760875927/50000000000000000000 : ℝ)+(13653308477099/12500000000000000000 : ℝ)=(50002606834994784323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2552221760875927/50000000000000000000 : ℝ) ≤ ((5447402711886524819/5447500000000000000 : ℝ)+2*(43561467971/435800000000000 : ℝ)*(223/1250 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (5447402711886524819/5447500000000000000 : ℝ)+2*(43561467971/435800000000000 : ℝ)*(223/1250 : ℝ)=(2500044514012701/2500000000000000 : ℝ) by norm_num, show 1+2*(2552221760875927/50000000000000000000 : ℝ)=(25002552221760875927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5447402711886524819/5447500000000000000 : ℝ)*(X 1 0+X 2 0)+(43561467971/435800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (2281/25000 : ℝ)) (hi := (223/1250 : ℝ)) (c := (5447402711886524819/5447500000000000000 : ℝ)) (alpha := (43561467971/435800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5447402711886524819/5447500000000000000 : ℝ)*(X 0 1+X 2 1)+(43561467971/435800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (2281/25000 : ℝ)) (hi := (223/1250 : ℝ)) (c := (5447402711886524819/5447500000000000000 : ℝ)) (alpha := (43561467971/435800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5447402711886524819/5447500000000000000 : ℝ)*(X 0 2+X 1 2)+(43561467971/435800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (2281/25000 : ℝ)) (hi := (223/1250 : ℝ)) (c := (5447402711886524819/5447500000000000000 : ℝ)) (alpha := (43561467971/435800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16175521/200000000 : ℝ)*X 0 0+(1354457911/2500000000 : ℝ)*X 0 1+(2708915697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2596824859/5000000000 : ℝ)*X 1 0+(-112969439/1000000000 : ℝ)*X 1 1+(5417831371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((324603091/625000000 : ℝ)*X 2 0+(5417831537/10000000000 : ℝ)*X 2 1+(-1129694519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((566477913/1250000000 : ℝ)*X 0 0+(378214573/1000000000 : ℝ)*X 0 1+(472768157/1250000000 : ℝ)*X 0 2+(566477913/1250000000 : ℝ)*X 1 0+(378214573/1000000000 : ℝ)*X 1 1+(472768157/1250000000 : ℝ)*X 1 2+(566477913/1250000000 : ℝ)*X 2 0+(378214573/1000000000 : ℝ)*X 2 1+(472768157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1598942177/10000000000 : ℝ)*X 0 0+(1025848881/2000000000 : ℝ)*X 0 1+(5129244367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5386270189/10000000000 : ℝ)*X 1 0+(-1260706711/10000000000 : ℝ)*X 1 1+(5129244263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((538626989/1000000000 : ℝ)*X 2 0+(2564622283/5000000000 : ℝ)*X 2 1+(-126070671/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3443516519/10000000000 : ℝ)*X 0 0+(540527643/1250000000 : ℝ)*X 0 1+(67565953/156250000 : ℝ)*X 0 2+(3443516519/10000000000 : ℝ)*X 1 0+(540527643/1250000000 : ℝ)*X 1 1+(67565953/156250000 : ℝ)*X 1 2+(3443516519/10000000000 : ℝ)*X 2 0+(540527643/1250000000 : ℝ)*X 2 1+(67565953/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1426925121/10000000000 : ℝ)*X 0 0+(153400177/312500000 : ℝ)*X 0 1+(1095842619/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576376047/5000000000 : ℝ)*X 1 0+(-4298693/39062500 : ℝ)*X 1 1+(5479213261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152752287/10000000000 : ℝ)*X 2 0+(8561271/15625000 : ℝ)*X 2 1+(-137558111/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1188196951/2500000000 : ℝ)*X 0 0+(458302331/1250000000 : ℝ)*X 0 1+(3666416437/10000000000 : ℝ)*X 0 2+(1188196951/2500000000 : ℝ)*X 1 0+(458302331/1250000000 : ℝ)*X 1 1+(3666416437/10000000000 : ℝ)*X 1 2+(1188196951/2500000000 : ℝ)*X 2 0+(458302331/1250000000 : ℝ)*X 2 1+(3666416437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-966691817/10000000000 : ℝ)*X 0 0+(5625604151/10000000000 : ℝ)*X 0 1+(254967571/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5406296569/10000000000 : ℝ)*X 1 0+(-19900583/156250000 : ℝ)*X 1 1+(1019870291/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5406296561/10000000000 : ℝ)*X 2 0+(5099350971/10000000000 : ℝ)*X 2 1+(-1273637969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((665117831/2000000000 : ℝ)*X 0 0+(876028421/2000000000 : ℝ)*X 0 1+(547518111/1250000000 : ℝ)*X 0 2+(665117831/2000000000 : ℝ)*X 1 0+(876028421/2000000000 : ℝ)*X 1 1+(547518111/1250000000 : ℝ)*X 1 2+(665117831/2000000000 : ℝ)*X 2 0+(876028421/2000000000 : ℝ)*X 2 1+(547518111/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-8631/12500 : ℝ) ≤ (-94031334867438556421086326481239/136187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17011991/100000000000000 : ℝ)*(lower0) + (1931867/50000000000000 : ℝ)*(upper3) + (4954851/20000000000000 : ℝ)*(lower4) + (1691481/50000000000000 : ℝ)*(lower5) + (536798365322909/50000000000000 : ℝ)*(major0) + (536798365322909/50000000000000 : ℝ)*(major1) + (536798365322909/50000000000000 : ℝ)*(major2) + (405054131/50000000000000 : ℝ)*(sp1) + (167993491937707/10000000000000 : ℝ)*(sp4) + (67197366706529/4000000000000 : ℝ)*(sp5) + (839965029301373/50000000000000 : ℝ)*(sp6) + (245136824427037/50000000000000 : ℝ)*(sp7) + (29197209/50000000000000 : ℝ)*(sp8) + (4919168741/100000000000000 : ℝ)*(sp14) + (245136824427037/50000000000000 : ℝ)*(f.failure) + (1679934977771487/100000000000000 : ℝ)*(f.sum) + (4140504564371/10895000000000000000000000000 : ℝ)*base66 + (23835167513015971/272375000000000000000000000000000 : ℝ)*base67 + (1483554825919265971/272375000000000000000000000000000 : ℝ)*base69 + (1655306809321640971/272375000000000000000000000000000 : ℝ)*base71 + (7510652931061/2723750000000000000000000000 : ℝ)*base73 + (2167148805558890971/272375000000000000000000000000000 : ℝ)*base75 + (1490997135321640971/272375000000000000000000000000000 : ℝ)*base77 + (2693873132106140971/272375000000000000000000000000000 : ℝ)*base79 + (6133811927067/5447500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (13812997/5000000000000000000000 : ℝ)*base89 + (13812997/5000000000000000000000 : ℝ)*base91 + (13812997/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7307/12500 : ℝ) ≤ (9951644373284010879104227117599/17023437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (667891/10000000000000 : ℝ)*(lower0) + (22036071/100000000000000 : ℝ)*(upper2) + (7118831/50000000000000 : ℝ)*(upper3) + (46880119/100000000000000 : ℝ)*(lower5) + (75081322740207/6250000000000 : ℝ)*(major0) + (75081322740207/6250000000000 : ℝ)*(major1) + (75081322740207/6250000000000 : ℝ)*(major2) + (229315552326671/12500000000000 : ℝ)*(sp0) + (917260705844651/50000000000000 : ℝ)*(sp1) + (1834523705767711/100000000000000 : ℝ)*(sp2) + (27429583361477/5000000000000 : ℝ)*(sp3) + (89105707/12500000000000 : ℝ)*(sp6) + (78775327/100000000000000 : ℝ)*(sp7) + (601384813/20000000000000 : ℝ)*(sp9) + (548591746004867/100000000000000 : ℝ)*(f.failure) + (229315552326671/12500000000000 : ℝ)*(f.sum) + (15140735423359/10895000000000000000000000000 : ℝ)*base66 + (10830820829089967/34046875000000000000000000000000 : ℝ)*base68 + (125010636550089967/34046875000000000000000000000000 : ℝ)*base70 + (2513061489174301/4255859375000000000000000000000 : ℝ)*base71 + (7372440273571/2723750000000000000000000000 : ℝ)*base74 + (10027099812926727/8511718750000000000000000000000 : ℝ)*base75 + (19976316587755921/17023437500000000000000000000000 : ℝ)*base78 + (29391859316135773/8511718750000000000000000000000 : ℝ)*base80 + (1565566254751/10895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2812773/10000000000000000000000 : ℝ)*base90 + (2812773/10000000000000000000000 : ℝ)*base92 + (2812773/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81963/100000 : ℝ) ≤ (22325461082448974467193152114593/27237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56912741/100000000000000 : ℝ)*(upper1) + (52900377/50000000000000 : ℝ)*(upper4) + (9920481/50000000000000 : ℝ)*(lower5) + (115364335493883/10000000000000 : ℝ)*(major0) + (115364335493883/10000000000000 : ℝ)*(major1) + (115364335493883/10000000000000 : ℝ)*(major2) + (24272803429/100000000000000 : ℝ)*(sp1) + (41869699101/100000000000000 : ℝ)*(sp2) + (8862249093/100000000000000 : ℝ)*(sp3) + (179948209/10000000000000 : ℝ)*(sp4) + (1753134834314001/100000000000000 : ℝ)*(sp8) + (1753112360992663/100000000000000 : ℝ)*(sp9) + (175309476409699/10000000000000 : ℝ)*(sp10) + (263409624152001/50000000000000 : ℝ)*(sp11) + (105365622110619/20000000000000 : ℝ)*(f.failure) + (438284158449023/25000000000000 : ℝ)*(f.sum) + (1016813579999/1089500000000000000000000000 : ℝ)*base66 + (28967125422905323/54475000000000000000000000000000 : ℝ)*base68 + (108718716466730323/54475000000000000000000000000000 : ℝ)*base70 + (244566315182805323/54475000000000000000000000000000 : ℝ)*base72 + (620512152439/435800000000000000000000000 : ℝ)*base74 + (365565349536305323/54475000000000000000000000000000 : ℝ)*base76 + (92988856425755323/54475000000000000000000000000000 : ℝ)*base78 + (443237683330323/54475000000000000000000000000000 : ℝ)*base80 + (1691218822801/544750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (28961139/2000000000000000000000 : ℝ)*base89 + (28961139/2000000000000000000000 : ℝ)*base91 + (28961139/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-93027/100000 : ℝ) ≤ (-63344214526379173648622014878051/68093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11940919/50000000000000 : ℝ)*(upper3) + (160320741/100000000000000 : ℝ)*(lower4) + (77748157/50000000000000 : ℝ)*(upper5) + (302789164853831/25000000000000 : ℝ)*(major0) + (302789164853831/25000000000000 : ℝ)*(major1) + (302789164853831/25000000000000 : ℝ)*(major2) + (1327687977/100000000000000 : ℝ)*(sp4) + (1772992251/25000000000000 : ℝ)*(sp5) + (43193200843/50000000000000 : ℝ)*(sp6) + (3602828703/25000000000000 : ℝ)*(sp7) + (1900227924034229/100000000000000 : ℝ)*(sp12) + (950111079876601/50000000000000 : ℝ)*(sp13) + (47503571633013/2500000000000 : ℝ)*(sp14) + (55307799088379/10000000000000 : ℝ)*(sp15) + (553092402198603/100000000000000 : ℝ)*(f.failure) + (950114625861103/50000000000000 : ℝ)*(f.sum) + (829152801159/5447500000000000000000000000 : ℝ)*base66 + (388329401311369089/136187500000000000000000000000000 : ℝ)*base67 + (1339835561926431589/136187500000000000000000000000000 : ℝ)*base69 + (67472137500744089/136187500000000000000000000000000 : ℝ)*base71 + (5614043973787/2723750000000000000000000000 : ℝ)*base74 + (623516246681619089/136187500000000000000000000000000 : ℝ)*base75 + (507469359168619089/136187500000000000000000000000000 : ℝ)*base77 + (230970201822119089/136187500000000000000000000000000 : ℝ)*base79 + (29558117694311/5447500000000000000000000000 : ℝ)*base81 + (64423843/10000000000000000000000 : ℝ)*base89 + (64423843/10000000000000000000000 : ℝ)*base91 + (64423843/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1757_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (223/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8631/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7307/12500 : ℝ) else (81963/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93027/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1757_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1757_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (223/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8631/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7307/12500 : ℝ) else (81963/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93027/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1757_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1757_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (223/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8631/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7307/12500 : ℝ) else (81963/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93027/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1757_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

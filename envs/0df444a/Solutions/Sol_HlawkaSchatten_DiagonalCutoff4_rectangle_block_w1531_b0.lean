-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1531_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:26.776834+00:00
-- url     : https://prove2.me/submissions/604e12f2-5f76-432f-a504-20c40f592589

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
theorem support_rectangle_w1531_s0_0 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-416466679/2500000000 : ℝ)*x 0 + (1474587221/2500000000 : ℝ)*x 1 + (4863360669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416466679/2500000000 : ℝ)^4559 ≤ (4956089526649/50000000000000 : ℝ)^3535 := by
    have hnat : (416466679 : ℕ)^4559*50000000000000^3535 ≤ 4956089526649^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416466679 2500000000 4956089526649 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1474587221/2500000000 : ℝ)^4559 ≤ (12654846571131/25000000000000 : ℝ)^3535 := by
    have hnat : (1474587221 : ℕ)^4559*25000000000000^3535 ≤ 12654846571131^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474587221 2500000000 12654846571131 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4863360669/10000000000 : ℝ)^4559 ≤ (9867108660961/25000000000000 : ℝ)^3535 := by
    have hnat : (4863360669 : ℕ)^4559*25000000000000^3535 ≤ 9867108660961^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4863360669 10000000000 9867108660961 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416466679/2500000000 : ℝ), (1474587221/2500000000 : ℝ), (4863360669/10000000000 : ℝ)] ![(4956089526649/50000000000000 : ℝ), (12654846571131/25000000000000 : ℝ), (9867108660961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416466679/2500000000 : ℝ)|^4559 ≤ (4956089526649/50000000000000 : ℝ)^3535
        have hw : |(-416466679/2500000000 : ℝ)|=(416466679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1474587221/2500000000 : ℝ)|^4559 ≤ (12654846571131/25000000000000 : ℝ)^3535
        have hw : |(1474587221/2500000000 : ℝ)|=(1474587221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4863360669/10000000000 : ℝ)|^4559 ≤ (9867108660961/25000000000000 : ℝ)^3535
        have hw : |(4863360669/10000000000 : ℝ)|=(4863360669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s0_1 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (684232199/1250000000 : ℝ)*x 0 + (-2244594111/10000000000 : ℝ)*x 1 + (2431680353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (684232199/1250000000 : ℝ)^4559 ≤ (22985489147519/50000000000000 : ℝ)^3535 := by
    have hnat : (684232199 : ℕ)^4559*50000000000000^3535 ≤ 22985489147519^3535*1250000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684232199 1250000000 22985489147519 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244594111/10000000000 : ℝ)^4559 ≤ (1456058665807/10000000000000 : ℝ)^3535 := by
    have hnat : (2244594111 : ℕ)^4559*10000000000000^3535 ≤ 1456058665807^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244594111 10000000000 1456058665807 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2431680353/5000000000 : ℝ)^4559 ≤ (39468435031097/100000000000000 : ℝ)^3535 := by
    have hnat : (2431680353 : ℕ)^4559*100000000000000^3535 ≤ 39468435031097^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431680353 5000000000 39468435031097 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(684232199/1250000000 : ℝ), (-2244594111/10000000000 : ℝ), (2431680353/5000000000 : ℝ)] ![(22985489147519/50000000000000 : ℝ), (1456058665807/10000000000000 : ℝ), (39468435031097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(684232199/1250000000 : ℝ)|^4559 ≤ (22985489147519/50000000000000 : ℝ)^3535
        have hw : |(684232199/1250000000 : ℝ)|=(684232199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2244594111/10000000000 : ℝ)|^4559 ≤ (1456058665807/10000000000000 : ℝ)^3535
        have hw : |(-2244594111/10000000000 : ℝ)|=(2244594111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2431680353/5000000000 : ℝ)|^4559 ≤ (39468435031097/100000000000000 : ℝ)^3535
        have hw : |(2431680353/5000000000 : ℝ)|=(2431680353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s0_2 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5473857561/10000000000 : ℝ)*x 0 + (1215840173/2500000000 : ℝ)*x 1 + (-2244594169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5473857561/10000000000 : ℝ)^4559 ≤ (1838839118371/4000000000000 : ℝ)^3535 := by
    have hnat : (5473857561 : ℕ)^4559*4000000000000^3535 ≤ 1838839118371^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473857561 10000000000 1838839118371 4000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1215840173/2500000000 : ℝ)^4559 ≤ (39468434884569/100000000000000 : ℝ)^3535 := by
    have hnat : (1215840173 : ℕ)^4559*100000000000000^3535 ≤ 39468434884569^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215840173 2500000000 39468434884569 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244594169/10000000000 : ℝ)^4559 ≤ (7280293571651/50000000000000 : ℝ)^3535 := by
    have hnat : (2244594169 : ℕ)^4559*50000000000000^3535 ≤ 7280293571651^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244594169 10000000000 7280293571651 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5473857561/10000000000 : ℝ), (1215840173/2500000000 : ℝ), (-2244594169/10000000000 : ℝ)] ![(1838839118371/4000000000000 : ℝ), (39468434884569/100000000000000 : ℝ), (7280293571651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5473857561/10000000000 : ℝ)|^4559 ≤ (1838839118371/4000000000000 : ℝ)^3535
        have hw : |(5473857561/10000000000 : ℝ)|=(5473857561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1215840173/2500000000 : ℝ)|^4559 ≤ (39468434884569/100000000000000 : ℝ)^3535
        have hw : |(1215840173/2500000000 : ℝ)|=(1215840173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2244594169/10000000000 : ℝ)|^4559 ≤ (7280293571651/50000000000000 : ℝ)^3535
        have hw : |(-2244594169/10000000000 : ℝ)|=(2244594169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s0_3 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4140059049/10000000000 : ℝ)*x 0 + (3091582089/10000000000 : ℝ)*x 1 + (5469961491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4140059049/10000000000 : ℝ)^4559 ≤ (4008418321199/12500000000000 : ℝ)^3535 := by
    have hnat : (4140059049 : ℕ)^4559*12500000000000^3535 ≤ 4008418321199^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140059049 10000000000 4008418321199 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091582089/10000000000 : ℝ)^4559 ≤ (2750483702781/12500000000000 : ℝ)^3535 := by
    have hnat : (3091582089 : ℕ)^4559*12500000000000^3535 ≤ 2750483702781^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091582089 10000000000 2750483702781 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469961491/10000000000 : ℝ)^4559 ≤ (11482195948617/25000000000000 : ℝ)^3535 := by
    have hnat : (5469961491 : ℕ)^4559*25000000000000^3535 ≤ 11482195948617^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469961491 10000000000 11482195948617 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4140059049/10000000000 : ℝ), (3091582089/10000000000 : ℝ), (5469961491/10000000000 : ℝ)] ![(4008418321199/12500000000000 : ℝ), (2750483702781/12500000000000 : ℝ), (11482195948617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4140059049/10000000000 : ℝ)|^4559 ≤ (4008418321199/12500000000000 : ℝ)^3535
        have hw : |(4140059049/10000000000 : ℝ)|=(4140059049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091582089/10000000000 : ℝ)|^4559 ≤ (2750483702781/12500000000000 : ℝ)^3535
        have hw : |(3091582089/10000000000 : ℝ)|=(3091582089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469961491/10000000000 : ℝ)|^4559 ≤ (11482195948617/25000000000000 : ℝ)^3535
        have hw : |(5469961491/10000000000 : ℝ)|=(5469961491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s0_4 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1669228207/10000000000 : ℝ)*x 0 + (4889662263/10000000000 : ℝ)*x 1 + (2935553981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1669228207/10000000000 : ℝ)^4559 ≤ (1987596382861/20000000000000 : ℝ)^3535 := by
    have hnat : (1669228207 : ℕ)^4559*20000000000000^3535 ≤ 1987596382861^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669228207 10000000000 1987596382861 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4889662263/10000000000 : ℝ)^4559 ≤ (19871965316813/50000000000000 : ℝ)^3535 := by
    have hnat : (4889662263 : ℕ)^4559*50000000000000^3535 ≤ 19871965316813^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4889662263 10000000000 19871965316813 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2935553981/5000000000 : ℝ)^4559 ≤ (50318087435631/100000000000000 : ℝ)^3535 := by
    have hnat : (2935553981 : ℕ)^4559*100000000000000^3535 ≤ 50318087435631^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935553981 5000000000 50318087435631 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1669228207/10000000000 : ℝ), (4889662263/10000000000 : ℝ), (2935553981/5000000000 : ℝ)] ![(1987596382861/20000000000000 : ℝ), (19871965316813/50000000000000 : ℝ), (50318087435631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1669228207/10000000000 : ℝ)|^4559 ≤ (1987596382861/20000000000000 : ℝ)^3535
        have hw : |(-1669228207/10000000000 : ℝ)|=(1669228207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4889662263/10000000000 : ℝ)|^4559 ≤ (19871965316813/50000000000000 : ℝ)^3535
        have hw : |(4889662263/10000000000 : ℝ)|=(4889662263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2935553981/5000000000 : ℝ)|^4559 ≤ (50318087435631/100000000000000 : ℝ)^3535
        have hw : |(2935553981/5000000000 : ℝ)|=(2935553981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s0_5 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191012251/10000000000 : ℝ)*x 0 + (-618423523/5000000000 : ℝ)*x 1 + (1467777007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191012251/10000000000 : ℝ)^4559 ≤ (42930681543109/100000000000000 : ℝ)^3535 := by
    have hnat : (5191012251 : ℕ)^4559*100000000000000^3535 ≤ 42930681543109^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191012251 10000000000 42930681543109 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618423523/5000000000 : ℝ)^4559 ≤ (843903783993/12500000000000 : ℝ)^3535 := by
    have hnat : (618423523 : ℕ)^4559*12500000000000^3535 ≤ 843903783993^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618423523 5000000000 843903783993 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1467777007/2500000000 : ℝ)^4559 ≤ (3144880510321/6250000000000 : ℝ)^3535 := by
    have hnat : (1467777007 : ℕ)^4559*6250000000000^3535 ≤ 3144880510321^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467777007 2500000000 3144880510321 6250000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191012251/10000000000 : ℝ), (-618423523/5000000000 : ℝ), (1467777007/2500000000 : ℝ)] ![(42930681543109/100000000000000 : ℝ), (843903783993/12500000000000 : ℝ), (3144880510321/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191012251/10000000000 : ℝ)|^4559 ≤ (42930681543109/100000000000000 : ℝ)^3535
        have hw : |(5191012251/10000000000 : ℝ)|=(5191012251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-618423523/5000000000 : ℝ)|^4559 ≤ (843903783993/12500000000000 : ℝ)^3535
        have hw : |(-618423523/5000000000 : ℝ)|=(618423523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1467777007/2500000000 : ℝ)|^4559 ≤ (3144880510321/6250000000000 : ℝ)^3535
        have hw : |(1467777007/2500000000 : ℝ)|=(1467777007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s0_6 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519101221/1000000000 : ℝ)*x 0 + (91736067/156250000 : ℝ)*x 1 + (-1236846701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519101221/1000000000 : ℝ)^4559 ≤ (2683167569113/6250000000000 : ℝ)^3535 := by
    have hnat : (519101221 : ℕ)^4559*6250000000000^3535 ≤ 2683167569113^3535*1000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519101221 1000000000 2683167569113 6250000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91736067/156250000 : ℝ)^4559 ≤ (50318091038943/100000000000000 : ℝ)^3535 := by
    have hnat : (91736067 : ℕ)^4559*100000000000000^3535 ≤ 50318091038943^3535*156250000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91736067 156250000 50318091038943 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1236846701/10000000000 : ℝ)^4559 ≤ (6751227843287/100000000000000 : ℝ)^3535 := by
    have hnat : (1236846701 : ℕ)^4559*100000000000000^3535 ≤ 6751227843287^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236846701 10000000000 6751227843287 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519101221/1000000000 : ℝ), (91736067/156250000 : ℝ), (-1236846701/10000000000 : ℝ)] ![(2683167569113/6250000000000 : ℝ), (50318091038943/100000000000000 : ℝ), (6751227843287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519101221/1000000000 : ℝ)|^4559 ≤ (2683167569113/6250000000000 : ℝ)^3535
        have hw : |(519101221/1000000000 : ℝ)|=(519101221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91736067/156250000 : ℝ)|^4559 ≤ (50318091038943/100000000000000 : ℝ)^3535
        have hw : |(91736067/156250000 : ℝ)|=(91736067/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1236846701/10000000000 : ℝ)|^4559 ≤ (6751227843287/100000000000000 : ℝ)^3535
        have hw : |(-1236846701/10000000000 : ℝ)|=(1236846701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s0_7 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036945677/2500000000 : ℝ)*x 0 + (676190121/1250000000 : ℝ)*x 1 + (3154180701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036945677/2500000000 : ℝ)^4559 ≤ (32144521640543/100000000000000 : ℝ)^3535 := by
    have hnat : (1036945677 : ℕ)^4559*100000000000000^3535 ≤ 32144521640543^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036945677 2500000000 32144521640543 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676190121/1250000000 : ℝ)^4559 ≤ (45275334882607/100000000000000 : ℝ)^3535 := by
    have hnat : (676190121 : ℕ)^4559*100000000000000^3535 ≤ 45275334882607^3535*1250000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676190121 1250000000 45275334882607 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154180701/10000000000 : ℝ)^4559 ≤ (22580143460863/100000000000000 : ℝ)^3535 := by
    have hnat : (3154180701 : ℕ)^4559*100000000000000^3535 ≤ 22580143460863^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154180701 10000000000 22580143460863 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036945677/2500000000 : ℝ), (676190121/1250000000 : ℝ), (3154180701/10000000000 : ℝ)] ![(32144521640543/100000000000000 : ℝ), (45275334882607/100000000000000 : ℝ), (22580143460863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036945677/2500000000 : ℝ)|^4559 ≤ (32144521640543/100000000000000 : ℝ)^3535
        have hw : |(1036945677/2500000000 : ℝ)|=(1036945677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676190121/1250000000 : ℝ)|^4559 ≤ (45275334882607/100000000000000 : ℝ)^3535
        have hw : |(676190121/1250000000 : ℝ)|=(676190121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154180701/10000000000 : ℝ)|^4559 ≤ (22580143460863/100000000000000 : ℝ)^3535
        have hw : |(3154180701/10000000000 : ℝ)|=(3154180701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1531_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3069/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (631/2500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4557/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4557 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4557*1^1024 ≤ 0^1024*1^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4557/1024 : ℝ) ≤ (423671497110822631/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4557 ≤ (423671497110822631/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4557*25000000000000000000^1024 ≤ 423671497110822631^1024*5^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 423671497110822631 25000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (423671497110822631/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4557 := by
      have hnat : (1 : ℕ)^1024*1^4557 ≤ 1^4557*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25423671497110822631/25000000000000000000 : ℝ) ≤ (5018916735101737/5000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (25423671497110822631/25000000000000000000 : ℝ)^1024 ≤ (5018916735101737/5000000000000000 : ℝ)^4557 := by
      have hnat : (25423671497110822631 : ℕ)^1024*5000000000000000^4557 ≤ 5018916735101737^4557*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25423671497110822631 25000000000000000000 5018916735101737 5000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5018916735101737/5000000000000000 : ℝ)) (X := (25423671497110822631/25000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12923671497110822631/12500000000000000000 : ℝ) ≤ (2518916735101737/2500000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (12923671497110822631/12500000000000000000 : ℝ)^1024 ≤ (2518916735101737/2500000000000000 : ℝ)^4557 := by
      have hnat : (12923671497110822631 : ℕ)^1024*2500000000000000^4557 ≤ 2518916735101737^4557*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12923671497110822631 12500000000000000000 2518916735101737 2500000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2518916735101737/2500000000000000 : ℝ)) (X := (12923671497110822631/12500000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(18916735101737/2000000000000000 : ℝ)*(0 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18916735101737/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(423671497110822631/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(18916735101737/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4557/1024 : ℝ) := by
    rw [show (1 : ℝ)+(18916735101737/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5018916735101737/5000000000000000 : ℝ) by norm_num, show 1+(423671497110822631/25000000000000000000 : ℝ)+(0 : ℝ)=(25423671497110822631/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(423671497110822631/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(18916735101737/2000000000000000 : ℝ)*(2/5 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18916735101737/2000000000000000 : ℝ)*(2/5 : ℝ)=(2518916735101737/2500000000000000 : ℝ) by norm_num, show 1+2*(423671497110822631/25000000000000000000 : ℝ)=(12923671497110822631/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(18916735101737/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18916735101737/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(18916735101737/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18916735101737/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(18916735101737/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18916735101737/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416466679/2500000000 : ℝ)*X 0 0+(1474587221/2500000000 : ℝ)*X 0 1+(4863360669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((684232199/1250000000 : ℝ)*X 1 0+(-2244594111/10000000000 : ℝ)*X 1 1+(2431680353/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5473857561/10000000000 : ℝ)*X 2 0+(1215840173/2500000000 : ℝ)*X 2 1+(-2244594169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4140059049/10000000000 : ℝ)*X 0 0+(3091582089/10000000000 : ℝ)*X 0 1+(5469961491/10000000000 : ℝ)*X 0 2+(4140059049/10000000000 : ℝ)*X 1 0+(3091582089/10000000000 : ℝ)*X 1 1+(5469961491/10000000000 : ℝ)*X 1 2+(4140059049/10000000000 : ℝ)*X 2 0+(3091582089/10000000000 : ℝ)*X 2 1+(5469961491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1669228207/10000000000 : ℝ)*X 0 0+(4889662263/10000000000 : ℝ)*X 0 1+(2935553981/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5191012251/10000000000 : ℝ)*X 1 0+(-618423523/5000000000 : ℝ)*X 1 1+(1467777007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519101221/1000000000 : ℝ)*X 2 0+(91736067/156250000 : ℝ)*X 2 1+(-1236846701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1036945677/2500000000 : ℝ)*X 0 0+(676190121/1250000000 : ℝ)*X 0 1+(3154180701/10000000000 : ℝ)*X 0 2+(1036945677/2500000000 : ℝ)*X 1 0+(676190121/1250000000 : ℝ)*X 1 1+(3154180701/10000000000 : ℝ)*X 1 2+(1036945677/2500000000 : ℝ)*X 2 0+(676190121/1250000000 : ℝ)*X 2 1+(3154180701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104728911597623830455501/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9320229/20000000000000 : ℝ)*(base1) + (878878523/100000000000000 : ℝ)*(base19) + (873406661/100000000000000 : ℝ)*(base23) + (121615459/100000000000000 : ℝ)*(upper3) + (51644773/50000000000000 : ℝ)*(upper5) + (693328931613391/100000000000000 : ℝ)*(major0) + (693328931613391/100000000000000 : ℝ)*(major1) + (693328931613391/100000000000000 : ℝ)*(major2) + (241549409323879/25000000000000 : ℝ)*(sp0) + (966199795365307/100000000000000 : ℝ)*(sp1) + (96619980083717/10000000000000 : ℝ)*(sp2) + (21022781189437/5000000000000 : ℝ)*(sp3) + (154177473/5000000000000 : ℝ)*(sp4) + (137895451/10000000000000 : ℝ)*(sp7) + (84091409868879/20000000000000 : ℝ)*(f.failure) + (96620067424383/10000000000000 : ℝ)*(f.sum) + (72928170160167/100000000000000000000000000000 : ℝ)*base65 + (2134461196239833/200000000000000000000000000000 : ℝ)*base68 + (2392402778239833/200000000000000000000000000000 : ℝ)*base70 + (461142480239833/200000000000000000000000000000 : ℝ)*base72 + (502599709739833/100000000000000000000000000000 : ℝ)*base74 + (214035981839833/200000000000000000000000000000 : ℝ)*base76 + (1460938805439833/200000000000000000000000000000 : ℝ)*base78 + (1541999099439833/200000000000000000000000000000 : ℝ)*base80 + (276272175439833/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (624439/250000000000000000000 : ℝ)*base90 + (624439/250000000000000000000 : ℝ)*base92 + (624439/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (184137578815098511950879/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288022917/100000000000000 : ℝ)*(base19) + (439921267/100000000000000 : ℝ)*(base23) + (20451383/12500000000000 : ℝ)*(base39) + (29917723/100000000000000 : ℝ)*(upper3) + (24764097/20000000000000 : ℝ)*(upper5) + (182787021851219/25000000000000 : ℝ)*(major0) + (182787021851219/25000000000000 : ℝ)*(major1) + (731147923793811/100000000000000 : ℝ)*(major2) + (949926573/100000000000000 : ℝ)*(sp1) + (187474499/20000000000000 : ℝ)*(sp2) + (509452071676133/50000000000000 : ℝ)*(sp4) + (127362863175347/12500000000000 : ℝ)*(sp5) + (1018902929669569/100000000000000 : ℝ)*(sp6) + (55423975808403/12500000000000 : ℝ)*(sp7) + (55423975808403/12500000000000 : ℝ)*(f.failure) + (101890430696333/10000000000000 : ℝ)*(f.sum) + (137339159819319/200000000000000000000000000000 : ℝ)*base65 + (191951937949707/200000000000000000000000000000 : ℝ)*base67 + (238167253332597/50000000000000000000000000000 : ℝ)*base70 + (105657379149707/200000000000000000000000000000 : ℝ)*base71 + (528130040780681/200000000000000000000000000000 : ℝ)*base74 + (102973527967403/50000000000000000000000000000 : ℝ)*base75 + (50012803617403/50000000000000000000000000000 : ℝ)*base77 + (30741680267403/50000000000000000000000000000 : ℝ)*base79 + (3360970032597/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (897323/156250000000000000000 : ℝ)*base90 + (897323/156250000000000000000 : ℝ)*base92 + (665177/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1531_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3069/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (631/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1531_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1531_s1_0 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1814533871/10000000000 : ℝ)*x 0 + (1389547399/2500000000 : ℝ)*x 1 + (159621411/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1814533871/10000000000 : ℝ)^4559 ≤ (11067463277361/100000000000000 : ℝ)^3535 := by
    have hnat : (1814533871 : ℕ)^4559*100000000000000^3535 ≤ 11067463277361^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814533871 10000000000 11067463277361 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389547399/2500000000 : ℝ)^4559 ≤ (23443206477509/50000000000000 : ℝ)^3535 := by
    have hnat : (1389547399 : ℕ)^4559*50000000000000^3535 ≤ 23443206477509^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389547399 2500000000 23443206477509 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159621411/312500000 : ℝ)^4559 ≤ (21023061876781/50000000000000 : ℝ)^3535 := by
    have hnat : (159621411 : ℕ)^4559*50000000000000^3535 ≤ 21023061876781^3535*312500000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159621411 312500000 21023061876781 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1814533871/10000000000 : ℝ), (1389547399/2500000000 : ℝ), (159621411/312500000 : ℝ)] ![(11067463277361/100000000000000 : ℝ), (23443206477509/50000000000000 : ℝ), (21023061876781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1814533871/10000000000 : ℝ)|^4559 ≤ (11067463277361/100000000000000 : ℝ)^3535
        have hw : |(-1814533871/10000000000 : ℝ)|=(1814533871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1389547399/2500000000 : ℝ)|^4559 ≤ (23443206477509/50000000000000 : ℝ)^3535
        have hw : |(1389547399/2500000000 : ℝ)|=(1389547399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159621411/312500000 : ℝ)|^4559 ≤ (21023061876781/50000000000000 : ℝ)^3535
        have hw : |(159621411/312500000 : ℝ)|=(159621411/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s1_1 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383201011/10000000000 : ℝ)*x 0 + (-410220381/2000000000 : ℝ)*x 1 + (2553941681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383201011/10000000000 : ℝ)^4559 ≤ (44991437295347/100000000000000 : ℝ)^3535 := by
    have hnat : (5383201011 : ℕ)^4559*100000000000000^3535 ≤ 44991437295347^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383201011 10000000000 44991437295347 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410220381/2000000000 : ℝ)^4559 ≤ (6481228968179/50000000000000 : ℝ)^3535 := by
    have hnat : (410220381 : ℕ)^4559*50000000000000^3535 ≤ 6481228968179^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410220381 2000000000 6481228968179 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2553941681/5000000000 : ℝ)^4559 ≤ (5255763093843/12500000000000 : ℝ)^3535 := by
    have hnat : (2553941681 : ℕ)^4559*12500000000000^3535 ≤ 5255763093843^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553941681 5000000000 5255763093843 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383201011/10000000000 : ℝ), (-410220381/2000000000 : ℝ), (2553941681/5000000000 : ℝ)] ![(44991437295347/100000000000000 : ℝ), (6481228968179/50000000000000 : ℝ), (5255763093843/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383201011/10000000000 : ℝ)|^4559 ≤ (44991437295347/100000000000000 : ℝ)^3535
        have hw : |(5383201011/10000000000 : ℝ)|=(5383201011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410220381/2000000000 : ℝ)|^4559 ≤ (6481228968179/50000000000000 : ℝ)^3535
        have hw : |(-410220381/2000000000 : ℝ)|=(410220381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2553941681/5000000000 : ℝ)|^4559 ≤ (5255763093843/12500000000000 : ℝ)^3535
        have hw : |(2553941681/5000000000 : ℝ)|=(2553941681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s1_2 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538319957/1000000000 : ℝ)*x 0 + (15962141/31250000 : ℝ)*x 1 + (-1025550761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538319957/1000000000 : ℝ)^4559 ≤ (11247855440783/25000000000000 : ℝ)^3535 := by
    have hnat : (538319957 : ℕ)^4559*25000000000000^3535 ≤ 11247855440783^3535*1000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538319957 1000000000 11247855440783 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15962141/31250000 : ℝ)^4559 ≤ (42046123413847/100000000000000 : ℝ)^3535 := by
    have hnat : (15962141 : ℕ)^4559*100000000000000^3535 ≤ 42046123413847^3535*31250000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15962141 31250000 42046123413847 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025550761/5000000000 : ℝ)^4559 ≤ (2592490962949/20000000000000 : ℝ)^3535 := by
    have hnat : (1025550761 : ℕ)^4559*20000000000000^3535 ≤ 2592490962949^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025550761 5000000000 2592490962949 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538319957/1000000000 : ℝ), (15962141/31250000 : ℝ), (-1025550761/5000000000 : ℝ)] ![(11247855440783/25000000000000 : ℝ), (42046123413847/100000000000000 : ℝ), (2592490962949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538319957/1000000000 : ℝ)|^4559 ≤ (11247855440783/25000000000000 : ℝ)^3535
        have hw : |(538319957/1000000000 : ℝ)|=(538319957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15962141/31250000 : ℝ)|^4559 ≤ (42046123413847/100000000000000 : ℝ)^3535
        have hw : |(15962141/31250000 : ℝ)|=(15962141/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025550761/5000000000 : ℝ)|^4559 ≤ (2592490962949/20000000000000 : ℝ)^3535
        have hw : |(-1025550761/5000000000 : ℝ)|=(1025550761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s1_3 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242681213/10000000000 : ℝ)*x 0 + (1875757703/5000000000 : ℝ)*x 1 + (4786307861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242681213/10000000000 : ℝ)^4559 ≤ (6619226591271/20000000000000 : ℝ)^3535 := by
    have hnat : (4242681213 : ℕ)^4559*20000000000000^3535 ≤ 6619226591271^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242681213 10000000000 6619226591271 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1875757703/5000000000 : ℝ)^4559 ≤ (28240033367123/100000000000000 : ℝ)^3535 := by
    have hnat : (1875757703 : ℕ)^4559*100000000000000^3535 ≤ 28240033367123^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875757703 5000000000 28240033367123 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4786307861/10000000000 : ℝ)^4559 ≤ (38663833659701/100000000000000 : ℝ)^3535 := by
    have hnat : (4786307861 : ℕ)^4559*100000000000000^3535 ≤ 38663833659701^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786307861 10000000000 38663833659701 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242681213/10000000000 : ℝ), (1875757703/5000000000 : ℝ), (4786307861/10000000000 : ℝ)] ![(6619226591271/20000000000000 : ℝ), (28240033367123/100000000000000 : ℝ), (38663833659701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242681213/10000000000 : ℝ)|^4559 ≤ (6619226591271/20000000000000 : ℝ)^3535
        have hw : |(4242681213/10000000000 : ℝ)|=(4242681213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1875757703/5000000000 : ℝ)|^4559 ≤ (28240033367123/100000000000000 : ℝ)^3535
        have hw : |(1875757703/5000000000 : ℝ)|=(1875757703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4786307861/10000000000 : ℝ)|^4559 ≤ (38663833659701/100000000000000 : ℝ)^3535
        have hw : |(4786307861/10000000000 : ℝ)|=(4786307861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s1_4 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1814801931/10000000000 : ℝ)*x 0 + (255639393/500000000 : ℝ)*x 1 + (5553210283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1814801931/10000000000 : ℝ)^4559 ≤ (1106957192731/10000000000000 : ℝ)^3535 := by
    have hnat : (1814801931 : ℕ)^4559*10000000000000^3535 ≤ 1106957192731^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814801931 10000000000 1106957192731 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255639393/500000000 : ℝ)^4559 ≤ (4209817862759/10000000000000 : ℝ)^3535 := by
    have hnat : (255639393 : ℕ)^4559*10000000000000^3535 ≤ 4209817862759^3535*500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255639393 500000000 4209817862759 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5553210283/10000000000 : ℝ)^4559 ≤ (2341612471719/5000000000000 : ℝ)^3535 := by
    have hnat : (5553210283 : ℕ)^4559*5000000000000^3535 ≤ 2341612471719^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553210283 10000000000 2341612471719 5000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1814801931/10000000000 : ℝ), (255639393/500000000 : ℝ), (5553210283/10000000000 : ℝ)] ![(1106957192731/10000000000000 : ℝ), (4209817862759/10000000000000 : ℝ), (2341612471719/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1814801931/10000000000 : ℝ)|^4559 ≤ (1106957192731/10000000000000 : ℝ)^3535
        have hw : |(-1814801931/10000000000 : ℝ)|=(1814801931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(255639393/500000000 : ℝ)|^4559 ≤ (4209817862759/10000000000000 : ℝ)^3535
        have hw : |(255639393/500000000 : ℝ)|=(255639393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5553210283/10000000000 : ℝ)|^4559 ≤ (2341612471719/5000000000000 : ℝ)^3535
        have hw : |(5553210283/10000000000 : ℝ)|=(5553210283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s1_5 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264329027/10000000000 : ℝ)*x 0 + (-321155211/2000000000 : ℝ)*x 1 + (2776605199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264329027/10000000000 : ℝ)^4559 ≤ (8742852482177/20000000000000 : ℝ)^3535 := by
    have hnat : (5264329027 : ℕ)^4559*20000000000000^3535 ≤ 8742852482177^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264329027 10000000000 8742852482177 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321155211/2000000000 : ℝ)^4559 ≤ (9453486887949/100000000000000 : ℝ)^3535 := by
    have hnat : (321155211 : ℕ)^4559*100000000000000^3535 ≤ 9453486887949^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321155211 2000000000 9453486887949 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2776605199/5000000000 : ℝ)^4559 ≤ (23416125342577/50000000000000 : ℝ)^3535 := by
    have hnat : (2776605199 : ℕ)^4559*50000000000000^3535 ≤ 23416125342577^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776605199 5000000000 23416125342577 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264329027/10000000000 : ℝ), (-321155211/2000000000 : ℝ), (2776605199/5000000000 : ℝ)] ![(8742852482177/20000000000000 : ℝ), (9453486887949/100000000000000 : ℝ), (23416125342577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264329027/10000000000 : ℝ)|^4559 ≤ (8742852482177/20000000000000 : ℝ)^3535
        have hw : |(5264329027/10000000000 : ℝ)|=(5264329027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-321155211/2000000000 : ℝ)|^4559 ≤ (9453486887949/100000000000000 : ℝ)^3535
        have hw : |(-321155211/2000000000 : ℝ)|=(321155211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2776605199/5000000000 : ℝ)|^4559 ≤ (23416125342577/50000000000000 : ℝ)^3535
        have hw : |(2776605199/5000000000 : ℝ)|=(2776605199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s1_6 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264328931/10000000000 : ℝ)*x 0 + (5553210491/10000000000 : ℝ)*x 1 + (-1605776057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264328931/10000000000 : ℝ)^4559 ≤ (21857130691397/50000000000000 : ℝ)^3535 := by
    have hnat : (5264328931 : ℕ)^4559*50000000000000^3535 ≤ 21857130691397^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264328931 10000000000 21857130691397 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5553210491/10000000000 : ℝ)^4559 ≤ (936645033933/2000000000000 : ℝ)^3535 := by
    have hnat : (5553210491 : ℕ)^4559*2000000000000^3535 ≤ 936645033933^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553210491 10000000000 936645033933 2000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1605776057/10000000000 : ℝ)^4559 ≤ (1890697380627/20000000000000 : ℝ)^3535 := by
    have hnat : (1605776057 : ℕ)^4559*20000000000000^3535 ≤ 1890697380627^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605776057 10000000000 1890697380627 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264328931/10000000000 : ℝ), (5553210491/10000000000 : ℝ), (-1605776057/10000000000 : ℝ)] ![(21857130691397/50000000000000 : ℝ), (936645033933/2000000000000 : ℝ), (1890697380627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264328931/10000000000 : ℝ)|^4559 ≤ (21857130691397/50000000000000 : ℝ)^3535
        have hw : |(5264328931/10000000000 : ℝ)|=(5264328931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5553210491/10000000000 : ℝ)|^4559 ≤ (936645033933/2000000000000 : ℝ)^3535
        have hw : |(5553210491/10000000000 : ℝ)|=(5553210491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1605776057/10000000000 : ℝ)|^4559 ≤ (1890697380627/20000000000000 : ℝ)^3535
        have hw : |(-1605776057/10000000000 : ℝ)|=(1605776057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s1_7 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243296269/10000000000 : ℝ)*x 0 + (2387520481/5000000000 : ℝ)*x 1 + (3762959509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243296269/10000000000 : ℝ)^4559 ≤ (33102320820977/100000000000000 : ℝ)^3535 := by
    have hnat : (4243296269 : ℕ)^4559*100000000000000^3535 ≤ 33102320820977^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243296269 10000000000 33102320820977 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2387520481/5000000000 : ℝ)^4559 ≤ (38546495119463/100000000000000 : ℝ)^3535 := by
    have hnat : (2387520481 : ℕ)^4559*100000000000000^3535 ≤ 38546495119463^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387520481 5000000000 38546495119463 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3762959509/10000000000 : ℝ)^4559 ≤ (14175592021389/50000000000000 : ℝ)^3535 := by
    have hnat : (3762959509 : ℕ)^4559*50000000000000^3535 ≤ 14175592021389^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3762959509 10000000000 14175592021389 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243296269/10000000000 : ℝ), (2387520481/5000000000 : ℝ), (3762959509/10000000000 : ℝ)] ![(33102320820977/100000000000000 : ℝ), (38546495119463/100000000000000 : ℝ), (14175592021389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243296269/10000000000 : ℝ)|^4559 ≤ (33102320820977/100000000000000 : ℝ)^3535
        have hw : |(4243296269/10000000000 : ℝ)|=(4243296269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2387520481/5000000000 : ℝ)|^4559 ≤ (38546495119463/100000000000000 : ℝ)^3535
        have hw : |(2387520481/5000000000 : ℝ)|=(2387520481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3762959509/10000000000 : ℝ)|^4559 ≤ (14175592021389/50000000000000 : ℝ)^3535
        have hw : |(3762959509/10000000000 : ℝ)|=(3762959509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1531_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (631/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2151/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4533/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (631/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (631/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (631/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (631/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (631/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (631/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3069/100000 : ℝ) ^ (4557/1024 : ℝ) ≤ (9242950973103/50000000000000000000 : ℝ) := by
    have hpowers : (3069/100000 : ℝ)^4557 ≤ (9242950973103/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3069 : ℕ)^4557*50000000000000000000^1024 ≤ 9242950973103^1024*100000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3069 100000 9242950973103 50000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3069/100000 : ℝ)) (X := (9242950973103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (631/2500 : ℝ) ^ (4557/1024 : ℝ) ≤ (109181947078274949/50000000000000000000 : ℝ) := by
    have hpowers : (631/2500 : ℝ)^4557 ≤ (109181947078274949/50000000000000000000 : ℝ)^1024 := by
      have hnat : (631 : ℕ)^4557*50000000000000000000^1024 ≤ 109181947078274949^1024*2500^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        631 2500 109181947078274949 50000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (631/2500 : ℝ)) (X := (109181947078274949/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000009242950973103/25000000000000000000 : ℝ) ≤ (10000000830790471/10000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (25000009242950973103/25000000000000000000 : ℝ)^1024 ≤ (10000000830790471/10000000000000000 : ℝ)^4557 := by
      have hnat : (25000009242950973103 : ℕ)^1024*10000000000000000^4557 ≤ 10000000830790471^4557*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000009242950973103 25000000000000000000 10000000830790471 10000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000830790471/10000000000000000 : ℝ)) (X := (25000009242950973103/25000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12527297797507312013/12500000000000000000 : ℝ) ≤ (2501225776240449/2500000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (12527297797507312013/12500000000000000000 : ℝ)^1024 ≤ (2501225776240449/2500000000000000 : ℝ)^4557 := by
      have hnat : (12527297797507312013 : ℕ)^1024*2500000000000000^4557 ≤ 2501225776240449^4557*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12527297797507312013 12500000000000000000 2501225776240449 2500000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501225776240449/2500000000000000 : ℝ)) (X := (12527297797507312013/12500000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25109181947078274949/25000000000000000000 : ℝ) ≤ (10009805379133121/10000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (25109181947078274949/25000000000000000000 : ℝ)^1024 ≤ (10009805379133121/10000000000000000 : ℝ)^4557 := by
      have hnat : (25109181947078274949 : ℕ)^1024*10000000000000000^4557 ≤ 10009805379133121^4557*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25109181947078274949 25000000000000000000 10009805379133121 10000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009805379133121/10000000000000000 : ℝ)) (X := (25109181947078274949/25000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9242950973103/50000000000000000000 : ℝ) ≤ ((221679928260591939691/221710000000000000000 : ℝ)+2*(196090966853/88684000000000 : ℝ)*(3069/100000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (221679928260591939691/221710000000000000000 : ℝ)+2*(196090966853/88684000000000 : ℝ)*(3069/100000 : ℝ)=(10000000830790471/10000000000000000 : ℝ) by norm_num, show 1+2*(9242950973103/50000000000000000000 : ℝ)=(25000009242950973103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(109181947078274949/50000000000000000000 : ℝ)+(9242950973103/50000000000000000000 : ℝ) ≤ ((221679928260591939691/221710000000000000000 : ℝ)+(196090966853/88684000000000 : ℝ)*((631/2500 : ℝ)+(3069/100000 : ℝ)))^(4557/1024 : ℝ) := by
    rw [show (221679928260591939691/221710000000000000000 : ℝ)+(196090966853/88684000000000 : ℝ)*((631/2500 : ℝ)+(3069/100000 : ℝ))=(2501225776240449/2500000000000000 : ℝ) by norm_num, show 1+(109181947078274949/50000000000000000000 : ℝ)+(9242950973103/50000000000000000000 : ℝ)=(12527297797507312013/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(109181947078274949/50000000000000000000 : ℝ) ≤ ((221679928260591939691/221710000000000000000 : ℝ)+2*(196090966853/88684000000000 : ℝ)*(631/2500 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (221679928260591939691/221710000000000000000 : ℝ)+2*(196090966853/88684000000000 : ℝ)*(631/2500 : ℝ)=(10009805379133121/10000000000000000 : ℝ) by norm_num, show 1+2*(109181947078274949/50000000000000000000 : ℝ)=(25109181947078274949/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (221679928260591939691/221710000000000000000 : ℝ)*(X 1 0+X 2 0)+(196090966853/88684000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (3069/100000 : ℝ)) (hi := (631/2500 : ℝ)) (c := (221679928260591939691/221710000000000000000 : ℝ)) (alpha := (196090966853/88684000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (221679928260591939691/221710000000000000000 : ℝ)*(X 0 1+X 2 1)+(196090966853/88684000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (3069/100000 : ℝ)) (hi := (631/2500 : ℝ)) (c := (221679928260591939691/221710000000000000000 : ℝ)) (alpha := (196090966853/88684000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (221679928260591939691/221710000000000000000 : ℝ)*(X 0 2+X 1 2)+(196090966853/88684000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (3069/100000 : ℝ)) (hi := (631/2500 : ℝ)) (c := (221679928260591939691/221710000000000000000 : ℝ)) (alpha := (196090966853/88684000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1814533871/10000000000 : ℝ)*X 0 0+(1389547399/2500000000 : ℝ)*X 0 1+(159621411/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5383201011/10000000000 : ℝ)*X 1 0+(-410220381/2000000000 : ℝ)*X 1 1+(2553941681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((538319957/1000000000 : ℝ)*X 2 0+(15962141/31250000 : ℝ)*X 2 1+(-1025550761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4242681213/10000000000 : ℝ)*X 0 0+(1875757703/5000000000 : ℝ)*X 0 1+(4786307861/10000000000 : ℝ)*X 0 2+(4242681213/10000000000 : ℝ)*X 1 0+(1875757703/5000000000 : ℝ)*X 1 1+(4786307861/10000000000 : ℝ)*X 1 2+(4242681213/10000000000 : ℝ)*X 2 0+(1875757703/5000000000 : ℝ)*X 2 1+(4786307861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1814801931/10000000000 : ℝ)*X 0 0+(255639393/500000000 : ℝ)*X 0 1+(5553210283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264329027/10000000000 : ℝ)*X 1 0+(-321155211/2000000000 : ℝ)*X 1 1+(2776605199/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5264328931/10000000000 : ℝ)*X 2 0+(5553210491/10000000000 : ℝ)*X 2 1+(-1605776057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4243296269/10000000000 : ℝ)*X 0 0+(2387520481/5000000000 : ℝ)*X 0 1+(3762959509/10000000000 : ℝ)*X 0 2+(4243296269/10000000000 : ℝ)*X 1 0+(2387520481/5000000000 : ℝ)*X 1 1+(3762959509/10000000000 : ℝ)*X 1 2+(4243296269/10000000000 : ℝ)*X 2 0+(2387520481/5000000000 : ℝ)*X 2 1+(3762959509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5939968625647818017589417153/1385687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214274909/100000000000000 : ℝ)*(base1) + (1682511087/100000000000000 : ℝ)*(base19) + (272014053/25000000000000 : ℝ)*(base23) + (47077183/50000000000000 : ℝ)*(upper3) + (178042819/100000000000000 : ℝ)*(upper5) + (199194657693987/12500000000000 : ℝ)*(major0) + (199194657693987/12500000000000 : ℝ)*(major1) + (199194657693987/12500000000000 : ℝ)*(major2) + (555181258922537/25000000000000 : ℝ)*(sp0) + (1110364061899379/50000000000000 : ℝ)*(sp1) + (2220728718253633/100000000000000 : ℝ)*(sp2) + (966381410575971/100000000000000 : ℝ)*(sp3) + (2492447303/50000000000000 : ℝ)*(sp4) + (737263613/25000000000000 : ℝ)*(sp7) + (966384573905331/100000000000000 : ℝ)*(f.failure) + (555182451577461/25000000000000 : ℝ)*(f.sum) + (36089561953233/22171000000000000000000000000 : ℝ)*base65 + (31842247814844911983/2771375000000000000000000000000000 : ℝ)*base68 + (32921844359523036983/2771375000000000000000000000000000 : ℝ)*base70 + (14361969973545036983/2771375000000000000000000000000000 : ℝ)*base72 + (3654967410591/1108550000000000000000000000 : ℝ)*base74 + (31458969637115786983/2771375000000000000000000000000000 : ℝ)*base76 + (17383859182009036983/2771375000000000000000000000000000 : ℝ)*base78 + (32277513298873911983/2771375000000000000000000000000000 : ℝ)*base80 + (68242227806643/22171000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14585829/1250000000000000000000 : ℝ)*base89 + (14585829/1250000000000000000000 : ℝ)*base91 + (14585829/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24202722219968419728772635711/5542750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14786269/2000000000000 : ℝ)*(base19) + (199475991/25000000000000 : ℝ)*(base23) + (30034509/25000000000000 : ℝ)*(upper3) + (2481111/6250000000000 : ℝ)*(lower4) + (7981683/12500000000000 : ℝ)*(upper5) + (1629304628848593/100000000000000 : ℝ)*(major0) + (1629304628848593/100000000000000 : ℝ)*(major1) + (1629304628848593/100000000000000 : ℝ)*(major2) + (1317741583/25000000000000 : ℝ)*(sp1) + (127197863/2000000000000 : ℝ)*(sp2) + (1135273090275689/50000000000000 : ℝ)*(sp4) + (567635042567899/25000000000000 : ℝ)*(sp5) + (283817377844283/12500000000000 : ℝ)*(sp6) + (988062931593973/100000000000000 : ℝ)*(sp7) + (988062931593973/100000000000000 : ℝ)*(f.failure) + (1135273090275689/50000000000000 : ℝ)*(f.sum) + (4777443254497/692843750000000000000000000 : ℝ)*base66 + (74052365252272704763/22171000000000000000000000000000000 : ℝ)*base67 + (234631017994897704763/22171000000000000000000000000000000 : ℝ)*base69 + (32625005873852295237/22171000000000000000000000000000000 : ℝ)*base72 + (67589672062261/22171000000000000000000000000 : ℝ)*base74 + (248891329414419704763/22171000000000000000000000000000000 : ℝ)*base75 + (35240900915807704763/22171000000000000000000000000000000 : ℝ)*base77 + (103095476351248704763/22171000000000000000000000000000000 : ℝ)*base79 + (37026187444353/11085500000000000000000000000 : ℝ)*base81 + (1212307/1250000000000000000000 : ℝ)*base89 + (1212307/1250000000000000000000 : ℝ)*base91 + (1212307/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1531_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (631/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2151/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4533/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1531_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1531_s2_0 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73477999/400000000 : ℝ)*x 0 + (545207731/1000000000 : ℝ)*x 1 + (2599724231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73477999/400000000 : ℝ)^4559 ≤ (5622053342761/50000000000000 : ℝ)^3535 := by
    have hnat : (73477999 : ℕ)^4559*50000000000000^3535 ≤ 5622053342761^3535*400000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73477999 400000000 5622053342761 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545207731/1000000000 : ℝ)^4559 ≤ (45735211125117/100000000000000 : ℝ)^3535 := by
    have hnat : (545207731 : ℕ)^4559*100000000000000^3535 ≤ 45735211125117^3535*1000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545207731 1000000000 45735211125117 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599724231/5000000000 : ℝ)^4559 ≤ (2151034108259/5000000000000 : ℝ)^3535 := by
    have hnat : (2599724231 : ℕ)^4559*5000000000000^3535 ≤ 2151034108259^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599724231 5000000000 2151034108259 5000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73477999/400000000 : ℝ), (545207731/1000000000 : ℝ), (2599724231/5000000000 : ℝ)] ![(5622053342761/50000000000000 : ℝ), (45735211125117/100000000000000 : ℝ), (2151034108259/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73477999/400000000 : ℝ)|^4559 ≤ (5622053342761/50000000000000 : ℝ)^3535
        have hw : |(-73477999/400000000 : ℝ)|=(73477999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545207731/1000000000 : ℝ)|^4559 ≤ (45735211125117/100000000000000 : ℝ)^3535
        have hw : |(545207731/1000000000 : ℝ)|=(545207731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599724231/5000000000 : ℝ)|^4559 ≤ (2151034108259/5000000000000 : ℝ)^3535
        have hw : |(2599724231/5000000000 : ℝ)|=(2599724231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s2_1 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42848661/80000000 : ℝ)*x 0 + (-491714707/2500000000 : ℝ)*x 1 + (2599724421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42848661/80000000 : ℝ)^4559 ≤ (5587418477141/12500000000000 : ℝ)^3535 := by
    have hnat : (42848661 : ℕ)^4559*12500000000000^3535 ≤ 5587418477141^3535*80000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42848661 80000000 5587418477141 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491714707/2500000000 : ℝ)^4559 ≤ (6139982977773/50000000000000 : ℝ)^3535 := by
    have hnat : (491714707 : ℕ)^4559*50000000000000^3535 ≤ 6139982977773^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491714707 2500000000 6139982977773 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599724421/5000000000 : ℝ)^4559 ≤ (21510343110057/50000000000000 : ℝ)^3535 := by
    have hnat : (2599724421 : ℕ)^4559*50000000000000^3535 ≤ 21510343110057^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599724421 5000000000 21510343110057 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42848661/80000000 : ℝ), (-491714707/2500000000 : ℝ), (2599724421/5000000000 : ℝ)] ![(5587418477141/12500000000000 : ℝ), (6139982977773/50000000000000 : ℝ), (21510343110057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42848661/80000000 : ℝ)|^4559 ≤ (5587418477141/12500000000000 : ℝ)^3535
        have hw : |(42848661/80000000 : ℝ)|=(42848661/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491714707/2500000000 : ℝ)|^4559 ≤ (6139982977773/50000000000000 : ℝ)^3535
        have hw : |(-491714707/2500000000 : ℝ)|=(491714707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599724421/5000000000 : ℝ)|^4559 ≤ (21510343110057/50000000000000 : ℝ)^3535
        have hw : |(2599724421/5000000000 : ℝ)|=(2599724421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s2_2 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678041663/5000000000 : ℝ)*x 0 + (324965527/625000000 : ℝ)*x 1 + (-983429217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678041663/5000000000 : ℝ)^4559 ≤ (8939871072401/20000000000000 : ℝ)^3535 := by
    have hnat : (2678041663 : ℕ)^4559*20000000000000^3535 ≤ 8939871072401^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678041663 5000000000 8939871072401 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324965527/625000000 : ℝ)^4559 ≤ (43020681845053/100000000000000 : ℝ)^3535 := by
    have hnat : (324965527 : ℕ)^4559*100000000000000^3535 ≤ 43020681845053^3535*625000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324965527 625000000 43020681845053 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983429217/5000000000 : ℝ)^4559 ≤ (2455992556611/20000000000000 : ℝ)^3535 := by
    have hnat : (983429217 : ℕ)^4559*20000000000000^3535 ≤ 2455992556611^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983429217 5000000000 2455992556611 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678041663/5000000000 : ℝ), (324965527/625000000 : ℝ), (-983429217/5000000000 : ℝ)] ![(8939871072401/20000000000000 : ℝ), (43020681845053/100000000000000 : ℝ), (2455992556611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678041663/5000000000 : ℝ)|^4559 ≤ (8939871072401/20000000000000 : ℝ)^3535
        have hw : |(2678041663/5000000000 : ℝ)|=(2678041663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324965527/625000000 : ℝ)|^4559 ≤ (43020681845053/100000000000000 : ℝ)^3535
        have hw : |(324965527/625000000 : ℝ)|=(324965527/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983429217/5000000000 : ℝ)|^4559 ≤ (2455992556611/20000000000000 : ℝ)^3535
        have hw : |(-983429217/5000000000 : ℝ)|=(983429217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s2_3 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2129412129/5000000000 : ℝ)*x 0 + (1988408437/5000000000 : ℝ)*x 1 + (4557353637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129412129/5000000000 : ℝ)^4559 ≤ (8314657132847/25000000000000 : ℝ)^3535 := by
    have hnat : (2129412129 : ℕ)^4559*25000000000000^3535 ≤ 8314657132847^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129412129 5000000000 8314657132847 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988408437/5000000000 : ℝ)^4559 ≤ (380575832631/1250000000000 : ℝ)^3535 := by
    have hnat : (1988408437 : ℕ)^4559*1250000000000^3535 ≤ 380575832631^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988408437 5000000000 380575832631 1250000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4557353637/10000000000 : ℝ)^4559 ≤ (36295304850789/100000000000000 : ℝ)^3535 := by
    have hnat : (4557353637 : ℕ)^4559*100000000000000^3535 ≤ 36295304850789^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557353637 10000000000 36295304850789 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129412129/5000000000 : ℝ), (1988408437/5000000000 : ℝ), (4557353637/10000000000 : ℝ)] ![(8314657132847/25000000000000 : ℝ), (380575832631/1250000000000 : ℝ), (36295304850789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129412129/5000000000 : ℝ)|^4559 ≤ (8314657132847/25000000000000 : ℝ)^3535
        have hw : |(2129412129/5000000000 : ℝ)|=(2129412129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1988408437/5000000000 : ℝ)|^4559 ≤ (380575832631/1250000000000 : ℝ)^3535
        have hw : |(1988408437/5000000000 : ℝ)|=(1988408437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4557353637/10000000000 : ℝ)|^4559 ≤ (36295304850789/100000000000000 : ℝ)^3535
        have hw : |(4557353637/10000000000 : ℝ)|=(4557353637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s2_4 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-367399191/2000000000 : ℝ)*x 0 + (5201001369/10000000000 : ℝ)*x 1 + (5450511917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367399191/2000000000 : ℝ)^4559 ≤ (2811117415471/25000000000000 : ℝ)^3535 := by
    have hnat : (367399191 : ℕ)^4559*25000000000000^3535 ≤ 2811117415471^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367399191 2000000000 2811117415471 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5201001369/10000000000 : ℝ)^4559 ≤ (8607450752881/20000000000000 : ℝ)^3535 := by
    have hnat : (5201001369 : ℕ)^4559*20000000000000^3535 ≤ 8607450752881^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201001369 10000000000 8607450752881 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450511917/10000000000 : ℝ)^4559 ≤ (5714784569347/12500000000000 : ℝ)^3535 := by
    have hnat : (5450511917 : ℕ)^4559*12500000000000^3535 ≤ 5714784569347^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450511917 10000000000 5714784569347 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-367399191/2000000000 : ℝ), (5201001369/10000000000 : ℝ), (5450511917/10000000000 : ℝ)] ![(2811117415471/25000000000000 : ℝ), (8607450752881/20000000000000 : ℝ), (5714784569347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-367399191/2000000000 : ℝ)|^4559 ≤ (2811117415471/25000000000000 : ℝ)^3535
        have hw : |(-367399191/2000000000 : ℝ)|=(367399191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5201001369/10000000000 : ℝ)|^4559 ≤ (8607450752881/20000000000000 : ℝ)^3535
        have hw : |(5201001369/10000000000 : ℝ)|=(5201001369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450511917/10000000000 : ℝ)|^4559 ≤ (5714784569347/12500000000000 : ℝ)^3535
        have hw : |(5450511917/10000000000 : ℝ)|=(5450511917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s2_5 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165298963/312500000 : ℝ)*x 0 + (-1715796107/10000000000 : ℝ)*x 1 + (5450513527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165298963/312500000 : ℝ)^4559 ≤ (43984728438381/100000000000000 : ℝ)^3535 := by
    have hnat : (165298963 : ℕ)^4559*100000000000000^3535 ≤ 43984728438381^3535*312500000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165298963 312500000 43984728438381 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1715796107/10000000000 : ℝ)^4559 ≤ (10296977577907/100000000000000 : ℝ)^3535 := by
    have hnat : (1715796107 : ℕ)^4559*100000000000000^3535 ≤ 10296977577907^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715796107 10000000000 10296977577907 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450513527/10000000000 : ℝ)^4559 ≤ (22859146985593/50000000000000 : ℝ)^3535 := by
    have hnat : (5450513527 : ℕ)^4559*50000000000000^3535 ≤ 22859146985593^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450513527 10000000000 22859146985593 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165298963/312500000 : ℝ), (-1715796107/10000000000 : ℝ), (5450513527/10000000000 : ℝ)] ![(43984728438381/100000000000000 : ℝ), (10296977577907/100000000000000 : ℝ), (22859146985593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165298963/312500000 : ℝ)|^4559 ≤ (43984728438381/100000000000000 : ℝ)^3535
        have hw : |(165298963/312500000 : ℝ)|=(165298963/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1715796107/10000000000 : ℝ)|^4559 ≤ (10296977577907/100000000000000 : ℝ)^3535
        have hw : |(-1715796107/10000000000 : ℝ)|=(1715796107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450513527/10000000000 : ℝ)|^4559 ≤ (22859146985593/50000000000000 : ℝ)^3535
        have hw : |(5450513527/10000000000 : ℝ)|=(5450513527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s2_6 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289567633/10000000000 : ℝ)*x 0 + (5450513761/10000000000 : ℝ)*x 1 + (-214474331/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289567633/10000000000 : ℝ)^4559 ≤ (21992368599997/50000000000000 : ℝ)^3535 := by
    have hnat : (5289567633 : ℕ)^4559*50000000000000^3535 ≤ 21992368599997^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289567633 10000000000 21992368599997 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450513761/10000000000 : ℝ)^4559 ≤ (9143659300503/20000000000000 : ℝ)^3535 := by
    have hnat : (5450513761 : ℕ)^4559*20000000000000^3535 ≤ 9143659300503^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450513761 10000000000 9143659300503 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214474331/1250000000 : ℝ)^4559 ≤ (10296966285683/100000000000000 : ℝ)^3535 := by
    have hnat : (214474331 : ℕ)^4559*100000000000000^3535 ≤ 10296966285683^3535*1250000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214474331 1250000000 10296966285683 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289567633/10000000000 : ℝ), (5450513761/10000000000 : ℝ), (-214474331/1250000000 : ℝ)] ![(21992368599997/50000000000000 : ℝ), (9143659300503/20000000000000 : ℝ), (10296966285683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289567633/10000000000 : ℝ)|^4559 ≤ (21992368599997/50000000000000 : ℝ)^3535
        have hw : |(5289567633/10000000000 : ℝ)|=(5289567633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450513761/10000000000 : ℝ)|^4559 ≤ (9143659300503/20000000000000 : ℝ)^3535
        have hw : |(5450513761/10000000000 : ℝ)|=(5450513761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214474331/1250000000 : ℝ)|^4559 ≤ (10296966285683/100000000000000 : ℝ)^3535
        have hw : |(-214474331/1250000000 : ℝ)|=(214474331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s2_7 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532366757/1250000000 : ℝ)*x 0 + (4553787529/10000000000 : ℝ)*x 1 + (124387927/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532366757/1250000000 : ℝ)^4559 ≤ (3325973436769/10000000000000 : ℝ)^3535 := by
    have hnat : (532366757 : ℕ)^4559*10000000000000^3535 ≤ 3325973436769^3535*1250000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532366757 1250000000 3325973436769 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4553787529/10000000000 : ℝ)^4559 ≤ (36258681072021/100000000000000 : ℝ)^3535 := by
    have hnat : (4553787529 : ℕ)^4559*100000000000000^3535 ≤ 36258681072021^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553787529 10000000000 36258681072021 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124387927/312500000 : ℝ)^4559 ≤ (1905099034213/6250000000000 : ℝ)^3535 := by
    have hnat : (124387927 : ℕ)^4559*6250000000000^3535 ≤ 1905099034213^3535*312500000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124387927 312500000 1905099034213 6250000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532366757/1250000000 : ℝ), (4553787529/10000000000 : ℝ), (124387927/312500000 : ℝ)] ![(3325973436769/10000000000000 : ℝ), (36258681072021/100000000000000 : ℝ), (1905099034213/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532366757/1250000000 : ℝ)|^4559 ≤ (3325973436769/10000000000000 : ℝ)^3535
        have hw : |(532366757/1250000000 : ℝ)|=(532366757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4553787529/10000000000 : ℝ)|^4559 ≤ (36258681072021/100000000000000 : ℝ)^3535
        have hw : |(4553787529/10000000000 : ℝ)|=(4553787529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(124387927/312500000 : ℝ)|^4559 ≤ (1905099034213/6250000000000 : ℝ)^3535
        have hw : |(124387927/312500000 : ℝ)|=(124387927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1531_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4533/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2151/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5289/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1991/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4533/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2151/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4533/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2151/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4533/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2151/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4533/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2151/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4533/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2151/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4533/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2151/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (2151/25000 : ℝ) ^ (4557/1024 : ℝ) ≤ (908194203351389/50000000000000000000 : ℝ) := by
    have hpowers : (2151/25000 : ℝ)^4557 ≤ (908194203351389/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2151 : ℕ)^4557*50000000000000000000^1024 ≤ 908194203351389^1024*25000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2151 25000 908194203351389 50000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2151/25000 : ℝ)) (X := (908194203351389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4533/25000 : ℝ) ^ (4557/1024 : ℝ) ≤ (2004465416763781/4000000000000000000 : ℝ) := by
    have hpowers : (4533/25000 : ℝ)^4557 ≤ (2004465416763781/4000000000000000000 : ℝ)^1024 := by
      have hnat : (4533 : ℕ)^4557*4000000000000000000^1024 ≤ 2004465416763781^1024*25000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4533 25000 2004465416763781 4000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4533/25000 : ℝ)) (X := (2004465416763781/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000908194203351389/25000000000000000000 : ℝ) ≤ (2500020407675403/2500000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (25000908194203351389/25000000000000000000 : ℝ)^1024 ≤ (2500020407675403/2500000000000000 : ℝ)^4557 := by
      have hnat : (25000908194203351389 : ℕ)^1024*2500000000000000^4557 ≤ 2500020407675403^4557*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000908194203351389 25000000000000000000 2500020407675403 2500000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500020407675403/2500000000000000 : ℝ)) (X := (25000908194203351389/25000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051928023825797303/100000000000000000000 : ℝ) ≤ (10001166635854319/10000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (100051928023825797303/100000000000000000000 : ℝ)^1024 ≤ (10001166635854319/10000000000000000 : ℝ)^4557 := by
      have hnat : (100051928023825797303 : ℕ)^1024*10000000000000000^4557 ≤ 10001166635854319^4557*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051928023825797303 100000000000000000000 10001166635854319 10000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001166635854319/10000000000000000 : ℝ)) (X := (100051928023825797303/100000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2002004465416763781/2000000000000000000 : ℝ) ≤ (5001125820503513/5000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (2002004465416763781/2000000000000000000 : ℝ)^1024 ≤ (5001125820503513/5000000000000000 : ℝ)^4557 := by
      have hnat : (2002004465416763781 : ℕ)^1024*5000000000000000^4557 ≤ 5001125820503513^4557*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002004465416763781 2000000000000000000 5001125820503513 5000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001125820503513/5000000000000000 : ℝ)) (X := (2002004465416763781/2000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(908194203351389/50000000000000000000 : ℝ) ≤ ((793850891738809809/794000000000000000 : ℝ)+2*(1085005152707/952800000000000 : ℝ)*(2151/25000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (793850891738809809/794000000000000000 : ℝ)+2*(1085005152707/952800000000000 : ℝ)*(2151/25000 : ℝ)=(2500020407675403/2500000000000000 : ℝ) by norm_num, show 1+2*(908194203351389/50000000000000000000 : ℝ)=(25000908194203351389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2004465416763781/4000000000000000000 : ℝ)+(908194203351389/50000000000000000000 : ℝ) ≤ ((793850891738809809/794000000000000000 : ℝ)+(1085005152707/952800000000000 : ℝ)*((4533/25000 : ℝ)+(2151/25000 : ℝ)))^(4557/1024 : ℝ) := by
    rw [show (793850891738809809/794000000000000000 : ℝ)+(1085005152707/952800000000000 : ℝ)*((4533/25000 : ℝ)+(2151/25000 : ℝ))=(10001166635854319/10000000000000000 : ℝ) by norm_num, show 1+(2004465416763781/4000000000000000000 : ℝ)+(908194203351389/50000000000000000000 : ℝ)=(100051928023825797303/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2004465416763781/4000000000000000000 : ℝ) ≤ ((793850891738809809/794000000000000000 : ℝ)+2*(1085005152707/952800000000000 : ℝ)*(4533/25000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (793850891738809809/794000000000000000 : ℝ)+2*(1085005152707/952800000000000 : ℝ)*(4533/25000 : ℝ)=(5001125820503513/5000000000000000 : ℝ) by norm_num, show 1+2*(2004465416763781/4000000000000000000 : ℝ)=(2002004465416763781/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (793850891738809809/794000000000000000 : ℝ)*(X 1 0+X 2 0)+(1085005152707/952800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (2151/25000 : ℝ)) (hi := (4533/25000 : ℝ)) (c := (793850891738809809/794000000000000000 : ℝ)) (alpha := (1085005152707/952800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (793850891738809809/794000000000000000 : ℝ)*(X 0 1+X 2 1)+(1085005152707/952800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (2151/25000 : ℝ)) (hi := (4533/25000 : ℝ)) (c := (793850891738809809/794000000000000000 : ℝ)) (alpha := (1085005152707/952800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (793850891738809809/794000000000000000 : ℝ)*(X 0 2+X 1 2)+(1085005152707/952800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (2151/25000 : ℝ)) (hi := (4533/25000 : ℝ)) (c := (793850891738809809/794000000000000000 : ℝ)) (alpha := (1085005152707/952800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-73477999/400000000 : ℝ)*X 0 0+(545207731/1000000000 : ℝ)*X 0 1+(2599724231/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42848661/80000000 : ℝ)*X 1 0+(-491714707/2500000000 : ℝ)*X 1 1+(2599724421/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678041663/5000000000 : ℝ)*X 2 0+(324965527/625000000 : ℝ)*X 2 1+(-983429217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2129412129/5000000000 : ℝ)*X 0 0+(1988408437/5000000000 : ℝ)*X 0 1+(4557353637/10000000000 : ℝ)*X 0 2+(2129412129/5000000000 : ℝ)*X 1 0+(1988408437/5000000000 : ℝ)*X 1 1+(4557353637/10000000000 : ℝ)*X 1 2+(2129412129/5000000000 : ℝ)*X 2 0+(1988408437/5000000000 : ℝ)*X 2 1+(4557353637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-367399191/2000000000 : ℝ)*X 0 0+(5201001369/10000000000 : ℝ)*X 0 1+(5450511917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165298963/312500000 : ℝ)*X 1 0+(-1715796107/10000000000 : ℝ)*X 1 1+(5450513527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289567633/10000000000 : ℝ)*X 2 0+(5450513761/10000000000 : ℝ)*X 2 1+(-214474331/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((532366757/1250000000 : ℝ)*X 0 0+(4553787529/10000000000 : ℝ)*X 0 1+(124387927/312500000 : ℝ)*X 0 2+(532366757/1250000000 : ℝ)*X 1 0+(4553787529/10000000000 : ℝ)*X 1 1+(124387927/312500000 : ℝ)*X 1 2+(532366757/1250000000 : ℝ)*X 2 0+(4553787529/10000000000 : ℝ)*X 2 1+(124387927/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114433213285047018855597/15880000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194220129/12500000000000 : ℝ)*(base19) + (44168723/2500000000000 : ℝ)*(base23) + (117198611/100000000000000 : ℝ)*(upper3) + (163407559/100000000000000 : ℝ)*(upper4) + (160857339/50000000000000 : ℝ)*(upper5) + (2840498911450803/100000000000000 : ℝ)*(major0) + (2840498911450803/100000000000000 : ℝ)*(major1) + (2840498911450803/100000000000000 : ℝ)*(major2) + (1979198150163599/50000000000000 : ℝ)*(sp0) + (1979212889530953/50000000000000 : ℝ)*(sp1) + (3958425566074019/100000000000000 : ℝ)*(sp2) + (4306392497601/250000000000 : ℝ)*(sp3) + (1551624787/5000000000000 : ℝ)*(sp4) + (13250834203/100000000000000 : ℝ)*(sp7) + (430642562468651/25000000000000 : ℝ)*(f.failure) + (1979213666411469/50000000000000 : ℝ)*(f.sum) + (33557505828067/15880000000000000000000000000 : ℝ)*base65 + (193917649181705873/79400000000000000000000000000000 : ℝ)*base68 + (310115280070894127/79400000000000000000000000000000 : ℝ)*base69 + (220120448172894127/79400000000000000000000000000000 : ℝ)*base71 + (23942658092187/15880000000000000000000000000 : ℝ)*base73 + (299125542268494127/79400000000000000000000000000000 : ℝ)*base75 + (647064432980705873/79400000000000000000000000000000 : ℝ)*base78 + (310408784960905873/79400000000000000000000000000000 : ℝ)*base80 + (98418261723427/15880000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1282709/312500000000000000000 : ℝ)*base89 + (1282709/312500000000000000000 : ℝ)*base91 + (1282709/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13243862991200838746200359/9925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23736867/10000000000000 : ℝ)*(base8) + (1001297759/100000000000000 : ℝ)*(base15) + (84161311/20000000000000 : ℝ)*(base29) + (80220887/50000000000000 : ℝ)*(lower2) + (20661407/12500000000000 : ℝ)*(lower4) + (2875957660138713/100000000000000 : ℝ)*(major0) + (718989520236317/25000000000000 : ℝ)*(major1) + (718989520236317/25000000000000 : ℝ)*(major2) + (5238029243/25000000000000 : ℝ)*(sp2) + (6488008819/100000000000000 : ℝ)*(sp3) + (1001960511232749/25000000000000 : ℝ)*(sp4) + (4007840860195351/100000000000000 : ℝ)*(sp5) + (200391045468807/5000000000000 : ℝ)*(sp6) + (348813469420447/20000000000000 : ℝ)*(sp7) + (872036917555527/50000000000000 : ℝ)*(f.failure) + (2003921141149833/50000000000000 : ℝ)*(f.sum) + (21533789151499/11910000000000000000000000000 : ℝ)*base65 + (293599124366552141/59550000000000000000000000000000 : ℝ)*base68 + (341987693473052141/59550000000000000000000000000000 : ℝ)*base70 + (1856743303256697451/238200000000000000000000000000000 : ℝ)*base71 + (60890744451353/95280000000000000000000000000 : ℝ)*base74 + (78647693661784539/9925000000000000000000000000000 : ℝ)*base75 + (3043081451446502549/238200000000000000000000000000000 : ℝ)*base78 + (102727838824840461/9925000000000000000000000000000 : ℝ)*base80 + (224255368372567/95280000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (41807/625000000000000000000 : ℝ)*base90 + (41807/625000000000000000000 : ℝ)*base92 + (41807/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1531_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4533/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2151/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1991/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1531_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1531_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1991/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1531_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1531_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1531_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1991/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1531_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

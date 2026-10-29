-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1321_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:43:35.095378+00:00
-- url     : https://prove2.me/submissions/269c35dc-4ee7-49cf-9086-fcec8d722670

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
theorem support_rectangle_w1321_s0_0 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-364325219/2000000000 : ℝ)*x 0 + (1501509059/2500000000 : ℝ)*x 1 + (2402936961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364325219/2000000000 : ℝ)^4281 ≤ (1333084928269/12500000000000 : ℝ)^3257 := by
    have hnat : (364325219 : ℕ)^4281*12500000000000^3257 ≤ 1333084928269^3257*2000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364325219 2000000000 1333084928269 12500000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1501509059/2500000000 : ℝ)^4281 ≤ (10233072451731/20000000000000 : ℝ)^3257 := by
    have hnat : (1501509059 : ℕ)^4281*20000000000000^3257 ≤ 10233072451731^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501509059 2500000000 10233072451731 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2402936961/5000000000 : ℝ)^4281 ≤ (7633991661817/20000000000000 : ℝ)^3257 := by
    have hnat : (2402936961 : ℕ)^4281*20000000000000^3257 ≤ 7633991661817^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402936961 5000000000 7633991661817 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364325219/2000000000 : ℝ), (1501509059/2500000000 : ℝ), (2402936961/5000000000 : ℝ)] ![(1333084928269/12500000000000 : ℝ), (10233072451731/20000000000000 : ℝ), (7633991661817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364325219/2000000000 : ℝ)|^4281 ≤ (1333084928269/12500000000000 : ℝ)^3257
        have hw : |(-364325219/2000000000 : ℝ)|=(364325219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1501509059/2500000000 : ℝ)|^4281 ≤ (10233072451731/20000000000000 : ℝ)^3257
        have hw : |(1501509059/2500000000 : ℝ)|=(1501509059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2402936961/5000000000 : ℝ)|^4281 ≤ (7633991661817/20000000000000 : ℝ)^3257
        have hw : |(2402936961/5000000000 : ℝ)|=(2402936961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s0_1 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (344010373/625000000 : ℝ)*x 0 + (-1252420393/5000000000 : ℝ)*x 1 + (1201468513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344010373/625000000 : ℝ)^4281 ≤ (45621020792647/100000000000000 : ℝ)^3257 := by
    have hnat : (344010373 : ℕ)^4281*100000000000000^3257 ≤ 45621020792647^3257*625000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344010373 625000000 45621020792647 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252420393/5000000000 : ℝ)^4281 ≤ (8104509766009/50000000000000 : ℝ)^3257 := by
    have hnat : (1252420393 : ℕ)^4281*50000000000000^3257 ≤ 8104509766009^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252420393 5000000000 8104509766009 50000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201468513/2500000000 : ℝ)^4281 ≤ (38169959666211/100000000000000 : ℝ)^3257 := by
    have hnat : (1201468513 : ℕ)^4281*100000000000000^3257 ≤ 38169959666211^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201468513 2500000000 38169959666211 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344010373/625000000 : ℝ), (-1252420393/5000000000 : ℝ), (1201468513/2500000000 : ℝ)] ![(45621020792647/100000000000000 : ℝ), (8104509766009/50000000000000 : ℝ), (38169959666211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344010373/625000000 : ℝ)|^4281 ≤ (45621020792647/100000000000000 : ℝ)^3257
        have hw : |(344010373/625000000 : ℝ)|=(344010373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252420393/5000000000 : ℝ)|^4281 ≤ (8104509766009/50000000000000 : ℝ)^3257
        have hw : |(-1252420393/5000000000 : ℝ)|=(1252420393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1201468513/2500000000 : ℝ)|^4281 ≤ (38169959666211/100000000000000 : ℝ)^3257
        have hw : |(1201468513/2500000000 : ℝ)|=(1201468513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s0_2 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (688020653/1250000000 : ℝ)*x 0 + (4805874449/10000000000 : ℝ)*x 1 + (-626210313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688020653/1250000000 : ℝ)^4281 ≤ (22810506343629/50000000000000 : ℝ)^3257 := by
    have hnat : (688020653 : ℕ)^4281*50000000000000^3257 ≤ 22810506343629^3257*1250000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688020653 1250000000 22810506343629 50000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4805874449/10000000000 : ℝ)^4281 ≤ (4771245476333/12500000000000 : ℝ)^3257 := by
    have hnat : (4805874449 : ℕ)^4281*12500000000000^3257 ≤ 4771245476333^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805874449 10000000000 4771245476333 12500000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626210313/2500000000 : ℝ)^4281 ≤ (810451174781/5000000000000 : ℝ)^3257 := by
    have hnat : (626210313 : ℕ)^4281*5000000000000^3257 ≤ 810451174781^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626210313 2500000000 810451174781 5000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(688020653/1250000000 : ℝ), (4805874449/10000000000 : ℝ), (-626210313/2500000000 : ℝ)] ![(22810506343629/50000000000000 : ℝ), (4771245476333/12500000000000 : ℝ), (810451174781/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(688020653/1250000000 : ℝ)|^4281 ≤ (22810506343629/50000000000000 : ℝ)^3257
        have hw : |(688020653/1250000000 : ℝ)|=(688020653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4805874449/10000000000 : ℝ)|^4281 ≤ (4771245476333/12500000000000 : ℝ)^3257
        have hw : |(4805874449/10000000000 : ℝ)|=(4805874449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-626210313/2500000000 : ℝ)|^4281 ≤ (810451174781/5000000000000 : ℝ)^3257
        have hw : |(-626210313/2500000000 : ℝ)|=(626210313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s0_3 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2090953849/5000000000 : ℝ)*x 0 + (388459341/1250000000 : ℝ)*x 1 + (5601652599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090953849/5000000000 : ℝ)^4281 ≤ (1271729226247/4000000000000 : ℝ)^3257 := by
    have hnat : (2090953849 : ℕ)^4281*4000000000000^3257 ≤ 1271729226247^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090953849 5000000000 1271729226247 4000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388459341/1250000000 : ℝ)^4281 ≤ (21520750847623/100000000000000 : ℝ)^3257 := by
    have hnat : (388459341 : ℕ)^4281*100000000000000^3257 ≤ 21520750847623^3257*1250000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388459341 1250000000 21520750847623 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5601652599/10000000000 : ℝ)^4281 ≤ (46686018472763/100000000000000 : ℝ)^3257 := by
    have hnat : (5601652599 : ℕ)^4281*100000000000000^3257 ≤ 46686018472763^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5601652599 10000000000 46686018472763 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090953849/5000000000 : ℝ), (388459341/1250000000 : ℝ), (5601652599/10000000000 : ℝ)] ![(1271729226247/4000000000000 : ℝ), (21520750847623/100000000000000 : ℝ), (46686018472763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090953849/5000000000 : ℝ)|^4281 ≤ (1271729226247/4000000000000 : ℝ)^3257
        have hw : |(2090953849/5000000000 : ℝ)|=(2090953849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388459341/1250000000 : ℝ)|^4281 ≤ (21520750847623/100000000000000 : ℝ)^3257
        have hw : |(388459341/1250000000 : ℝ)|=(388459341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5601652599/10000000000 : ℝ)|^4281 ≤ (46686018472763/100000000000000 : ℝ)^3257
        have hw : |(5601652599/10000000000 : ℝ)|=(5601652599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s0_4 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1826193913/10000000000 : ℝ)*x 0 + (967360087/2000000000 : ℝ)*x 1 + (1194801341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1826193913/10000000000 : ℝ)^4281 ≤ (10699843233219/100000000000000 : ℝ)^3257 := by
    have hnat : (1826193913 : ℕ)^4281*100000000000000^3257 ≤ 10699843233219^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826193913 10000000000 10699843233219 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967360087/2000000000 : ℝ)^4281 ≤ (38493139595757/100000000000000 : ℝ)^3257 := by
    have hnat : (967360087 : ℕ)^4281*100000000000000^3257 ≤ 38493139595757^3257*2000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967360087 2000000000 38493139595757 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194801341/2000000000 : ℝ)^4281 ≤ (10161403431083/20000000000000 : ℝ)^3257 := by
    have hnat : (1194801341 : ℕ)^4281*20000000000000^3257 ≤ 10161403431083^3257*2000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194801341 2000000000 10161403431083 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1826193913/10000000000 : ℝ), (967360087/2000000000 : ℝ), (1194801341/2000000000 : ℝ)] ![(10699843233219/100000000000000 : ℝ), (38493139595757/100000000000000 : ℝ), (10161403431083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1826193913/10000000000 : ℝ)|^4281 ≤ (10699843233219/100000000000000 : ℝ)^3257
        have hw : |(-1826193913/10000000000 : ℝ)|=(1826193913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(967360087/2000000000 : ℝ)|^4281 ≤ (38493139595757/100000000000000 : ℝ)^3257
        have hw : |(967360087/2000000000 : ℝ)|=(967360087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194801341/2000000000 : ℝ)|^4281 ≤ (10161403431083/20000000000000 : ℝ)^3257
        have hw : |(1194801341/2000000000 : ℝ)|=(1194801341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s0_5 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5177222211/10000000000 : ℝ)*x 0 + (-1336709003/10000000000 : ℝ)*x 1 + (5974006639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5177222211/10000000000 : ℝ)^4281 ≤ (42092906205523/100000000000000 : ℝ)^3257 := by
    have hnat : (5177222211 : ℕ)^4281*100000000000000^3257 ≤ 42092906205523^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177222211 10000000000 42092906205523 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1336709003/10000000000 : ℝ)^4281 ≤ (3550038680239/50000000000000 : ℝ)^3257 := by
    have hnat : (1336709003 : ℕ)^4281*50000000000000^3257 ≤ 3550038680239^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336709003 10000000000 3550038680239 50000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5974006639/10000000000 : ℝ)^4281 ≤ (50807016417631/100000000000000 : ℝ)^3257 := by
    have hnat : (5974006639 : ℕ)^4281*100000000000000^3257 ≤ 50807016417631^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5974006639 10000000000 50807016417631 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5177222211/10000000000 : ℝ), (-1336709003/10000000000 : ℝ), (5974006639/10000000000 : ℝ)] ![(42092906205523/100000000000000 : ℝ), (3550038680239/50000000000000 : ℝ), (50807016417631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5177222211/10000000000 : ℝ)|^4281 ≤ (42092906205523/100000000000000 : ℝ)^3257
        have hw : |(5177222211/10000000000 : ℝ)|=(5177222211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1336709003/10000000000 : ℝ)|^4281 ≤ (3550038680239/50000000000000 : ℝ)^3257
        have hw : |(-1336709003/10000000000 : ℝ)|=(1336709003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5974006639/10000000000 : ℝ)|^4281 ≤ (50807016417631/100000000000000 : ℝ)^3257
        have hw : |(5974006639/10000000000 : ℝ)|=(5974006639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s0_6 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5177222229/10000000000 : ℝ)*x 0 + (5974006679/10000000000 : ℝ)*x 1 + (-1336708911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5177222229/10000000000 : ℝ)^4281 ≤ (42092906397881/100000000000000 : ℝ)^3257 := by
    have hnat : (5177222229 : ℕ)^4281*100000000000000^3257 ≤ 42092906397881^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177222229 10000000000 42092906397881 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5974006679/10000000000 : ℝ)^4281 ≤ (50807016864773/100000000000000 : ℝ)^3257 := by
    have hnat : (5974006679 : ℕ)^4281*100000000000000^3257 ≤ 50807016864773^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5974006679 10000000000 50807016864773 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1336708911/10000000000 : ℝ)^4281 ≤ (7100076718173/100000000000000 : ℝ)^3257 := by
    have hnat : (1336708911 : ℕ)^4281*100000000000000^3257 ≤ 7100076718173^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336708911 10000000000 7100076718173 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5177222229/10000000000 : ℝ), (5974006679/10000000000 : ℝ), (-1336708911/10000000000 : ℝ)] ![(42092906397881/100000000000000 : ℝ), (50807016864773/100000000000000 : ℝ), (7100076718173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5177222229/10000000000 : ℝ)|^4281 ≤ (42092906397881/100000000000000 : ℝ)^3257
        have hw : |(5177222229/10000000000 : ℝ)|=(5177222229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5974006679/10000000000 : ℝ)|^4281 ≤ (50807016864773/100000000000000 : ℝ)^3257
        have hw : |(5974006679/10000000000 : ℝ)|=(5974006679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1336708911/10000000000 : ℝ)|^4281 ≤ (7100076718173/100000000000000 : ℝ)^3257
        have hw : |(-1336708911/10000000000 : ℝ)|=(1336708911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s0_7 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52392489/125000000 : ℝ)*x 0 + (5537386833/10000000000 : ℝ)*x 1 + (3174232443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52392489/125000000 : ℝ)^4281 ≤ (1594405523381/5000000000000 : ℝ)^3257 := by
    have hnat : (52392489 : ℕ)^4281*5000000000000^3257 ≤ 1594405523381^3257*125000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52392489 125000000 1594405523381 5000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5537386833/10000000000 : ℝ)^4281 ≤ (9196656624751/20000000000000 : ℝ)^3257 := by
    have hnat : (5537386833 : ℕ)^4281*20000000000000^3257 ≤ 9196656624751^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537386833 10000000000 9196656624751 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3174232443/10000000000 : ℝ)^4281 ≤ (4425721279573/20000000000000 : ℝ)^3257 := by
    have hnat : (3174232443 : ℕ)^4281*20000000000000^3257 ≤ 4425721279573^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174232443 10000000000 4425721279573 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52392489/125000000 : ℝ), (5537386833/10000000000 : ℝ), (3174232443/10000000000 : ℝ)] ![(1594405523381/5000000000000 : ℝ), (9196656624751/20000000000000 : ℝ), (4425721279573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52392489/125000000 : ℝ)|^4281 ≤ (1594405523381/5000000000000 : ℝ)^3257
        have hw : |(52392489/125000000 : ℝ)|=(52392489/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5537386833/10000000000 : ℝ)|^4281 ≤ (9196656624751/20000000000000 : ℝ)^3257
        have hw : |(5537386833/10000000000 : ℝ)|=(5537386833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3174232443/10000000000 : ℝ)|^4281 ≤ (4425721279573/20000000000000 : ℝ)^3257
        have hw : |(3174232443/10000000000 : ℝ)|=(3174232443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1321_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9618859/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (251/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27023/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (535/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^535 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^535*1^128 ≤ 0^128*1^535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 535 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (535/128 : ℝ) ≤ (271422054184063893/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^535 ≤ (271422054184063893/12500000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^535*12500000000000000000^128 ≤ 271422054184063893^128*5^535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 271422054184063893 12500000000000000000 535 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (271422054184063893/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^535 := by
      have hnat : (1 : ℕ)^128*1^535 ≤ 1^535*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12771422054184063893/12500000000000000000 : ℝ) ≤ (5025763498655791/5000000000000000 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (12771422054184063893/12500000000000000000 : ℝ)^128 ≤ (5025763498655791/5000000000000000 : ℝ)^535 := by
      have hnat : (12771422054184063893 : ℕ)^128*5000000000000000^535 ≤ 5025763498655791^535*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12771422054184063893 12500000000000000000 5025763498655791 5000000000000000 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025763498655791/5000000000000000 : ℝ)) (X := (12771422054184063893/12500000000000000000 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6521422054184063893/6250000000000000000 : ℝ) ≤ (2525763498655791/2500000000000000 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (6521422054184063893/6250000000000000000 : ℝ)^128 ≤ (2525763498655791/2500000000000000 : ℝ)^535 := by
      have hnat : (6521422054184063893 : ℕ)^128*2500000000000000^535 ≤ 2525763498655791^535*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6521422054184063893 6250000000000000000 2525763498655791 2500000000000000 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2525763498655791/2500000000000000 : ℝ)) (X := (6521422054184063893/6250000000000000000 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25763498655791/2000000000000000 : ℝ)*(0 : ℝ))^(535/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(25763498655791/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(271422054184063893/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25763498655791/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(535/128 : ℝ) := by
    rw [show (1 : ℝ)+(25763498655791/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5025763498655791/5000000000000000 : ℝ) by norm_num, show 1+(271422054184063893/12500000000000000000 : ℝ)+(0 : ℝ)=(12771422054184063893/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(271422054184063893/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25763498655791/2000000000000000 : ℝ)*(2/5 : ℝ))^(535/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(25763498655791/2000000000000000 : ℝ)*(2/5 : ℝ)=(2525763498655791/2500000000000000 : ℝ) by norm_num, show 1+2*(271422054184063893/12500000000000000000 : ℝ)=(6521422054184063893/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25763498655791/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25763498655791/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25763498655791/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25763498655791/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25763498655791/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25763498655791/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-364325219/2000000000 : ℝ)*X 0 0+(1501509059/2500000000 : ℝ)*X 0 1+(2402936961/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((344010373/625000000 : ℝ)*X 1 0+(-1252420393/5000000000 : ℝ)*X 1 1+(1201468513/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((688020653/1250000000 : ℝ)*X 2 0+(4805874449/10000000000 : ℝ)*X 2 1+(-626210313/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2090953849/5000000000 : ℝ)*X 0 0+(388459341/1250000000 : ℝ)*X 0 1+(5601652599/10000000000 : ℝ)*X 0 2+(2090953849/5000000000 : ℝ)*X 1 0+(388459341/1250000000 : ℝ)*X 1 1+(5601652599/10000000000 : ℝ)*X 1 2+(2090953849/5000000000 : ℝ)*X 2 0+(388459341/1250000000 : ℝ)*X 2 1+(5601652599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1826193913/10000000000 : ℝ)*X 0 0+(967360087/2000000000 : ℝ)*X 0 1+(1194801341/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5177222211/10000000000 : ℝ)*X 1 0+(-1336709003/10000000000 : ℝ)*X 1 1+(5974006639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5177222229/10000000000 : ℝ)*X 2 0+(5974006679/10000000000 : ℝ)*X 2 1+(-1336708911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((52392489/125000000 : ℝ)*X 0 0+(5537386833/10000000000 : ℝ)*X 0 1+(3174232443/10000000000 : ℝ)*X 0 2+(52392489/125000000 : ℝ)*X 1 0+(5537386833/10000000000 : ℝ)*X 1 1+(3174232443/10000000000 : ℝ)*X 1 2+(52392489/125000000 : ℝ)*X 2 0+(5537386833/10000000000 : ℝ)*X 2 1+(3174232443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15296937548729864584071/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104369451/100000000000000 : ℝ)*(base1) + (958388619/50000000000000 : ℝ)*(base19) + (1804149111/100000000000000 : ℝ)*(base23) + (281149207/100000000000000 : ℝ)*(upper3) + (127047017/100000000000000 : ℝ)*(upper5) + (24684095514973/4000000000000 : ℝ)*(major0) + (24684095514973/4000000000000 : ℝ)*(major1) + (24684095514973/4000000000000 : ℝ)*(major2) + (208306794762079/25000000000000 : ℝ)*(sp0) + (416615468701133/50000000000000 : ℝ)*(sp1) + (104153881253799/12500000000000 : ℝ)*(sp2) + (200484229409917/50000000000000 : ℝ)*(sp3) + (2889750319/50000000000000 : ℝ)*(sp4) + (3103430897/100000000000000 : ℝ)*(sp7) + (200485833310091/50000000000000 : ℝ)*(f.failure) + (52077053386219/6250000000000 : ℝ)*(f.sum) + (1618732626643/4000000000000000000000000000 : ℝ)*base65 + (23279310013357/8000000000000000000000000000 : ℝ)*base68 + (6969149026643/8000000000000000000000000000 : ℝ)*base69 + (26939196421357/8000000000000000000000000000 : ℝ)*base72 + (6599360550643/4000000000000000000000000000 : ℝ)*base73 + (47824520493357/8000000000000000000000000000 : ℝ)*base76 + (2508830981357/8000000000000000000000000000 : ℝ)*base78 + (10846306770643/8000000000000000000000000000 : ℝ)*base79 + (8619377046643/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2981169/312500000000000000000 : ℝ)*base89 + (2981169/312500000000000000000 : ℝ)*base91 + (2981169/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132782854040162098349097/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252542247/20000000000000 : ℝ)*(base19) + (1278428453/100000000000000 : ℝ)*(base23) + (25124977/50000000000000 : ℝ)*(base32) + (87224587/50000000000000 : ℝ)*(upper3) + (64890109/50000000000000 : ℝ)*(upper5) + (651255516692389/100000000000000 : ℝ)*(major0) + (651255516692389/100000000000000 : ℝ)*(major1) + (651255516692389/100000000000000 : ℝ)*(major2) + (56177499/2000000000000 : ℝ)*(sp1) + (3009354669/100000000000000 : ℝ)*(sp2) + (21983691864559/2500000000000 : ℝ)*(sp4) + (54958975187261/6250000000000 : ℝ)*(sp5) + (439671693399619/50000000000000 : ℝ)*(sp6) + (84632626301731/20000000000000 : ℝ)*(sp7) + (423163181758609/100000000000000 : ℝ)*(f.failure) + (21983691864559/2500000000000 : ℝ)*(f.sum) + (181856951525301/100000000000000000000000000000 : ℝ)*base66 + (145609302525301/200000000000000000000000000000 : ℝ)*base68 + (246960347474699/200000000000000000000000000000 : ℝ)*base69 + (669306126725301/200000000000000000000000000000 : ℝ)*base72 + (148341698225301/100000000000000000000000000000 : ℝ)*base74 + (1056776865325301/200000000000000000000000000000 : ℝ)*base76 + (515851251125301/200000000000000000000000000000 : ℝ)*base78 + (1318643420874699/200000000000000000000000000000 : ℝ)*base79 + (185203935425301/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (757131/625000000000000000000 : ℝ)*base89 + (757131/625000000000000000000 : ℝ)*base91 + (757131/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1321_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9618859/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (251/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1321_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1321_s1_0 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1004737601/5000000000 : ℝ)*x 0 + (2825844701/5000000000 : ℝ)*x 1 + (5039939323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004737601/5000000000 : ℝ)^4281 ≤ (12133106447961/100000000000000 : ℝ)^3257 := by
    have hnat : (1004737601 : ℕ)^4281*100000000000000^3257 ≤ 12133106447961^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004737601 5000000000 12133106447961 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2825844701/5000000000 : ℝ)^4281 ≤ (23617460894263/50000000000000 : ℝ)^3257 := by
    have hnat : (2825844701 : ℕ)^4281*50000000000000^3257 ≤ 23617460894263^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825844701 5000000000 23617460894263 50000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5039939323/10000000000 : ℝ)^4281 ≤ (40631971743557/100000000000000 : ℝ)^3257 := by
    have hnat : (5039939323 : ℕ)^4281*100000000000000^3257 ≤ 40631971743557^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039939323 10000000000 40631971743557 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1004737601/5000000000 : ℝ), (2825844701/5000000000 : ℝ), (5039939323/10000000000 : ℝ)] ![(12133106447961/100000000000000 : ℝ), (23617460894263/50000000000000 : ℝ), (40631971743557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1004737601/5000000000 : ℝ)|^4281 ≤ (12133106447961/100000000000000 : ℝ)^3257
        have hw : |(-1004737601/5000000000 : ℝ)|=(1004737601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2825844701/5000000000 : ℝ)|^4281 ≤ (23617460894263/50000000000000 : ℝ)^3257
        have hw : |(2825844701/5000000000 : ℝ)|=(2825844701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5039939323/10000000000 : ℝ)|^4281 ≤ (40631971743557/100000000000000 : ℝ)^3257
        have hw : |(5039939323/10000000000 : ℝ)|=(5039939323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s1_1 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407918453/10000000000 : ℝ)*x 0 + (-2336514143/10000000000 : ℝ)*x 1 + (2519969653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407918453/10000000000 : ℝ)^4281 ≤ (11143840375157/25000000000000 : ℝ)^3257 := by
    have hnat : (5407918453 : ℕ)^4281*25000000000000^3257 ≤ 11143840375157^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407918453 10000000000 11143840375157 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2336514143/10000000000 : ℝ)^4281 ≤ (2958533384919/20000000000000 : ℝ)^3257 := by
    have hnat : (2336514143 : ℕ)^4281*20000000000000^3257 ≤ 2958533384919^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336514143 10000000000 2958533384919 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2519969653/5000000000 : ℝ)^4281 ≤ (40631971563413/100000000000000 : ℝ)^3257 := by
    have hnat : (2519969653 : ℕ)^4281*100000000000000^3257 ≤ 40631971563413^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519969653 5000000000 40631971563413 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407918453/10000000000 : ℝ), (-2336514143/10000000000 : ℝ), (2519969653/5000000000 : ℝ)] ![(11143840375157/25000000000000 : ℝ), (2958533384919/20000000000000 : ℝ), (40631971563413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407918453/10000000000 : ℝ)|^4281 ≤ (11143840375157/25000000000000 : ℝ)^3257
        have hw : |(5407918453/10000000000 : ℝ)|=(5407918453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2336514143/10000000000 : ℝ)|^4281 ≤ (2958533384919/20000000000000 : ℝ)^3257
        have hw : |(-2336514143/10000000000 : ℝ)|=(2336514143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2519969653/5000000000 : ℝ)|^4281 ≤ (40631971563413/100000000000000 : ℝ)^3257
        have hw : |(2519969653/5000000000 : ℝ)|=(2519969653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s1_2 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407918171/10000000000 : ℝ)*x 0 + (2519969583/5000000000 : ℝ)*x 1 + (-2336514687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407918171/10000000000 : ℝ)^4281 ≤ (5571919805677/12500000000000 : ℝ)^3257 := by
    have hnat : (5407918171 : ℕ)^4281*12500000000000^3257 ≤ 5571919805677^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407918171 10000000000 5571919805677 12500000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2519969583/5000000000 : ℝ)^4281 ≤ (40631970079877/100000000000000 : ℝ)^3257 := by
    have hnat : (2519969583 : ℕ)^4281*100000000000000^3257 ≤ 40631970079877^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519969583 5000000000 40631970079877 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2336514687/10000000000 : ℝ)^4281 ≤ (3698167862883/25000000000000 : ℝ)^3257 := by
    have hnat : (2336514687 : ℕ)^4281*25000000000000^3257 ≤ 3698167862883^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336514687 10000000000 3698167862883 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407918171/10000000000 : ℝ), (2519969583/5000000000 : ℝ), (-2336514687/10000000000 : ℝ)] ![(5571919805677/12500000000000 : ℝ), (40631970079877/100000000000000 : ℝ), (3698167862883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407918171/10000000000 : ℝ)|^4281 ≤ (5571919805677/12500000000000 : ℝ)^3257
        have hw : |(5407918171/10000000000 : ℝ)|=(5407918171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2519969583/5000000000 : ℝ)|^4281 ≤ (40631970079877/100000000000000 : ℝ)^3257
        have hw : |(2519969583/5000000000 : ℝ)|=(2519969583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2336514687/10000000000 : ℝ)|^4281 ≤ (3698167862883/25000000000000 : ℝ)^3257
        have hw : |(-2336514687/10000000000 : ℝ)|=(2336514687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s1_3 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296035077/10000000000 : ℝ)*x 0 + (3704395813/10000000000 : ℝ)*x 1 + (2487816469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296035077/10000000000 : ℝ)^4281 ≤ (6587709302529/20000000000000 : ℝ)^3257 := by
    have hnat : (4296035077 : ℕ)^4281*20000000000000^3257 ≤ 6587709302529^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296035077 10000000000 6587709302529 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3704395813/10000000000 : ℝ)^4281 ≤ (27109545485451/100000000000000 : ℝ)^3257 := by
    have hnat : (3704395813 : ℕ)^4281*100000000000000^3257 ≤ 27109545485451^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704395813 10000000000 27109545485451 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2487816469/5000000000 : ℝ)^4281 ≤ (39951907991577/100000000000000 : ℝ)^3257 := by
    have hnat : (2487816469 : ℕ)^4281*100000000000000^3257 ≤ 39951907991577^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487816469 5000000000 39951907991577 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296035077/10000000000 : ℝ), (3704395813/10000000000 : ℝ), (2487816469/5000000000 : ℝ)] ![(6587709302529/20000000000000 : ℝ), (27109545485451/100000000000000 : ℝ), (39951907991577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296035077/10000000000 : ℝ)|^4281 ≤ (6587709302529/20000000000000 : ℝ)^3257
        have hw : |(4296035077/10000000000 : ℝ)|=(4296035077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3704395813/10000000000 : ℝ)|^4281 ≤ (27109545485451/100000000000000 : ℝ)^3257
        have hw : |(3704395813/10000000000 : ℝ)|=(3704395813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2487816469/5000000000 : ℝ)|^4281 ≤ (39951907991577/100000000000000 : ℝ)^3257
        have hw : |(2487816469/5000000000 : ℝ)|=(2487816469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s1_4 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010052111/10000000000 : ℝ)*x 0 + (5047739889/10000000000 : ℝ)*x 1 + (2821872203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010052111/10000000000 : ℝ)^4281 ≤ (12137685164297/100000000000000 : ℝ)^3257 := by
    have hnat : (2010052111 : ℕ)^4281*100000000000000^3257 ≤ 12137685164297^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010052111 10000000000 12137685164297 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5047739889/10000000000 : ℝ)^4281 ≤ (1628586079819/4000000000000 : ℝ)^3257 := by
    have hnat : (5047739889 : ℕ)^4281*4000000000000^3257 ≤ 1628586079819^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5047739889 10000000000 1628586079819 4000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2821872203/5000000000 : ℝ)^4281 ≤ (11786915706193/25000000000000 : ℝ)^3257 := by
    have hnat : (2821872203 : ℕ)^4281*25000000000000^3257 ≤ 11786915706193^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821872203 5000000000 11786915706193 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010052111/10000000000 : ℝ), (5047739889/10000000000 : ℝ), (2821872203/5000000000 : ℝ)] ![(12137685164297/100000000000000 : ℝ), (1628586079819/4000000000000 : ℝ), (11786915706193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010052111/10000000000 : ℝ)|^4281 ≤ (12137685164297/100000000000000 : ℝ)^3257
        have hw : |(-2010052111/10000000000 : ℝ)|=(2010052111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5047739889/10000000000 : ℝ)|^4281 ≤ (1628586079819/4000000000000 : ℝ)^3257
        have hw : |(5047739889/10000000000 : ℝ)|=(5047739889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2821872203/5000000000 : ℝ)|^4281 ≤ (11786915706193/25000000000000 : ℝ)^3257
        have hw : |(2821872203/5000000000 : ℝ)|=(2821872203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s1_5 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2624730297/5000000000 : ℝ)*x 0 + (-3465419/20000000 : ℝ)*x 1 + (5643744019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624730297/5000000000 : ℝ)^4281 ≤ (10716644216909/25000000000000 : ℝ)^3257 := by
    have hnat : (2624730297 : ℕ)^4281*25000000000000^3257 ≤ 10716644216909^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624730297 5000000000 10716644216909 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3465419/20000000 : ℝ)^4281 ≤ (1248220567507/12500000000000 : ℝ)^3257 := by
    have hnat : (3465419 : ℕ)^4281*12500000000000^3257 ≤ 1248220567507^3257*20000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3465419 20000000 1248220567507 12500000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5643744019/10000000000 : ℝ)^4281 ≤ (47147658575337/100000000000000 : ℝ)^3257 := by
    have hnat : (5643744019 : ℕ)^4281*100000000000000^3257 ≤ 47147658575337^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643744019 10000000000 47147658575337 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624730297/5000000000 : ℝ), (-3465419/20000000 : ℝ), (5643744019/10000000000 : ℝ)] ![(10716644216909/25000000000000 : ℝ), (1248220567507/12500000000000 : ℝ), (47147658575337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624730297/5000000000 : ℝ)|^4281 ≤ (10716644216909/25000000000000 : ℝ)^3257
        have hw : |(2624730297/5000000000 : ℝ)|=(2624730297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3465419/20000000 : ℝ)|^4281 ≤ (1248220567507/12500000000000 : ℝ)^3257
        have hw : |(-3465419/20000000 : ℝ)|=(3465419/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5643744019/10000000000 : ℝ)|^4281 ≤ (47147658575337/100000000000000 : ℝ)^3257
        have hw : |(5643744019/10000000000 : ℝ)|=(5643744019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s1_6 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13123651/25000000 : ℝ)*x 0 + (2821871929/5000000000 : ℝ)*x 1 + (-1732710009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13123651/25000000 : ℝ)^4281 ≤ (5358321848173/12500000000000 : ℝ)^3257 := by
    have hnat : (13123651 : ℕ)^4281*12500000000000^3257 ≤ 5358321848173^3257*25000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13123651 25000000 5358321848173 12500000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2821871929/5000000000 : ℝ)^4281 ≤ (47147656807483/100000000000000 : ℝ)^3257 := by
    have hnat : (2821871929 : ℕ)^4281*100000000000000^3257 ≤ 47147656807483^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821871929 5000000000 47147656807483 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732710009/10000000000 : ℝ)^4281 ≤ (1997153679147/20000000000000 : ℝ)^3257 := by
    have hnat : (1732710009 : ℕ)^4281*20000000000000^3257 ≤ 1997153679147^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732710009 10000000000 1997153679147 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13123651/25000000 : ℝ), (2821871929/5000000000 : ℝ), (-1732710009/10000000000 : ℝ)] ![(5358321848173/12500000000000 : ℝ), (47147656807483/100000000000000 : ℝ), (1997153679147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13123651/25000000 : ℝ)|^4281 ≤ (5358321848173/12500000000000 : ℝ)^3257
        have hw : |(13123651/25000000 : ℝ)|=(13123651/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2821871929/5000000000 : ℝ)|^4281 ≤ (47147656807483/100000000000000 : ℝ)^3257
        have hw : |(2821871929/5000000000 : ℝ)|=(2821871929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1732710009/10000000000 : ℝ)|^4281 ≤ (1997153679147/20000000000000 : ℝ)^3257
        have hw : |(-1732710009/10000000000 : ℝ)|=(1732710009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s1_7 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148616547/5000000000 : ℝ)*x 0 + (4959422571/10000000000 : ℝ)*x 1 + (1860452947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148616547/5000000000 : ℝ)^4281 ≤ (8237655092907/25000000000000 : ℝ)^3257 := by
    have hnat : (2148616547 : ℕ)^4281*25000000000000^3257 ≤ 8237655092907^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148616547 5000000000 8237655092907 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4959422571/10000000000 : ℝ)^4281 ≤ (9945227908381/25000000000000 : ℝ)^3257 := by
    have hnat : (4959422571 : ℕ)^4281*25000000000000^3257 ≤ 9945227908381^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4959422571 10000000000 9945227908381 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1860452947/5000000000 : ℝ)^4281 ≤ (6817116996123/25000000000000 : ℝ)^3257 := by
    have hnat : (1860452947 : ℕ)^4281*25000000000000^3257 ≤ 6817116996123^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860452947 5000000000 6817116996123 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148616547/5000000000 : ℝ), (4959422571/10000000000 : ℝ), (1860452947/5000000000 : ℝ)] ![(8237655092907/25000000000000 : ℝ), (9945227908381/25000000000000 : ℝ), (6817116996123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148616547/5000000000 : ℝ)|^4281 ≤ (8237655092907/25000000000000 : ℝ)^3257
        have hw : |(2148616547/5000000000 : ℝ)|=(2148616547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4959422571/10000000000 : ℝ)|^4281 ≤ (9945227908381/25000000000000 : ℝ)^3257
        have hw : |(4959422571/10000000000 : ℝ)|=(4959422571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1860452947/5000000000 : ℝ)|^4281 ≤ (6817116996123/25000000000000 : ℝ)^3257
        have hw : |(1860452947/5000000000 : ℝ)|=(1860452947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1321_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9618859/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1673/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19621/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (251/20000 : ℝ) ^ (535/128 : ℝ) ≤ (1129600686777/100000000000000000000 : ℝ) := by
    have hpowers : (251/20000 : ℝ)^535 ≤ (1129600686777/100000000000000000000 : ℝ)^128 := by
      have hnat : (251 : ℕ)^535*100000000000000000000^128 ≤ 1129600686777^128*20000^535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251 20000 1129600686777 100000000000000000000 535 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (251/20000 : ℝ)) (X := (1129600686777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hpowhi : (27023/100000 : ℝ) ^ (535/128 : ℝ) ≤ (105381379127502363/25000000000000000000 : ℝ) := by
    have hpowers : (27023/100000 : ℝ)^535 ≤ (105381379127502363/25000000000000000000 : ℝ)^128 := by
      have hnat : (27023 : ℕ)^535*25000000000000000000^128 ≤ 105381379127502363^128*100000^535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27023 100000 105381379127502363 25000000000000000000 535 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27023/100000 : ℝ)) (X := (105381379127502363/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001129600686777/50000000000000000000 : ℝ) ≤ (10000000054051921/10000000000000000 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (50000001129600686777/50000000000000000000 : ℝ)^128 ≤ (10000000054051921/10000000000000000 : ℝ)^535 := by
      have hnat : (50000001129600686777 : ℕ)^128*10000000000000000^535 ≤ 10000000054051921^535*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001129600686777 50000000000000000000 10000000054051921 10000000000000000 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000054051921/10000000000000000 : ℝ)) (X := (50000001129600686777/50000000000000000000 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100421526646110696229/100000000000000000000 : ℝ) ≤ (5005034496564709/5000000000000000 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (100421526646110696229/100000000000000000000 : ℝ)^128 ≤ (5005034496564709/5000000000000000 : ℝ)^535 := by
      have hnat : (100421526646110696229 : ℕ)^128*5000000000000000^535 ≤ 5005034496564709^535*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100421526646110696229 100000000000000000000 5005034496564709 5000000000000000 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005034496564709/5000000000000000 : ℝ)) (X := (100421526646110696229/100000000000000000000 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12605381379127502363/12500000000000000000 : ℝ) ≤ (2004027586441383/2000000000000000 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (12605381379127502363/12500000000000000000 : ℝ)^128 ≤ (2004027586441383/2000000000000000 : ℝ)^535 := by
      have hnat : (12605381379127502363 : ℕ)^128*2000000000000000^535 ≤ 2004027586441383^535*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12605381379127502363 12500000000000000000 2004027586441383 2000000000000000 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004027586441383/2000000000000000 : ℝ)) (X := (12605381379127502363/12500000000000000000 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1129600686777/100000000000000000000 : ℝ) ≤ ((128827364177862691429/128840000000000000000 : ℝ)+2*(10068939077497/2576800000000000 : ℝ)*(251/20000 : ℝ))^(535/128 : ℝ) := by
    rw [show (128827364177862691429/128840000000000000000 : ℝ)+2*(10068939077497/2576800000000000 : ℝ)*(251/20000 : ℝ)=(10000000054051921/10000000000000000 : ℝ) by norm_num, show 1+2*(1129600686777/100000000000000000000 : ℝ)=(50000001129600686777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(105381379127502363/25000000000000000000 : ℝ)+(1129600686777/100000000000000000000 : ℝ) ≤ ((128827364177862691429/128840000000000000000 : ℝ)+(10068939077497/2576800000000000 : ℝ)*((27023/100000 : ℝ)+(251/20000 : ℝ)))^(535/128 : ℝ) := by
    rw [show (128827364177862691429/128840000000000000000 : ℝ)+(10068939077497/2576800000000000 : ℝ)*((27023/100000 : ℝ)+(251/20000 : ℝ))=(5005034496564709/5000000000000000 : ℝ) by norm_num, show 1+(105381379127502363/25000000000000000000 : ℝ)+(1129600686777/100000000000000000000 : ℝ)=(100421526646110696229/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(105381379127502363/25000000000000000000 : ℝ) ≤ ((128827364177862691429/128840000000000000000 : ℝ)+2*(10068939077497/2576800000000000 : ℝ)*(27023/100000 : ℝ))^(535/128 : ℝ) := by
    rw [show (128827364177862691429/128840000000000000000 : ℝ)+2*(10068939077497/2576800000000000 : ℝ)*(27023/100000 : ℝ)=(2004027586441383/2000000000000000 : ℝ) by norm_num, show 1+2*(105381379127502363/25000000000000000000 : ℝ)=(12605381379127502363/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (128827364177862691429/128840000000000000000 : ℝ)*(X 1 0+X 2 0)+(10068939077497/2576800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (251/20000 : ℝ)) (hi := (27023/100000 : ℝ)) (c := (128827364177862691429/128840000000000000000 : ℝ)) (alpha := (10068939077497/2576800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (128827364177862691429/128840000000000000000 : ℝ)*(X 0 1+X 2 1)+(10068939077497/2576800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (251/20000 : ℝ)) (hi := (27023/100000 : ℝ)) (c := (128827364177862691429/128840000000000000000 : ℝ)) (alpha := (10068939077497/2576800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (128827364177862691429/128840000000000000000 : ℝ)*(X 0 2+X 1 2)+(10068939077497/2576800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (251/20000 : ℝ)) (hi := (27023/100000 : ℝ)) (c := (128827364177862691429/128840000000000000000 : ℝ)) (alpha := (10068939077497/2576800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1004737601/5000000000 : ℝ)*X 0 0+(2825844701/5000000000 : ℝ)*X 0 1+(5039939323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5407918453/10000000000 : ℝ)*X 1 0+(-2336514143/10000000000 : ℝ)*X 1 1+(2519969653/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5407918171/10000000000 : ℝ)*X 2 0+(2519969583/5000000000 : ℝ)*X 2 1+(-2336514687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4296035077/10000000000 : ℝ)*X 0 0+(3704395813/10000000000 : ℝ)*X 0 1+(2487816469/5000000000 : ℝ)*X 0 2+(4296035077/10000000000 : ℝ)*X 1 0+(3704395813/10000000000 : ℝ)*X 1 1+(2487816469/5000000000 : ℝ)*X 1 2+(4296035077/10000000000 : ℝ)*X 2 0+(3704395813/10000000000 : ℝ)*X 2 1+(2487816469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2010052111/10000000000 : ℝ)*X 0 0+(5047739889/10000000000 : ℝ)*X 0 1+(2821872203/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2624730297/5000000000 : ℝ)*X 1 0+(-3465419/20000000 : ℝ)*X 1 1+(5643744019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((13123651/25000000 : ℝ)*X 2 0+(2821871929/5000000000 : ℝ)*X 2 1+(-1732710009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148616547/5000000000 : ℝ)*X 0 0+(4959422571/10000000000 : ℝ)*X 0 1+(1860452947/5000000000 : ℝ)*X 0 2+(2148616547/5000000000 : ℝ)*X 1 0+(4959422571/10000000000 : ℝ)*X 1 1+(1860452947/5000000000 : ℝ)*X 1 2+(2148616547/5000000000 : ℝ)*X 2 0+(4959422571/10000000000 : ℝ)*X 2 1+(1860452947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6480014341548040245874931049/1610500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13345467/20000000000000 : ℝ)*(base1) + (52897799/100000000000000 : ℝ)*(base16) + (51198977/12500000000000 : ℝ)*(base19) + (75449839/20000000000000 : ℝ)*(base23) + (93469509/100000000000000 : ℝ)*(upper3) + (605323387883073/50000000000000 : ℝ)*(major0) + (605323387883073/50000000000000 : ℝ)*(major1) + (605323387883073/50000000000000 : ℝ)*(major2) + (163465654773221/10000000000000 : ℝ)*(sp0) + (326931358127919/20000000000000 : ℝ)*(sp1) + (817328437940007/50000000000000 : ℝ)*(sp2) + (19665888629447/2500000000000 : ℝ)*(sp3) + (154424867/20000000000000 : ℝ)*(sp4) + (276188861/50000000000000 : ℝ)*(sp7) + (786636164282937/100000000000000 : ℝ)*(f.failure) + (163465725312921/10000000000000 : ℝ)*(f.sum) + (76522548606621/64420000000000000000000000000 : ℝ)*base65 + (8269354857791331317/6442000000000000000000000000000000 : ℝ)*base67 + (16612881808670668683/6442000000000000000000000000000000 : ℝ)*base70 + (14452655565899331317/6442000000000000000000000000000000 : ℝ)*base71 + (315846933221141/64420000000000000000000000000 : ℝ)*base73 + (49900721615669331317/6442000000000000000000000000000000 : ℝ)*base75 + (41165130978221331317/6442000000000000000000000000000000 : ℝ)*base77 + (73738814062453331317/6442000000000000000000000000000000 : ℝ)*base79 + (332028335553519/64420000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5391117/625000000000000000000 : ℝ)*base90 + (5391117/625000000000000000000 : ℝ)*base92 + (5391117/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7808577914549091501577981563/3221000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131842787/50000000000000 : ℝ)*(base19) + (46623993/20000000000000 : ℝ)*(base23) + (1376111/4000000000000 : ℝ)*(upper2) + (47855801/100000000000000 : ℝ)*(upper3) + (10620113/25000000000000 : ℝ)*(upper5) + (621314676281817/50000000000000 : ℝ)*(major0) + (621314676281817/50000000000000 : ℝ)*(major1) + (621314676281817/50000000000000 : ℝ)*(major2) + (547530553/50000000000000 : ℝ)*(sp0) + (1129508797/100000000000000 : ℝ)*(sp1) + (838920099519589/50000000000000 : ℝ)*(sp4) + (838919950452957/50000000000000 : ℝ)*(sp5) + (10486506631127/625000000000 : ℝ)*(sp6) + (80741733021793/10000000000000 : ℝ)*(sp7) + (80741733021793/10000000000000 : ℝ)*(f.failure) + (335568258820057/20000000000000 : ℝ)*(f.sum) + (146779237472951/64420000000000000000000000000 : ℝ)*base66 + (60932845281988896493/6442000000000000000000000000000000 : ℝ)*base67 + (40457456929424896493/6442000000000000000000000000000000 : ℝ)*base69 + (38116624484082896493/6442000000000000000000000000000000 : ℝ)*base71 + (135674634408731/64420000000000000000000000000 : ℝ)*base74 + (36188383843460896493/6442000000000000000000000000000000 : ℝ)*base75 + (48084691559076896493/6442000000000000000000000000000000 : ℝ)*base77 + (3780035165936896493/6442000000000000000000000000000000 : ℝ)*base79 + (294273935334751/64420000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (455813/62500000000000000000 : ℝ)*base90 + (455813/62500000000000000000 : ℝ)*base92 + (455813/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1321_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9618859/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1673/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19621/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1321_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1321_s2_0 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2051492417/10000000000 : ℝ)*x 0 + (274281469/500000000 : ℝ)*x 1 + (2589558607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051492417/10000000000 : ℝ)^4281 ≤ (12467657595991/100000000000000 : ℝ)^3257 := by
    have hnat : (2051492417 : ℕ)^4281*100000000000000^3257 ≤ 12467657595991^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051492417 10000000000 12467657595991 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274281469/500000000 : ℝ)^4281 ≤ (5677397985421/12500000000000 : ℝ)^3257 := by
    have hnat : (274281469 : ℕ)^4281*12500000000000^3257 ≤ 5677397985421^3257*500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274281469 500000000 5677397985421 12500000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589558607/5000000000 : ℝ)^4281 ≤ (42113158510711/100000000000000 : ℝ)^3257 := by
    have hnat : (2589558607 : ℕ)^4281*100000000000000^3257 ≤ 42113158510711^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589558607 5000000000 42113158510711 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2051492417/10000000000 : ℝ), (274281469/500000000 : ℝ), (2589558607/5000000000 : ℝ)] ![(12467657595991/100000000000000 : ℝ), (5677397985421/12500000000000 : ℝ), (42113158510711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2051492417/10000000000 : ℝ)|^4281 ≤ (12467657595991/100000000000000 : ℝ)^3257
        have hw : |(-2051492417/10000000000 : ℝ)|=(2051492417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274281469/500000000 : ℝ)|^4281 ≤ (5677397985421/12500000000000 : ℝ)^3257
        have hw : |(274281469/500000000 : ℝ)|=(274281469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589558607/5000000000 : ℝ)|^4281 ≤ (42113158510711/100000000000000 : ℝ)^3257
        have hw : |(2589558607/5000000000 : ℝ)|=(2589558607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s2_1 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367449189/10000000000 : ℝ)*x 0 + (-1105028803/5000000000 : ℝ)*x 1 + (2589558371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367449189/10000000000 : ℝ)^4281 ≤ (44137430749729/100000000000000 : ℝ)^3257 := by
    have hnat : (5367449189 : ℕ)^4281*100000000000000^3257 ≤ 44137430749729^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367449189 10000000000 44137430749729 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105028803/5000000000 : ℝ)^4281 ≤ (13749415769831/100000000000000 : ℝ)^3257 := by
    have hnat : (1105028803 : ℕ)^4281*100000000000000^3257 ≤ 13749415769831^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105028803 5000000000 13749415769831 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589558371/5000000000 : ℝ)^4281 ≤ (8422630693211/20000000000000 : ℝ)^3257 := by
    have hnat : (2589558371 : ℕ)^4281*20000000000000^3257 ≤ 8422630693211^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589558371 5000000000 8422630693211 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367449189/10000000000 : ℝ), (-1105028803/5000000000 : ℝ), (2589558371/5000000000 : ℝ)] ![(44137430749729/100000000000000 : ℝ), (13749415769831/100000000000000 : ℝ), (8422630693211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367449189/10000000000 : ℝ)|^4281 ≤ (44137430749729/100000000000000 : ℝ)^3257
        have hw : |(5367449189/10000000000 : ℝ)|=(5367449189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1105028803/5000000000 : ℝ)|^4281 ≤ (13749415769831/100000000000000 : ℝ)^3257
        have hw : |(-1105028803/5000000000 : ℝ)|=(1105028803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589558371/5000000000 : ℝ)|^4281 ≤ (8422630693211/20000000000000 : ℝ)^3257
        have hw : |(2589558371/5000000000 : ℝ)|=(2589558371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s2_2 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683724259/5000000000 : ℝ)*x 0 + (1294779351/2500000000 : ℝ)*x 1 + (-552514407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683724259/5000000000 : ℝ)^4281 ≤ (44137423497207/100000000000000 : ℝ)^3257 := by
    have hnat : (2683724259 : ℕ)^4281*100000000000000^3257 ≤ 44137423497207^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683724259 5000000000 44137423497207 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294779351/2500000000 : ℝ)^4281 ≤ (21056580270699/50000000000000 : ℝ)^3257 := by
    have hnat : (1294779351 : ℕ)^4281*50000000000000^3257 ≤ 21056580270699^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294779351 2500000000 21056580270699 50000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552514407/2500000000 : ℝ)^4281 ≤ (13749415949731/100000000000000 : ℝ)^3257 := by
    have hnat : (552514407 : ℕ)^4281*100000000000000^3257 ≤ 13749415949731^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552514407 2500000000 13749415949731 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683724259/5000000000 : ℝ), (1294779351/2500000000 : ℝ), (-552514407/2500000000 : ℝ)] ![(44137423497207/100000000000000 : ℝ), (21056580270699/50000000000000 : ℝ), (13749415949731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683724259/5000000000 : ℝ)|^4281 ≤ (44137423497207/100000000000000 : ℝ)^3257
        have hw : |(2683724259/5000000000 : ℝ)|=(2683724259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294779351/2500000000 : ℝ)|^4281 ≤ (21056580270699/50000000000000 : ℝ)^3257
        have hw : |(1294779351/2500000000 : ℝ)|=(1294779351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-552514407/2500000000 : ℝ)|^4281 ≤ (13749415949731/100000000000000 : ℝ)^3257
        have hw : |(-552514407/2500000000 : ℝ)|=(552514407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s2_3 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325347679/10000000000 : ℝ)*x 0 + (1004474849/2500000000 : ℝ)*x 1 + (4654850883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325347679/10000000000 : ℝ)^4281 ≤ (8308567072037/25000000000000 : ℝ)^3257 := by
    have hnat : (4325347679 : ℕ)^4281*25000000000000^3257 ≤ 8308567072037^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325347679 10000000000 8308567072037 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004474849/2500000000 : ℝ)^4281 ≤ (30164522817243/100000000000000 : ℝ)^3257 := by
    have hnat : (1004474849 : ℕ)^4281*100000000000000^3257 ≤ 30164522817243^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004474849 2500000000 30164522817243 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4654850883/10000000000 : ℝ)^4281 ≤ (36601208875121/100000000000000 : ℝ)^3257 := by
    have hnat : (4654850883 : ℕ)^4281*100000000000000^3257 ≤ 36601208875121^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4654850883 10000000000 36601208875121 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325347679/10000000000 : ℝ), (1004474849/2500000000 : ℝ), (4654850883/10000000000 : ℝ)] ![(8308567072037/25000000000000 : ℝ), (30164522817243/100000000000000 : ℝ), (36601208875121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325347679/10000000000 : ℝ)|^4281 ≤ (8308567072037/25000000000000 : ℝ)^3257
        have hw : |(4325347679/10000000000 : ℝ)|=(4325347679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004474849/2500000000 : ℝ)|^4281 ≤ (30164522817243/100000000000000 : ℝ)^3257
        have hw : |(1004474849/2500000000 : ℝ)|=(1004474849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4654850883/10000000000 : ℝ)|^4281 ≤ (36601208875121/100000000000000 : ℝ)^3257
        have hw : |(4654850883/10000000000 : ℝ)|=(4654850883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s2_4 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2051564563/10000000000 : ℝ)*x 0 + (5181084691/10000000000 : ℝ)*x 1 + (1096728793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051564563/10000000000 : ℝ)^4281 ≤ (779264619201/6250000000000 : ℝ)^3257 := by
    have hnat : (2051564563 : ℕ)^4281*6250000000000^3257 ≤ 779264619201^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051564563 10000000000 779264619201 6250000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181084691/10000000000 : ℝ)^4281 ≤ (42134187826393/100000000000000 : ℝ)^3257 := by
    have hnat : (5181084691 : ℕ)^4281*100000000000000^3257 ≤ 42134187826393^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181084691 10000000000 42134187826393 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096728793/2000000000 : ℝ)^4281 ≤ (45397578254101/100000000000000 : ℝ)^3257 := by
    have hnat : (1096728793 : ℕ)^4281*100000000000000^3257 ≤ 45397578254101^3257*2000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096728793 2000000000 45397578254101 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2051564563/10000000000 : ℝ), (5181084691/10000000000 : ℝ), (1096728793/2000000000 : ℝ)] ![(779264619201/6250000000000 : ℝ), (42134187826393/100000000000000 : ℝ), (45397578254101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2051564563/10000000000 : ℝ)|^4281 ≤ (779264619201/6250000000000 : ℝ)^3257
        have hw : |(-2051564563/10000000000 : ℝ)|=(2051564563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181084691/10000000000 : ℝ)|^4281 ≤ (42134187826393/100000000000000 : ℝ)^3257
        have hw : |(5181084691/10000000000 : ℝ)|=(5181084691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096728793/2000000000 : ℝ)|^4281 ≤ (45397578254101/100000000000000 : ℝ)^3257
        have hw : |(1096728793/2000000000 : ℝ)|=(1096728793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s2_5 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644314059/5000000000 : ℝ)*x 0 + (-476382473/2500000000 : ℝ)*x 1 + (2741822013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644314059/5000000000 : ℝ)^4281 ≤ (43287464278101/100000000000000 : ℝ)^3257 := by
    have hnat : (2644314059 : ℕ)^4281*100000000000000^3257 ≤ 43287464278101^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644314059 5000000000 43287464278101 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476382473/2500000000 : ℝ)^4281 ≤ (2262991356901/20000000000000 : ℝ)^3257 := by
    have hnat : (476382473 : ℕ)^4281*20000000000000^3257 ≤ 2262991356901^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476382473 2500000000 2262991356901 20000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741822013/5000000000 : ℝ)^4281 ≤ (11349394729469/25000000000000 : ℝ)^3257 := by
    have hnat : (2741822013 : ℕ)^4281*25000000000000^3257 ≤ 11349394729469^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741822013 5000000000 11349394729469 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644314059/5000000000 : ℝ), (-476382473/2500000000 : ℝ), (2741822013/5000000000 : ℝ)] ![(43287464278101/100000000000000 : ℝ), (2262991356901/20000000000000 : ℝ), (11349394729469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644314059/5000000000 : ℝ)|^4281 ≤ (43287464278101/100000000000000 : ℝ)^3257
        have hw : |(2644314059/5000000000 : ℝ)|=(2644314059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-476382473/2500000000 : ℝ)|^4281 ≤ (2262991356901/20000000000000 : ℝ)^3257
        have hw : |(-476382473/2500000000 : ℝ)|=(476382473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741822013/5000000000 : ℝ)|^4281 ≤ (11349394729469/25000000000000 : ℝ)^3257
        have hw : |(2741822013/5000000000 : ℝ)|=(2741822013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s2_6 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322157051/2500000000 : ℝ)*x 0 + (1370910993/2500000000 : ℝ)*x 1 + (-1905529849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322157051/2500000000 : ℝ)^4281 ≤ (43287465203321/100000000000000 : ℝ)^3257 := by
    have hnat : (1322157051 : ℕ)^4281*100000000000000^3257 ≤ 43287465203321^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322157051 2500000000 43287465203321 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370910993/2500000000 : ℝ)^4281 ≤ (1418674322821/3125000000000 : ℝ)^3257 := by
    have hnat : (1370910993 : ℕ)^4281*3125000000000^3257 ≤ 1418674322821^3257*2500000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370910993 2500000000 1418674322821 3125000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1905529849/10000000000 : ℝ)^4281 ≤ (11314956448897/100000000000000 : ℝ)^3257 := by
    have hnat : (1905529849 : ℕ)^4281*100000000000000^3257 ≤ 11314956448897^3257*10000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905529849 10000000000 11314956448897 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322157051/2500000000 : ℝ), (1370910993/2500000000 : ℝ), (-1905529849/10000000000 : ℝ)] ![(43287465203321/100000000000000 : ℝ), (1418674322821/3125000000000 : ℝ), (11314956448897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322157051/2500000000 : ℝ)|^4281 ≤ (43287465203321/100000000000000 : ℝ)^3257
        have hw : |(1322157051/2500000000 : ℝ)|=(1322157051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370910993/2500000000 : ℝ)|^4281 ≤ (1418674322821/3125000000000 : ℝ)^3257
        have hw : |(1370910993/2500000000 : ℝ)|=(1370910993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1905529849/10000000000 : ℝ)|^4281 ≤ (11314956448897/100000000000000 : ℝ)^3257
        have hw : |(-1905529849/10000000000 : ℝ)|=(1905529849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1321_s2_7 (p : ℝ) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540687003/1250000000 : ℝ)*x 0 + (290672511/625000000 : ℝ)*x 1 + (2011015359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540687003/1250000000 : ℝ)^4281 ≤ (33235766481351/100000000000000 : ℝ)^3257 := by
    have hnat : (540687003 : ℕ)^4281*100000000000000^3257 ≤ 33235766481351^3257*1250000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540687003 1250000000 33235766481351 100000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290672511/625000000 : ℝ)^4281 ≤ (18279468306609/50000000000000 : ℝ)^3257 := by
    have hnat : (290672511 : ℕ)^4281*50000000000000^3257 ≤ 18279468306609^3257*625000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290672511 625000000 18279468306609 50000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011015359/5000000000 : ℝ)^4281 ≤ (7551324222471/25000000000000 : ℝ)^3257 := by
    have hnat : (2011015359 : ℕ)^4281*25000000000000^3257 ≤ 7551324222471^3257*5000000000^4281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011015359 5000000000 7551324222471 25000000000000 4281 3257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4281/1024 : ℝ)) 4281 3257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540687003/1250000000 : ℝ), (290672511/625000000 : ℝ), (2011015359/5000000000 : ℝ)] ![(33235766481351/100000000000000 : ℝ), (18279468306609/50000000000000 : ℝ), (7551324222471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540687003/1250000000 : ℝ)|^4281 ≤ (33235766481351/100000000000000 : ℝ)^3257
        have hw : |(540687003/1250000000 : ℝ)|=(540687003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(290672511/625000000 : ℝ)|^4281 ≤ (18279468306609/50000000000000 : ℝ)^3257
        have hw : |(290672511/625000000 : ℝ)|=(290672511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2011015359/5000000000 : ℝ)|^4281 ≤ (7551324222471/25000000000000 : ℝ)^3257
        have hw : |(2011015359/5000000000 : ℝ)|=(2011015359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1321_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9618859/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1673/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9711/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1619/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1673/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1673/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1673/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1673/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1673/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1673/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1673/25000 : ℝ) ^ (535/128 : ℝ) ≤ (616823363353681/50000000000000000000 : ℝ) := by
    have hpowers : (1673/25000 : ℝ)^535 ≤ (616823363353681/50000000000000000000 : ℝ)^128 := by
      have hnat : (1673 : ℕ)^535*50000000000000000000^128 ≤ 616823363353681^128*25000^535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1673 25000 616823363353681 50000000000000000000 535 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1673/25000 : ℝ)) (X := (616823363353681/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hpowhi : (19621/100000 : ℝ) ^ (535/128 : ℝ) ≤ (22122050337606853/20000000000000000000 : ℝ) := by
    have hpowers : (19621/100000 : ℝ)^535 ≤ (22122050337606853/20000000000000000000 : ℝ)^128 := by
      have hnat : (19621 : ℕ)^535*20000000000000000000^128 ≤ 22122050337606853^128*100000^535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19621 100000 22122050337606853 20000000000000000000 535 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19621/100000 : ℝ)) (X := (22122050337606853/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000616823363353681/25000000000000000000 : ℝ) ≤ (5000029515009177/5000000000000000 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (25000616823363353681/25000000000000000000 : ℝ)^128 ≤ (5000029515009177/5000000000000000 : ℝ)^535 := by
      have hnat : (25000616823363353681 : ℕ)^128*5000000000000000^535 ≤ 5000029515009177^535*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000616823363353681 25000000000000000000 5000029515009177 5000000000000000 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000029515009177/5000000000000000 : ℝ)) (X := (25000616823363353681/25000000000000000000 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100111843898414741627/100000000000000000000 : ℝ) ≤ (2500668688439283/2500000000000000 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (100111843898414741627/100000000000000000000 : ℝ)^128 ≤ (2500668688439283/2500000000000000 : ℝ)^535 := by
      have hnat : (100111843898414741627 : ℕ)^128*2500000000000000^535 ≤ 2500668688439283^535*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100111843898414741627 100000000000000000000 2500668688439283 2500000000000000 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500668688439283/2500000000000000 : ℝ)) (X := (100111843898414741627/100000000000000000000 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10022122050337606853/10000000000000000000 : ℝ) ≤ (1000529047749591/1000000000000000 : ℝ) ^ (535/128 : ℝ) := by
    have hpowers : (10022122050337606853/10000000000000000000 : ℝ)^128 ≤ (1000529047749591/1000000000000000 : ℝ)^535 := by
      have hnat : (10022122050337606853 : ℕ)^128*1000000000000000^535 ≤ 1000529047749591^535*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10022122050337606853 10000000000000000000 1000529047749591 1000000000000000 128 535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000529047749591/1000000000000000 : ℝ)) (X := (10022122050337606853/10000000000000000000 : ℝ)) (by norm_num) 535 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(616823363353681/50000000000000000000 : ℝ) ≤ ((9232553882327678151/9235000000000000000 : ℝ)+2*(1307861869389/646450000000000 : ℝ)*(1673/25000 : ℝ))^(535/128 : ℝ) := by
    rw [show (9232553882327678151/9235000000000000000 : ℝ)+2*(1307861869389/646450000000000 : ℝ)*(1673/25000 : ℝ)=(5000029515009177/5000000000000000 : ℝ) by norm_num, show 1+2*(616823363353681/50000000000000000000 : ℝ)=(25000616823363353681/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22122050337606853/20000000000000000000 : ℝ)+(616823363353681/50000000000000000000 : ℝ) ≤ ((9232553882327678151/9235000000000000000 : ℝ)+(1307861869389/646450000000000 : ℝ)*((19621/100000 : ℝ)+(1673/25000 : ℝ)))^(535/128 : ℝ) := by
    rw [show (9232553882327678151/9235000000000000000 : ℝ)+(1307861869389/646450000000000 : ℝ)*((19621/100000 : ℝ)+(1673/25000 : ℝ))=(2500668688439283/2500000000000000 : ℝ) by norm_num, show 1+(22122050337606853/20000000000000000000 : ℝ)+(616823363353681/50000000000000000000 : ℝ)=(100111843898414741627/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22122050337606853/20000000000000000000 : ℝ) ≤ ((9232553882327678151/9235000000000000000 : ℝ)+2*(1307861869389/646450000000000 : ℝ)*(19621/100000 : ℝ))^(535/128 : ℝ) := by
    rw [show (9232553882327678151/9235000000000000000 : ℝ)+2*(1307861869389/646450000000000 : ℝ)*(19621/100000 : ℝ)=(1000529047749591/1000000000000000 : ℝ) by norm_num, show 1+2*(22122050337606853/20000000000000000000 : ℝ)=(10022122050337606853/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9232553882327678151/9235000000000000000 : ℝ)*(X 1 0+X 2 0)+(1307861869389/646450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (1673/25000 : ℝ)) (hi := (19621/100000 : ℝ)) (c := (9232553882327678151/9235000000000000000 : ℝ)) (alpha := (1307861869389/646450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9232553882327678151/9235000000000000000 : ℝ)*(X 0 1+X 2 1)+(1307861869389/646450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (1673/25000 : ℝ)) (hi := (19621/100000 : ℝ)) (c := (9232553882327678151/9235000000000000000 : ℝ)) (alpha := (1307861869389/646450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9232553882327678151/9235000000000000000 : ℝ)*(X 0 2+X 1 2)+(1307861869389/646450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (535/128 : ℝ)) (lo := (1673/25000 : ℝ)) (hi := (19621/100000 : ℝ)) (c := (9232553882327678151/9235000000000000000 : ℝ)) (alpha := (1307861869389/646450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2051492417/10000000000 : ℝ)*X 0 0+(274281469/500000000 : ℝ)*X 0 1+(2589558607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5367449189/10000000000 : ℝ)*X 1 0+(-1105028803/5000000000 : ℝ)*X 1 1+(2589558371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2683724259/5000000000 : ℝ)*X 2 0+(1294779351/2500000000 : ℝ)*X 2 1+(-552514407/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325347679/10000000000 : ℝ)*X 0 0+(1004474849/2500000000 : ℝ)*X 0 1+(4654850883/10000000000 : ℝ)*X 0 2+(4325347679/10000000000 : ℝ)*X 1 0+(1004474849/2500000000 : ℝ)*X 1 1+(4654850883/10000000000 : ℝ)*X 1 2+(4325347679/10000000000 : ℝ)*X 2 0+(1004474849/2500000000 : ℝ)*X 2 1+(4654850883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2051564563/10000000000 : ℝ)*X 0 0+(5181084691/10000000000 : ℝ)*X 0 1+(1096728793/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644314059/5000000000 : ℝ)*X 1 0+(-476382473/2500000000 : ℝ)*X 1 1+(2741822013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322157051/2500000000 : ℝ)*X 2 0+(1370910993/2500000000 : ℝ)*X 2 1+(-1905529849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540687003/1250000000 : ℝ)*X 0 0+(290672511/625000000 : ℝ)*X 0 1+(2011015359/5000000000 : ℝ)*X 0 2+(540687003/1250000000 : ℝ)*X 1 0+(290672511/625000000 : ℝ)*X 1 1+(2011015359/5000000000 : ℝ)*X 1 2+(540687003/1250000000 : ℝ)*X 2 0+(290672511/625000000 : ℝ)*X 2 1+(2011015359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1321_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6138282420932192856878278317/1616125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1784093543/100000000000000 : ℝ)*(base19) + (806187961/100000000000000 : ℝ)*(base23) + (19123153/6250000000000 : ℝ)*(lower2) + (135241631/20000000000000 : ℝ)*(upper3) + (10605611/10000000000000 : ℝ)*(upper5) + (2416265396507727/100000000000000 : ℝ)*(major0) + (2416265396507727/100000000000000 : ℝ)*(major1) + (2416265396507727/100000000000000 : ℝ)*(major2) + (815631119129087/25000000000000 : ℝ)*(sp0) + (1631261836994449/50000000000000 : ℝ)*(sp1) + (3262524651894479/100000000000000 : ℝ)*(sp2) + (39249722906511/2500000000000 : ℝ)*(sp3) + (245391523/25000000000000 : ℝ)*(sp4) + (8146033813/50000000000000 : ℝ)*(sp7) + (785002604164033/50000000000000 : ℝ)*(f.failure) + (81563136452061/2500000000000 : ℝ)*(f.sum) + (43084187601417/32322500000000000000000000000 : ℝ)*base66 + (44485935353141690561/6464500000000000000000000000000000 : ℝ)*base68 + (2172518358215690561/6464500000000000000000000000000000 : ℝ)*base70 + (40253519103772690561/6464500000000000000000000000000000 : ℝ)*base72 + (118796132205727/32322500000000000000000000000 : ℝ)*base74 + (9267829703556309439/6464500000000000000000000000000000 : ℝ)*base75 + (15920031795572690561/6464500000000000000000000000000000 : ℝ)*base78 + (22864837849149690561/6464500000000000000000000000000000 : ℝ)*base80 + (52934834849957/32322500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (576653/312500000000000000000 : ℝ)*base90 + (576653/312500000000000000000 : ℝ)*base92 + (576653/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14488342451229417801483335457/1616125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1759909699/100000000000000 : ℝ)*(base19) + (2054773841/100000000000000 : ℝ)*(base23) + (237963077/100000000000000 : ℝ)*(upper3) + (2934849/3125000000000 : ℝ)*(lower4) + (69074643/50000000000000 : ℝ)*(upper5) + (1223911208429311/50000000000000 : ℝ)*(major0) + (1223911208429311/50000000000000 : ℝ)*(major1) + (1223911208429311/50000000000000 : ℝ)*(major2) + (18948585023/100000000000000 : ℝ)*(sp1) + (5803013771/25000000000000 : ℝ)*(sp2) + (1652567336200981/50000000000000 : ℝ)*(sp4) + (82627849097681/2500000000000 : ℝ)*(sp5) + (1652554702786519/50000000000000 : ℝ)*(sp6) + (49703433202701/3125000000000 : ℝ)*(sp7) + (49703433202701/3125000000000 : ℝ)*(f.failure) + (1652567336200981/50000000000000 : ℝ)*(f.sum) + (78432380849713/32322500000000000000000000000 : ℝ)*base65 + (40003086145285187727/3232250000000000000000000000000000 : ℝ)*base67 + (52020973917028187727/3232250000000000000000000000000000 : ℝ)*base69 + (30449132874417937727/3232250000000000000000000000000000 : ℝ)*base71 + (165935683091943/32322500000000000000000000000 : ℝ)*base73 + (67864028375602187727/3232250000000000000000000000000000 : ℝ)*base75 + (21100630024264687727/3232250000000000000000000000000000 : ℝ)*base77 + (21679638248842687727/3232250000000000000000000000000000 : ℝ)*base79 + (223426189900713/32322500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16951/1220703125000000000 : ℝ)*base90 + (16951/1220703125000000000 : ℝ)*base92 + (16951/1220703125000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1321_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9618859/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1673/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1619/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1321_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1321_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9618859/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1619/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1321_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1321_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1321_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (535/128 : ℝ) ≤ p) (hpb : p ≤ (4281/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9618859/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1619/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1321_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

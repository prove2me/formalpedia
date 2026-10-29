-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1418_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:50:47.977487+00:00
-- url     : https://prove2.me/submissions/ae668825-b5e4-438e-a87e-de69187818e6

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
theorem support_rectangle_w1418_s0_0 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1765058371/10000000000 : ℝ)*x 0 + (596473359/1000000000 : ℝ)*x 1 + (603589423/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765058371/10000000000 : ℝ)^2189 ≤ (1039415698931/10000000000000 : ℝ)^1677 := by
    have hnat : (1765058371 : ℕ)^2189*10000000000000^1677 ≤ 1039415698931^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765058371 10000000000 1039415698931 10000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596473359/1000000000 : ℝ)^2189 ≤ (50942165976227/100000000000000 : ℝ)^1677 := by
    have hnat : (596473359 : ℕ)^2189*100000000000000^1677 ≤ 50942165976227^1677*1000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596473359 1000000000 50942165976227 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603589423/1250000000 : ℝ)^2189 ≤ (7732735402189/20000000000000 : ℝ)^1677 := by
    have hnat : (603589423 : ℕ)^2189*20000000000000^1677 ≤ 7732735402189^1677*1250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603589423 1250000000 7732735402189 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1765058371/10000000000 : ℝ), (596473359/1000000000 : ℝ), (603589423/1250000000 : ℝ)] ![(1039415698931/10000000000000 : ℝ), (50942165976227/100000000000000 : ℝ), (7732735402189/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1765058371/10000000000 : ℝ)|^2189 ≤ (1039415698931/10000000000000 : ℝ)^1677
        have hw : |(-1765058371/10000000000 : ℝ)|=(1765058371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596473359/1000000000 : ℝ)|^2189 ≤ (50942165976227/100000000000000 : ℝ)^1677
        have hw : |(596473359/1000000000 : ℝ)|=(596473359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603589423/1250000000 : ℝ)|^2189 ≤ (7732735402189/20000000000000 : ℝ)^1677
        have hw : |(603589423/1250000000 : ℝ)|=(603589423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s0_1 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (549332339/1000000000 : ℝ)*x 0 + (-481456403/2000000000 : ℝ)*x 1 + (19314863/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549332339/1000000000 : ℝ)^2189 ≤ (9150292824127/20000000000000 : ℝ)^1677 := by
    have hnat : (549332339 : ℕ)^2189*20000000000000^1677 ≤ 9150292824127^1677*1000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549332339 1000000000 9150292824127 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481456403/2000000000 : ℝ)^2189 ≤ (3116971005893/20000000000000 : ℝ)^1677 := by
    have hnat : (481456403 : ℕ)^2189*20000000000000^1677 ≤ 3116971005893^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481456403 2000000000 3116971005893 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19314863/40000000 : ℝ)^2189 ≤ (9665920209061/25000000000000 : ℝ)^1677 := by
    have hnat : (19314863 : ℕ)^2189*25000000000000^1677 ≤ 9665920209061^1677*40000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19314863 40000000 9665920209061 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549332339/1000000000 : ℝ), (-481456403/2000000000 : ℝ), (19314863/40000000 : ℝ)] ![(9150292824127/20000000000000 : ℝ), (3116971005893/20000000000000 : ℝ), (9665920209061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549332339/1000000000 : ℝ)|^2189 ≤ (9150292824127/20000000000000 : ℝ)^1677
        have hw : |(549332339/1000000000 : ℝ)|=(549332339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-481456403/2000000000 : ℝ)|^2189 ≤ (3116971005893/20000000000000 : ℝ)^1677
        have hw : |(-481456403/2000000000 : ℝ)|=(481456403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19314863/40000000 : ℝ)|^2189 ≤ (9665920209061/25000000000000 : ℝ)^1677
        have hw : |(19314863/40000000 : ℝ)|=(19314863/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s0_2 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2746661849/5000000000 : ℝ)*x 0 + (1207178899/2500000000 : ℝ)*x 1 + (-2407281809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2746661849/5000000000 : ℝ)^2189 ≤ (11437866867251/25000000000000 : ℝ)^1677 := by
    have hnat : (2746661849 : ℕ)^2189*25000000000000^1677 ≤ 11437866867251^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746661849 5000000000 11437866867251 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1207178899/2500000000 : ℝ)^2189 ≤ (9665919806673/25000000000000 : ℝ)^1677 := by
    have hnat : (1207178899 : ℕ)^2189*25000000000000^1677 ≤ 9665919806673^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207178899 2500000000 9665919806673 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2407281809/10000000000 : ℝ)^2189 ≤ (7792426644319/50000000000000 : ℝ)^1677 := by
    have hnat : (2407281809 : ℕ)^2189*50000000000000^1677 ≤ 7792426644319^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2407281809 10000000000 7792426644319 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2746661849/5000000000 : ℝ), (1207178899/2500000000 : ℝ), (-2407281809/10000000000 : ℝ)] ![(11437866867251/25000000000000 : ℝ), (9665919806673/25000000000000 : ℝ), (7792426644319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2746661849/5000000000 : ℝ)|^2189 ≤ (11437866867251/25000000000000 : ℝ)^1677
        have hw : |(2746661849/5000000000 : ℝ)|=(2746661849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1207178899/2500000000 : ℝ)|^2189 ≤ (9665919806673/25000000000000 : ℝ)^1677
        have hw : |(1207178899/2500000000 : ℝ)|=(1207178899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2407281809/10000000000 : ℝ)|^2189 ≤ (7792426644319/50000000000000 : ℝ)^1677
        have hw : |(-2407281809/10000000000 : ℝ)|=(2407281809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s0_3 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2083791323/5000000000 : ℝ)*x 0 + (48494447/156250000 : ℝ)*x 1 + (5551331097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083791323/5000000000 : ℝ)^2189 ≤ (15951523962917/50000000000000 : ℝ)^1677 := by
    have hnat : (2083791323 : ℕ)^2189*50000000000000^1677 ≤ 15951523962917^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083791323 5000000000 15951523962917 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48494447/156250000 : ℝ)^2189 ≤ (21713853164841/100000000000000 : ℝ)^1677 := by
    have hnat : (48494447 : ℕ)^2189*100000000000000^1677 ≤ 21713853164841^1677*156250000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48494447 156250000 21713853164841 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5551331097/10000000000 : ℝ)^2189 ≤ (46383098896593/100000000000000 : ℝ)^1677 := by
    have hnat : (5551331097 : ℕ)^2189*100000000000000^1677 ≤ 46383098896593^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5551331097 10000000000 46383098896593 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083791323/5000000000 : ℝ), (48494447/156250000 : ℝ), (5551331097/10000000000 : ℝ)] ![(15951523962917/50000000000000 : ℝ), (21713853164841/100000000000000 : ℝ), (46383098896593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083791323/5000000000 : ℝ)|^2189 ≤ (15951523962917/50000000000000 : ℝ)^1677
        have hw : |(2083791323/5000000000 : ℝ)|=(2083791323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48494447/156250000 : ℝ)|^2189 ≤ (21713853164841/100000000000000 : ℝ)^1677
        have hw : |(48494447/156250000 : ℝ)|=(48494447/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5551331097/10000000000 : ℝ)|^2189 ≤ (46383098896593/100000000000000 : ℝ)^1677
        have hw : |(5551331097/10000000000 : ℝ)|=(5551331097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s0_4 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-442282251/2500000000 : ℝ)*x 0 + (194312227/400000000 : ℝ)*x 1 + (185456391/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442282251/2500000000 : ℝ)^2189 ≤ (10425457947653/100000000000000 : ℝ)^1677 := by
    have hnat : (442282251 : ℕ)^2189*100000000000000^1677 ≤ 10425457947653^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442282251 2500000000 10425457947653 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194312227/400000000 : ℝ)^2189 ≤ (4870999668109/12500000000000 : ℝ)^1677 := by
    have hnat : (194312227 : ℕ)^2189*12500000000000^1677 ≤ 4870999668109^1677*400000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194312227 400000000 4870999668109 12500000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185456391/312500000 : ℝ)^2189 ≤ (12651636172657/25000000000000 : ℝ)^1677 := by
    have hnat : (185456391 : ℕ)^2189*25000000000000^1677 ≤ 12651636172657^1677*312500000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185456391 312500000 12651636172657 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442282251/2500000000 : ℝ), (194312227/400000000 : ℝ), (185456391/312500000 : ℝ)] ![(10425457947653/100000000000000 : ℝ), (4870999668109/12500000000000 : ℝ), (12651636172657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442282251/2500000000 : ℝ)|^2189 ≤ (10425457947653/100000000000000 : ℝ)^1677
        have hw : |(-442282251/2500000000 : ℝ)|=(442282251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194312227/400000000 : ℝ)|^2189 ≤ (4870999668109/12500000000000 : ℝ)^1677
        have hw : |(194312227/400000000 : ℝ)|=(194312227/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(185456391/312500000 : ℝ)|^2189 ≤ (12651636172657/25000000000000 : ℝ)^1677
        have hw : |(185456391/312500000 : ℝ)|=(185456391/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s0_5 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5183310167/10000000000 : ℝ)*x 0 + (-20334261/156250000 : ℝ)*x 1 + (29673023/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183310167/10000000000 : ℝ)^2189 ≤ (10602658135683/25000000000000 : ℝ)^1677 := by
    have hnat : (5183310167 : ℕ)^2189*25000000000000^1677 ≤ 10602658135683^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183310167 10000000000 10602658135683 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20334261/156250000 : ℝ)^2189 ≤ (218213180749/3125000000000 : ℝ)^1677 := by
    have hnat : (20334261 : ℕ)^2189*3125000000000^1677 ≤ 218213180749^1677*156250000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20334261 156250000 218213180749 3125000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29673023/50000000 : ℝ)^2189 ≤ (50606545670141/100000000000000 : ℝ)^1677 := by
    have hnat : (29673023 : ℕ)^2189*100000000000000^1677 ≤ 50606545670141^1677*50000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29673023 50000000 50606545670141 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183310167/10000000000 : ℝ), (-20334261/156250000 : ℝ), (29673023/50000000 : ℝ)] ![(10602658135683/25000000000000 : ℝ), (218213180749/3125000000000 : ℝ), (50606545670141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183310167/10000000000 : ℝ)|^2189 ≤ (10602658135683/25000000000000 : ℝ)^1677
        have hw : |(5183310167/10000000000 : ℝ)|=(5183310167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20334261/156250000 : ℝ)|^2189 ≤ (218213180749/3125000000000 : ℝ)^1677
        have hw : |(-20334261/156250000 : ℝ)|=(20334261/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29673023/50000000 : ℝ)|^2189 ≤ (50606545670141/100000000000000 : ℝ)^1677
        have hw : |(29673023/50000000 : ℝ)|=(29673023/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s0_6 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5183310183/10000000000 : ℝ)*x 0 + (5934604421/10000000000 : ℝ)*x 1 + (-650696481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183310183/10000000000 : ℝ)^2189 ≤ (8482126542723/20000000000000 : ℝ)^1677 := by
    have hnat : (5183310183 : ℕ)^2189*20000000000000^1677 ≤ 8482126542723^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183310183 10000000000 8482126542723 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5934604421/10000000000 : ℝ)^2189 ≤ (50606543677723/100000000000000 : ℝ)^1677 := by
    have hnat : (5934604421 : ℕ)^2189*100000000000000^1677 ≤ 50606543677723^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5934604421 10000000000 50606543677723 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650696481/5000000000 : ℝ)^2189 ≤ (1396564718191/20000000000000 : ℝ)^1677 := by
    have hnat : (650696481 : ℕ)^2189*20000000000000^1677 ≤ 1396564718191^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650696481 5000000000 1396564718191 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183310183/10000000000 : ℝ), (5934604421/10000000000 : ℝ), (-650696481/5000000000 : ℝ)] ![(8482126542723/20000000000000 : ℝ), (50606543677723/100000000000000 : ℝ), (1396564718191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183310183/10000000000 : ℝ)|^2189 ≤ (8482126542723/20000000000000 : ℝ)^1677
        have hw : |(5183310183/10000000000 : ℝ)|=(5183310183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5934604421/10000000000 : ℝ)|^2189 ≤ (50606543677723/100000000000000 : ℝ)^1677
        have hw : |(5934604421/10000000000 : ℝ)|=(5934604421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-650696481/5000000000 : ℝ)|^2189 ≤ (1396564718191/20000000000000 : ℝ)^1677
        have hw : |(-650696481/5000000000 : ℝ)|=(650696481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s0_7 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1044088799/2500000000 : ℝ)*x 0 + (2744326257/5000000000 : ℝ)*x 1 + (792140397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044088799/2500000000 : ℝ)^2189 ≤ (7997683264813/25000000000000 : ℝ)^1677 := by
    have hnat : (1044088799 : ℕ)^2189*25000000000000^1677 ≤ 7997683264813^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044088799 2500000000 7997683264813 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744326257/5000000000 : ℝ)^2189 ≤ (45700692096059/100000000000000 : ℝ)^1677 := by
    have hnat : (2744326257 : ℕ)^2189*100000000000000^1677 ≤ 45700692096059^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744326257 5000000000 45700692096059 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792140397/2500000000 : ℝ)^2189 ≤ (5577143706501/25000000000000 : ℝ)^1677 := by
    have hnat : (792140397 : ℕ)^2189*25000000000000^1677 ≤ 5577143706501^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792140397 2500000000 5577143706501 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044088799/2500000000 : ℝ), (2744326257/5000000000 : ℝ), (792140397/2500000000 : ℝ)] ![(7997683264813/25000000000000 : ℝ), (45700692096059/100000000000000 : ℝ), (5577143706501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044088799/2500000000 : ℝ)|^2189 ≤ (7997683264813/25000000000000 : ℝ)^1677
        have hw : |(1044088799/2500000000 : ℝ)|=(1044088799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744326257/5000000000 : ℝ)|^2189 ≤ (45700692096059/100000000000000 : ℝ)^1677
        have hw : |(2744326257/5000000000 : ℝ)|=(2744326257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792140397/2500000000 : ℝ)|^2189 ≤ (5577143706501/25000000000000 : ℝ)^1677
        have hw : |(792140397/2500000000 : ℝ)|=(792140397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1418_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (197/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13167/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4377/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4377 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4377*1^1024 ≤ 0^1024*1^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4377/1024 : ℝ) ≤ (1990855003228282227/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4377 ≤ (1990855003228282227/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4377*100000000000000000000^1024 ≤ 1990855003228282227^1024*5^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1990855003228282227 100000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1990855003228282227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4377 := by
      have hnat : (1 : ℕ)^1024*1^4377 ≤ 1^4377*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101990855003228282227/100000000000000000000 : ℝ) ≤ (10046225032863649/10000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (101990855003228282227/100000000000000000000 : ℝ)^1024 ≤ (10046225032863649/10000000000000000 : ℝ)^4377 := by
      have hnat : (101990855003228282227 : ℕ)^1024*10000000000000000^4377 ≤ 10046225032863649^4377*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101990855003228282227 100000000000000000000 10046225032863649 10000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046225032863649/10000000000000000 : ℝ)) (X := (101990855003228282227/100000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51990855003228282227/50000000000000000000 : ℝ) ≤ (5046225032863649/5000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (51990855003228282227/50000000000000000000 : ℝ)^1024 ≤ (5046225032863649/5000000000000000 : ℝ)^4377 := by
      have hnat : (51990855003228282227 : ℕ)^1024*5000000000000000^4377 ≤ 5046225032863649^4377*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51990855003228282227 50000000000000000000 5046225032863649 5000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046225032863649/5000000000000000 : ℝ)) (X := (51990855003228282227/50000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(46225032863649/4000000000000000 : ℝ)*(0 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46225032863649/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1990855003228282227/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(46225032863649/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4377/1024 : ℝ) := by
    rw [show (1 : ℝ)+(46225032863649/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10046225032863649/10000000000000000 : ℝ) by norm_num, show 1+(1990855003228282227/100000000000000000000 : ℝ)+(0 : ℝ)=(101990855003228282227/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1990855003228282227/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(46225032863649/4000000000000000 : ℝ)*(2/5 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46225032863649/4000000000000000 : ℝ)*(2/5 : ℝ)=(5046225032863649/5000000000000000 : ℝ) by norm_num, show 1+2*(1990855003228282227/100000000000000000000 : ℝ)=(51990855003228282227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(46225032863649/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46225032863649/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(46225032863649/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46225032863649/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(46225032863649/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46225032863649/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1765058371/10000000000 : ℝ)*X 0 0+(596473359/1000000000 : ℝ)*X 0 1+(603589423/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((549332339/1000000000 : ℝ)*X 1 0+(-481456403/2000000000 : ℝ)*X 1 1+(19314863/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2746661849/5000000000 : ℝ)*X 2 0+(1207178899/2500000000 : ℝ)*X 2 1+(-2407281809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2083791323/5000000000 : ℝ)*X 0 0+(48494447/156250000 : ℝ)*X 0 1+(5551331097/10000000000 : ℝ)*X 0 2+(2083791323/5000000000 : ℝ)*X 1 0+(48494447/156250000 : ℝ)*X 1 1+(5551331097/10000000000 : ℝ)*X 1 2+(2083791323/5000000000 : ℝ)*X 2 0+(48494447/156250000 : ℝ)*X 2 1+(5551331097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-442282251/2500000000 : ℝ)*X 0 0+(194312227/400000000 : ℝ)*X 0 1+(185456391/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5183310167/10000000000 : ℝ)*X 1 0+(-20334261/156250000 : ℝ)*X 1 1+(29673023/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183310183/10000000000 : ℝ)*X 2 0+(5934604421/10000000000 : ℝ)*X 2 1+(-650696481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1044088799/2500000000 : ℝ)*X 0 0+(2744326257/5000000000 : ℝ)*X 0 1+(792140397/2500000000 : ℝ)*X 0 2+(1044088799/2500000000 : ℝ)*X 1 0+(2744326257/5000000000 : ℝ)*X 1 1+(792140397/2500000000 : ℝ)*X 1 2+(1044088799/2500000000 : ℝ)*X 2 0+(2744326257/5000000000 : ℝ)*X 2 1+(792140397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255848108867708746084131/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (671050237/100000000000000 : ℝ)*(base19) + (664288033/100000000000000 : ℝ)*(base23) + (3277669/4000000000000 : ℝ)*(upper3) + (3082707/10000000000000 : ℝ)*(upper4) + (4063233/4000000000000 : ℝ)*(upper5) + (644412007035073/100000000000000 : ℝ)*(major0) + (644412007035073/100000000000000 : ℝ)*(major1) + (644412007035073/100000000000000 : ℝ)*(major2) + (880269807778627/100000000000000 : ℝ)*(sp0) + (880271825021401/100000000000000 : ℝ)*(sp1) + (176054366356721/20000000000000 : ℝ)*(sp2) + (204275109095227/50000000000000 : ℝ)*(sp3) + (2688293011/100000000000000 : ℝ)*(sp4) + (303631337/25000000000000 : ℝ)*(sp7) + (204275716357901/50000000000000 : ℝ)*(f.failure) + (440136248035819/50000000000000 : ℝ)*(f.sum) + (518977196438623/200000000000000000000000000000 : ℝ)*base66 + (123725066161377/400000000000000000000000000000 : ℝ)*base67 + (1501526455038623/400000000000000000000000000000 : ℝ)*base70 + (448244383038623/400000000000000000000000000000 : ℝ)*base72 + (754727608038623/200000000000000000000000000000 : ℝ)*base74 + (1948152604961377/400000000000000000000000000000 : ℝ)*base75 + (515554856961377/400000000000000000000000000000 : ℝ)*base77 + (1199330976161377/400000000000000000000000000000 : ℝ)*base79 + (1208576673638623/200000000000000000000000000000 : ℝ)*base82 + (9220569/2500000000000000000000 : ℝ)*base89 + (9220569/2500000000000000000000 : ℝ)*base91 + (9220569/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (454714752723985177303191/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205274393/20000000000000 : ℝ)*(base19) + (129215589/12500000000000 : ℝ)*(base23) + (17901029/12500000000000 : ℝ)*(base32) + (81123077/50000000000000 : ℝ)*(upper3) + (36768021/50000000000000 : ℝ)*(upper5) + (339923865296351/50000000000000 : ℝ)*(major0) + (339923865296351/50000000000000 : ℝ)*(major1) + (339923865296351/50000000000000 : ℝ)*(major2) + (1189934223/50000000000000 : ℝ)*(sp1) + (490974353/20000000000000 : ℝ)*(sp2) + (464338972993099/50000000000000 : ℝ)*(sp4) + (232168634936447/25000000000000 : ℝ)*(sp5) + (464337228694861/50000000000000 : ℝ)*(sp6) + (21550861020969/5000000000000 : ℝ)*(sp7) + (107754340906903/25000000000000 : ℝ)*(f.failure) + (464338972993099/50000000000000 : ℝ)*(f.sum) + (248863608555201/100000000000000000000000000000 : ℝ)*base66 + (2036681433755201/200000000000000000000000000000 : ℝ)*base68 + (88937397044799/200000000000000000000000000000 : ℝ)*base69 + (2185737842955201/200000000000000000000000000000 : ℝ)*base72 + (332361627555201/100000000000000000000000000000 : ℝ)*base74 + (2207687387755201/200000000000000000000000000000 : ℝ)*base76 + (2145167354955201/200000000000000000000000000000 : ℝ)*base78 + (2440808284155201/200000000000000000000000000000 : ℝ)*base80 + (390335961144799/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15432507/1250000000000000000000 : ℝ)*base89 + (15432507/1250000000000000000000 : ℝ)*base91 + (15432507/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1418_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (197/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13167/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1418_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1418_s1_0 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-121186113/625000000 : ℝ)*x 0 + (2804828381/5000000000 : ℝ)*x 1 + (5072314453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121186113/625000000 : ℝ)^2189 ≤ (11750700866647/100000000000000 : ℝ)^1677 := by
    have hnat : (121186113 : ℕ)^2189*100000000000000^1677 ≤ 11750700866647^1677*625000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121186113 625000000 11750700866647 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2804828381/5000000000 : ℝ)^2189 ≤ (23510115389687/50000000000000 : ℝ)^1677 := by
    have hnat : (2804828381 : ℕ)^2189*50000000000000^1677 ≤ 23510115389687^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2804828381 5000000000 23510115389687 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5072314453/10000000000 : ℝ)^2189 ≤ (20614534165819/50000000000000 : ℝ)^1677 := by
    have hnat : (5072314453 : ℕ)^2189*50000000000000^1677 ≤ 20614534165819^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072314453 10000000000 20614534165819 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121186113/625000000 : ℝ), (2804828381/5000000000 : ℝ), (5072314453/10000000000 : ℝ)] ![(11750700866647/100000000000000 : ℝ), (23510115389687/50000000000000 : ℝ), (20614534165819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121186113/625000000 : ℝ)|^2189 ≤ (11750700866647/100000000000000 : ℝ)^1677
        have hw : |(-121186113/625000000 : ℝ)|=(121186113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2804828381/5000000000 : ℝ)|^2189 ≤ (23510115389687/50000000000000 : ℝ)^1677
        have hw : |(2804828381/5000000000 : ℝ)|=(2804828381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5072314453/10000000000 : ℝ)|^2189 ≤ (20614534165819/50000000000000 : ℝ)^1677
        have hw : |(5072314453/10000000000 : ℝ)|=(5072314453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s1_1 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5397915947/10000000000 : ℝ)*x 0 + (-444790373/2000000000 : ℝ)*x 1 + (50723117/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397915947/10000000000 : ℝ)^2189 ≤ (8943403946939/20000000000000 : ℝ)^1677 := by
    have hnat : (5397915947 : ℕ)^2189*20000000000000^1677 ≤ 8943403946939^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397915947 10000000000 8943403946939 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444790373/2000000000 : ℝ)^2189 ≤ (14053941125549/100000000000000 : ℝ)^1677 := by
    have hnat : (444790373 : ℕ)^2189*100000000000000^1677 ≤ 14053941125549^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444790373 2000000000 14053941125549 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50723117/100000000 : ℝ)^2189 ≤ (41229039122669/100000000000000 : ℝ)^1677 := by
    have hnat : (50723117 : ℕ)^2189*100000000000000^1677 ≤ 41229039122669^1677*100000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50723117 100000000 41229039122669 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397915947/10000000000 : ℝ), (-444790373/2000000000 : ℝ), (50723117/100000000 : ℝ)] ![(8943403946939/20000000000000 : ℝ), (14053941125549/100000000000000 : ℝ), (41229039122669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397915947/10000000000 : ℝ)|^2189 ≤ (8943403946939/20000000000000 : ℝ)^1677
        have hw : |(5397915947/10000000000 : ℝ)|=(5397915947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444790373/2000000000 : ℝ)|^2189 ≤ (14053941125549/100000000000000 : ℝ)^1677
        have hw : |(-444790373/2000000000 : ℝ)|=(444790373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50723117/100000000 : ℝ)|^2189 ≤ (41229039122669/100000000000000 : ℝ)^1677
        have hw : |(50723117/100000000 : ℝ)|=(50723117/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s1_2 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5397914237/10000000000 : ℝ)*x 0 + (2536157113/5000000000 : ℝ)*x 1 + (-2223950857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397914237/10000000000 : ℝ)^2189 ≤ (22358500621951/50000000000000 : ℝ)^1677 := by
    have hnat : (5397914237 : ℕ)^2189*50000000000000^1677 ≤ 22358500621951^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397914237 10000000000 22358500621951 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536157113/5000000000 : ℝ)^2189 ≤ (41229065923197/100000000000000 : ℝ)^1677 := by
    have hnat : (2536157113 : ℕ)^2189*100000000000000^1677 ≤ 41229065923197^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536157113 5000000000 41229065923197 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223950857/10000000000 : ℝ)^2189 ≤ (14053932810861/100000000000000 : ℝ)^1677 := by
    have hnat : (2223950857 : ℕ)^2189*100000000000000^1677 ≤ 14053932810861^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223950857 10000000000 14053932810861 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397914237/10000000000 : ℝ), (2536157113/5000000000 : ℝ), (-2223950857/10000000000 : ℝ)] ![(22358500621951/50000000000000 : ℝ), (41229065923197/100000000000000 : ℝ), (14053932810861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397914237/10000000000 : ℝ)|^2189 ≤ (22358500621951/50000000000000 : ℝ)^1677
        have hw : |(5397914237/10000000000 : ℝ)|=(5397914237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536157113/5000000000 : ℝ)|^2189 ≤ (41229065923197/100000000000000 : ℝ)^1677
        have hw : |(2536157113/5000000000 : ℝ)|=(2536157113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223950857/10000000000 : ℝ)|^2189 ≤ (14053932810861/100000000000000 : ℝ)^1677
        have hw : |(-2223950857/10000000000 : ℝ)|=(2223950857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s1_3 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2139319771/5000000000 : ℝ)*x 0 + (746974067/2000000000 : ℝ)*x 1 + (4892646179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139319771/5000000000 : ℝ)^2189 ≤ (33017236045189/100000000000000 : ℝ)^1677 := by
    have hnat : (2139319771 : ℕ)^2189*100000000000000^1677 ≤ 33017236045189^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139319771 5000000000 33017236045189 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746974067/2000000000 : ℝ)^2189 ≤ (3456194905177/12500000000000 : ℝ)^1677 := by
    have hnat : (746974067 : ℕ)^2189*12500000000000^1677 ≤ 3456194905177^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746974067 2000000000 3456194905177 12500000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4892646179/10000000000 : ℝ)^2189 ≤ (393332046987/1000000000000 : ℝ)^1677 := by
    have hnat : (4892646179 : ℕ)^2189*1000000000000^1677 ≤ 393332046987^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4892646179 10000000000 393332046987 1000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139319771/5000000000 : ℝ), (746974067/2000000000 : ℝ), (4892646179/10000000000 : ℝ)] ![(33017236045189/100000000000000 : ℝ), (3456194905177/12500000000000 : ℝ), (393332046987/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139319771/5000000000 : ℝ)|^2189 ≤ (33017236045189/100000000000000 : ℝ)^1677
        have hw : |(2139319771/5000000000 : ℝ)|=(2139319771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746974067/2000000000 : ℝ)|^2189 ≤ (3456194905177/12500000000000 : ℝ)^1677
        have hw : |(746974067/2000000000 : ℝ)|=(746974067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4892646179/10000000000 : ℝ)|^2189 ≤ (393332046987/1000000000000 : ℝ)^1677
        have hw : |(4892646179/10000000000 : ℝ)|=(4892646179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s1_4 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-969695219/5000000000 : ℝ)*x 0 + (1015733597/2000000000 : ℝ)*x 1 + (5603194921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (969695219/5000000000 : ℝ)^2189 ≤ (2938491270003/25000000000000 : ℝ)^1677 := by
    have hnat : (969695219 : ℕ)^2189*25000000000000^1677 ≤ 2938491270003^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969695219 5000000000 2938491270003 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015733597/2000000000 : ℝ)^2189 ≤ (5162061420531/12500000000000 : ℝ)^1677 := by
    have hnat : (1015733597 : ℕ)^2189*12500000000000^1677 ≤ 5162061420531^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015733597 2000000000 5162061420531 12500000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5603194921/10000000000 : ℝ)^2189 ≤ (23474771768543/50000000000000 : ℝ)^1677 := by
    have hnat : (5603194921 : ℕ)^2189*50000000000000^1677 ≤ 23474771768543^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603194921 10000000000 23474771768543 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-969695219/5000000000 : ℝ), (1015733597/2000000000 : ℝ), (5603194921/10000000000 : ℝ)] ![(2938491270003/25000000000000 : ℝ), (5162061420531/12500000000000 : ℝ), (23474771768543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-969695219/5000000000 : ℝ)|^2189 ≤ (2938491270003/25000000000000 : ℝ)^1677
        have hw : |(-969695219/5000000000 : ℝ)|=(969695219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015733597/2000000000 : ℝ)|^2189 ≤ (5162061420531/12500000000000 : ℝ)^1677
        have hw : |(1015733597/2000000000 : ℝ)|=(1015733597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5603194921/10000000000 : ℝ)|^2189 ≤ (23474771768543/50000000000000 : ℝ)^1677
        have hw : |(5603194921/10000000000 : ℝ)|=(5603194921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s1_5 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1051527361/2000000000 : ℝ)*x 0 + (-1693068473/10000000000 : ℝ)*x 1 + (5603194929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051527361/2000000000 : ℝ)^2189 ≤ (21603094712841/50000000000000 : ℝ)^1677 := by
    have hnat : (1051527361 : ℕ)^2189*50000000000000^1677 ≤ 21603094712841^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051527361 2000000000 21603094712841 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1693068473/10000000000 : ℝ)^2189 ≤ (9844266928649/100000000000000 : ℝ)^1677 := by
    have hnat : (1693068473 : ℕ)^2189*100000000000000^1677 ≤ 9844266928649^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693068473 10000000000 9844266928649 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5603194929/10000000000 : ℝ)^2189 ≤ (5868692953073/12500000000000 : ℝ)^1677 := by
    have hnat : (5603194929 : ℕ)^2189*12500000000000^1677 ≤ 5868692953073^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603194929 10000000000 5868692953073 12500000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051527361/2000000000 : ℝ), (-1693068473/10000000000 : ℝ), (5603194929/10000000000 : ℝ)] ![(21603094712841/50000000000000 : ℝ), (9844266928649/100000000000000 : ℝ), (5868692953073/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051527361/2000000000 : ℝ)|^2189 ≤ (21603094712841/50000000000000 : ℝ)^1677
        have hw : |(1051527361/2000000000 : ℝ)|=(1051527361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1693068473/10000000000 : ℝ)|^2189 ≤ (9844266928649/100000000000000 : ℝ)^1677
        have hw : |(-1693068473/10000000000 : ℝ)|=(1693068473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5603194929/10000000000 : ℝ)|^2189 ≤ (5868692953073/12500000000000 : ℝ)^1677
        have hw : |(5603194929/10000000000 : ℝ)|=(5603194929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s1_6 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5257636781/10000000000 : ℝ)*x 0 + (1120638979/2000000000 : ℝ)*x 1 + (-846534279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257636781/10000000000 : ℝ)^2189 ≤ (540077364603/1250000000000 : ℝ)^1677 := by
    have hnat : (5257636781 : ℕ)^2189*1250000000000^1677 ≤ 540077364603^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257636781 10000000000 540077364603 1250000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120638979/2000000000 : ℝ)^2189 ≤ (46949543252717/100000000000000 : ℝ)^1677 := by
    have hnat : (1120638979 : ℕ)^2189*100000000000000^1677 ≤ 46949543252717^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120638979 2000000000 46949543252717 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846534279/5000000000 : ℝ)^2189 ≤ (9844267573769/100000000000000 : ℝ)^1677 := by
    have hnat : (846534279 : ℕ)^2189*100000000000000^1677 ≤ 9844267573769^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846534279 5000000000 9844267573769 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257636781/10000000000 : ℝ), (1120638979/2000000000 : ℝ), (-846534279/5000000000 : ℝ)] ![(540077364603/1250000000000 : ℝ), (46949543252717/100000000000000 : ℝ), (9844267573769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257636781/10000000000 : ℝ)|^2189 ≤ (540077364603/1250000000000 : ℝ)^1677
        have hw : |(5257636781/10000000000 : ℝ)|=(5257636781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120638979/2000000000 : ℝ)|^2189 ≤ (46949543252717/100000000000000 : ℝ)^1677
        have hw : |(1120638979/2000000000 : ℝ)|=(1120638979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-846534279/5000000000 : ℝ)|^2189 ≤ (9844267573769/100000000000000 : ℝ)^1677
        have hw : |(-846534279/5000000000 : ℝ)|=(846534279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s1_7 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (133735253/312500000 : ℝ)*x 0 + (2439477087/5000000000 : ℝ)*x 1 + (1874399209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133735253/312500000 : ℝ)^2189 ≤ (33026186504167/100000000000000 : ℝ)^1677 := by
    have hnat : (133735253 : ℕ)^2189*100000000000000^1677 ≤ 33026186504167^1677*312500000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133735253 312500000 33026186504167 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2439477087/5000000000 : ℝ)^2189 ≤ (3918958646539/10000000000000 : ℝ)^1677 := by
    have hnat : (2439477087 : ℕ)^2189*10000000000000^1677 ≤ 3918958646539^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439477087 5000000000 3918958646539 10000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1874399209/5000000000 : ℝ)^2189 ≤ (6946056753653/25000000000000 : ℝ)^1677 := by
    have hnat : (1874399209 : ℕ)^2189*25000000000000^1677 ≤ 6946056753653^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874399209 5000000000 6946056753653 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133735253/312500000 : ℝ), (2439477087/5000000000 : ℝ), (1874399209/5000000000 : ℝ)] ![(33026186504167/100000000000000 : ℝ), (3918958646539/10000000000000 : ℝ), (6946056753653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133735253/312500000 : ℝ)|^2189 ≤ (33026186504167/100000000000000 : ℝ)^1677
        have hw : |(133735253/312500000 : ℝ)|=(133735253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2439477087/5000000000 : ℝ)|^2189 ≤ (3918958646539/10000000000000 : ℝ)^1677
        have hw : |(2439477087/5000000000 : ℝ)|=(2439477087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1874399209/5000000000 : ℝ)|^2189 ≤ (6946056753653/25000000000000 : ℝ)^1677
        have hw : |(1874399209/5000000000 : ℝ)|=(1874399209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1418_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13167/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (197/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (189/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (473/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13167/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (197/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13167/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (197/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13167/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (197/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13167/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (197/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13167/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (197/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13167/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (197/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (197/10000 : ℝ) ^ (4377/1024 : ℝ) ≤ (5126753694247/100000000000000000000 : ℝ) := by
    have hpowers : (197/10000 : ℝ)^4377 ≤ (5126753694247/100000000000000000000 : ℝ)^1024 := by
      have hnat : (197 : ℕ)^4377*100000000000000000000^1024 ≤ 5126753694247^1024*10000^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        197 10000 5126753694247 100000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (197/10000 : ℝ)) (X := (5126753694247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13167/50000 : ℝ) ^ (4377/1024 : ℝ) ≤ (333464029993938753/100000000000000000000 : ℝ) := by
    have hpowers : (13167/50000 : ℝ)^4377 ≤ (333464029993938753/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13167 : ℕ)^4377*100000000000000000000^1024 ≤ 333464029993938753^1024*50000^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13167 50000 333464029993938753 100000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13167/50000 : ℝ)) (X := (333464029993938753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000005126753694247/50000000000000000000 : ℝ) ≤ (2500000059970249/2500000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (50000005126753694247/50000000000000000000 : ℝ)^1024 ≤ (2500000059970249/2500000000000000 : ℝ)^4377 := by
      have hnat : (50000005126753694247 : ℕ)^1024*2500000000000000^4377 ≤ 2500000059970249^4377*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000005126753694247 50000000000000000000 2500000059970249 2500000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000059970249/2500000000000000 : ℝ)) (X := (50000005126753694247/50000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100333469156747633/100000000000000000 : ℝ) ≤ (5003895786135447/5000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (100333469156747633/100000000000000000 : ℝ)^1024 ≤ (5003895786135447/5000000000000000 : ℝ)^4377 := by
      have hnat : (100333469156747633 : ℕ)^1024*5000000000000000^4377 ≤ 5003895786135447^4377*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100333469156747633 100000000000000000 5003895786135447 5000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003895786135447/5000000000000000 : ℝ)) (X := (100333469156747633/100000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50333464029993938753/50000000000000000000 : ℝ) ≤ (1251947863082599/1250000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (50333464029993938753/50000000000000000000 : ℝ)^1024 ≤ (1251947863082599/1250000000000000 : ℝ)^4377 := by
      have hnat : (50333464029993938753 : ℕ)^1024*1250000000000000^4377 ≤ 1251947863082599^4377*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50333464029993938753 50000000000000000000 1251947863082599 1250000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251947863082599/1250000000000000 : ℝ)) (X := (50333464029993938753/50000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5126753694247/100000000000000000000 : ℝ) ≤ ((30451163499355548553/30455000000000000000 : ℝ)+2*(3895666194949/1218200000000000 : ℝ)*(197/10000 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (30451163499355548553/30455000000000000000 : ℝ)+2*(3895666194949/1218200000000000 : ℝ)*(197/10000 : ℝ)=(2500000059970249/2500000000000000 : ℝ) by norm_num, show 1+2*(5126753694247/100000000000000000000 : ℝ)=(50000005126753694247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(333464029993938753/100000000000000000000 : ℝ)+(5126753694247/100000000000000000000 : ℝ) ≤ ((30451163499355548553/30455000000000000000 : ℝ)+(3895666194949/1218200000000000 : ℝ)*((13167/50000 : ℝ)+(197/10000 : ℝ)))^(4377/1024 : ℝ) := by
    rw [show (30451163499355548553/30455000000000000000 : ℝ)+(3895666194949/1218200000000000 : ℝ)*((13167/50000 : ℝ)+(197/10000 : ℝ))=(5003895786135447/5000000000000000 : ℝ) by norm_num, show 1+(333464029993938753/100000000000000000000 : ℝ)+(5126753694247/100000000000000000000 : ℝ)=(100333469156747633/100000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(333464029993938753/100000000000000000000 : ℝ) ≤ ((30451163499355548553/30455000000000000000 : ℝ)+2*(3895666194949/1218200000000000 : ℝ)*(13167/50000 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (30451163499355548553/30455000000000000000 : ℝ)+2*(3895666194949/1218200000000000 : ℝ)*(13167/50000 : ℝ)=(1251947863082599/1250000000000000 : ℝ) by norm_num, show 1+2*(333464029993938753/100000000000000000000 : ℝ)=(50333464029993938753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30451163499355548553/30455000000000000000 : ℝ)*(X 1 0+X 2 0)+(3895666194949/1218200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (197/10000 : ℝ)) (hi := (13167/50000 : ℝ)) (c := (30451163499355548553/30455000000000000000 : ℝ)) (alpha := (3895666194949/1218200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30451163499355548553/30455000000000000000 : ℝ)*(X 0 1+X 2 1)+(3895666194949/1218200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (197/10000 : ℝ)) (hi := (13167/50000 : ℝ)) (c := (30451163499355548553/30455000000000000000 : ℝ)) (alpha := (3895666194949/1218200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30451163499355548553/30455000000000000000 : ℝ)*(X 0 2+X 1 2)+(3895666194949/1218200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (197/10000 : ℝ)) (hi := (13167/50000 : ℝ)) (c := (30451163499355548553/30455000000000000000 : ℝ)) (alpha := (3895666194949/1218200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-121186113/625000000 : ℝ)*X 0 0+(2804828381/5000000000 : ℝ)*X 0 1+(5072314453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5397915947/10000000000 : ℝ)*X 1 0+(-444790373/2000000000 : ℝ)*X 1 1+(50723117/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5397914237/10000000000 : ℝ)*X 2 0+(2536157113/5000000000 : ℝ)*X 2 1+(-2223950857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2139319771/5000000000 : ℝ)*X 0 0+(746974067/2000000000 : ℝ)*X 0 1+(4892646179/10000000000 : ℝ)*X 0 2+(2139319771/5000000000 : ℝ)*X 1 0+(746974067/2000000000 : ℝ)*X 1 1+(4892646179/10000000000 : ℝ)*X 1 2+(2139319771/5000000000 : ℝ)*X 2 0+(746974067/2000000000 : ℝ)*X 2 1+(4892646179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-969695219/5000000000 : ℝ)*X 0 0+(1015733597/2000000000 : ℝ)*X 0 1+(5603194921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051527361/2000000000 : ℝ)*X 1 0+(-1693068473/10000000000 : ℝ)*X 1 1+(5603194929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257636781/10000000000 : ℝ)*X 2 0+(1120638979/2000000000 : ℝ)*X 2 1+(-846534279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((133735253/312500000 : ℝ)*X 0 0+(2439477087/5000000000 : ℝ)*X 0 1+(1874399209/5000000000 : ℝ)*X 0 2+(133735253/312500000 : ℝ)*X 1 0+(2439477087/5000000000 : ℝ)*X 1 1+(1874399209/5000000000 : ℝ)*X 1 2+(133735253/312500000 : ℝ)*X 2 0+(2439477087/5000000000 : ℝ)*X 2 1+(1874399209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13566400656036699352618906923/1522750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76393017/50000000000000 : ℝ)*(base1) + (17070293/781250000000 : ℝ)*(base19) + (319089541/20000000000000 : ℝ)*(base23) + (48035951/25000000000000 : ℝ)*(upper3) + (102517717/20000000000000 : ℝ)*(upper5) + (1362377284942097/100000000000000 : ℝ)*(major0) + (1362377284942097/100000000000000 : ℝ)*(major1) + (1362377284942097/100000000000000 : ℝ)*(major2) + (930506947366839/50000000000000 : ℝ)*(sp0) + (465254277112887/25000000000000 : ℝ)*(sp1) + (465254424500337/25000000000000 : ℝ)*(sp2) + (172746206722237/20000000000000 : ℝ)*(sp3) + (5551501409/100000000000000 : ℝ)*(sp4) + (758613283/20000000000000 : ℝ)*(sp7) + (431867489731817/50000000000000 : ℝ)*(f.failure) + (465254823362263/25000000000000 : ℝ)*(f.sum) + (86343418617013/60910000000000000000000000000 : ℝ)*base65 + (19677131305234539359/3045500000000000000000000000000000 : ℝ)*base68 + (8404965170914460641/3045500000000000000000000000000000 : ℝ)*base69 + (4461583004524539359/3045500000000000000000000000000000 : ℝ)*base72 + (20663148842097/60910000000000000000000000000 : ℝ)*base74 + (3942942890060960641/3045500000000000000000000000000000 : ℝ)*base75 + (14780819740684539359/3045500000000000000000000000000000 : ℝ)*base78 + (24778511755423039359/3045500000000000000000000000000000 : ℝ)*base80 + (427411387530463/60910000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6927173/2500000000000000000000 : ℝ)*base89 + (6927173/2500000000000000000000 : ℝ)*base91 + (6927173/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (671270068030985145257301267/95171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12546159/20000000000000 : ℝ)*(base1) + (727296593/50000000000000 : ℝ)*(base19) + (72033569/5000000000000 : ℝ)*(base23) + (42015453/25000000000000 : ℝ)*(upper3) + (30787949/20000000000000 : ℝ)*(upper5) + (87228551084063/6250000000000 : ℝ)*(major0) + (87228551084063/6250000000000 : ℝ)*(major1) + (87228551084063/6250000000000 : ℝ)*(major2) + (2061989951/25000000000000 : ℝ)*(sp1) + (8052444243/100000000000000 : ℝ)*(sp2) + (1906479557790531/100000000000000 : ℝ)*(sp4) + (953234896253373/50000000000000 : ℝ)*(sp5) + (1906470001944113/100000000000000 : ℝ)*(sp6) + (884833841791479/100000000000000 : ℝ)*(sp7) + (442416952261137/50000000000000 : ℝ)*(f.failure) + (381295899011947/20000000000000 : ℝ)*(f.sum) + (804354043717/15227500000000000000000000000 : ℝ)*base66 + (587627526114032911/190343750000000000000000000000000 : ℝ)*base68 + (1306399399443092089/190343750000000000000000000000000 : ℝ)*base69 + (26330745001876661/190343750000000000000000000000000 : ℝ)*base72 + (9050472880111/7613750000000000000000000000 : ℝ)*base74 + (38056520346064161/190343750000000000000000000000000 : ℝ)*base76 + (973615986052310839/190343750000000000000000000000000 : ℝ)*base77 + (1492094204977720411/190343750000000000000000000000000 : ℝ)*base80 + (63033140685061/30455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (20021747/2500000000000000000000 : ℝ)*base90 + (20021747/2500000000000000000000 : ℝ)*base92 + (20021747/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1418_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13167/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (197/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (189/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (473/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1418_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1418_s2_0 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-246617043/1250000000 : ℝ)*x 0 + (1365167553/2500000000 : ℝ)*x 1 + (2599727819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246617043/1250000000 : ℝ)^2189 ≤ (12020044970433/100000000000000 : ℝ)^1677 := by
    have hnat : (246617043 : ℕ)^2189*100000000000000^1677 ≤ 12020044970433^1677*1250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246617043 1250000000 12020044970433 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365167553/2500000000 : ℝ)^2189 ≤ (45396803324709/100000000000000 : ℝ)^1677 := by
    have hnat : (1365167553 : ℕ)^2189*100000000000000^1677 ≤ 45396803324709^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365167553 2500000000 45396803324709 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599727819/5000000000 : ℝ)^2189 ≤ (42583151680669/100000000000000 : ℝ)^1677 := by
    have hnat : (2599727819 : ℕ)^2189*100000000000000^1677 ≤ 42583151680669^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599727819 5000000000 42583151680669 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246617043/1250000000 : ℝ), (1365167553/2500000000 : ℝ), (2599727819/5000000000 : ℝ)] ![(12020044970433/100000000000000 : ℝ), (45396803324709/100000000000000 : ℝ), (42583151680669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246617043/1250000000 : ℝ)|^2189 ≤ (12020044970433/100000000000000 : ℝ)^1677
        have hw : |(-246617043/1250000000 : ℝ)|=(246617043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365167553/2500000000 : ℝ)|^2189 ≤ (45396803324709/100000000000000 : ℝ)^1677
        have hw : |(1365167553/2500000000 : ℝ)|=(1365167553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599727819/5000000000 : ℝ)|^2189 ≤ (42583151680669/100000000000000 : ℝ)^1677
        have hw : |(2599727819/5000000000 : ℝ)|=(2599727819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s2_1 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2680421237/5000000000 : ℝ)*x 0 + (-2107396193/10000000000 : ℝ)*x 1 + (259972779/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680421237/5000000000 : ℝ)^2189 ≤ (44316553036941/100000000000000 : ℝ)^1677 := by
    have hnat : (2680421237 : ℕ)^2189*100000000000000^1677 ≤ 44316553036941^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680421237 5000000000 44316553036941 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107396193/10000000000 : ℝ)^2189 ≤ (6550147939919/50000000000000 : ℝ)^1677 := by
    have hnat : (2107396193 : ℕ)^2189*50000000000000^1677 ≤ 6550147939919^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107396193 10000000000 6550147939919 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259972779/500000000 : ℝ)^2189 ≤ (10645787765157/25000000000000 : ℝ)^1677 := by
    have hnat : (259972779 : ℕ)^2189*25000000000000^1677 ≤ 10645787765157^1677*500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259972779 500000000 10645787765157 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680421237/5000000000 : ℝ), (-2107396193/10000000000 : ℝ), (259972779/500000000 : ℝ)] ![(44316553036941/100000000000000 : ℝ), (6550147939919/50000000000000 : ℝ), (10645787765157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680421237/5000000000 : ℝ)|^2189 ≤ (44316553036941/100000000000000 : ℝ)^1677
        have hw : |(2680421237/5000000000 : ℝ)|=(2680421237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107396193/10000000000 : ℝ)|^2189 ≤ (6550147939919/50000000000000 : ℝ)^1677
        have hw : |(-2107396193/10000000000 : ℝ)|=(2107396193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259972779/500000000 : ℝ)|^2189 ≤ (10645787765157/25000000000000 : ℝ)^1677
        have hw : |(259972779/500000000 : ℝ)|=(259972779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s2_2 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5360842159/10000000000 : ℝ)*x 0 + (5199455937/10000000000 : ℝ)*x 1 + (-131712259/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360842159/10000000000 : ℝ)^2189 ≤ (22158274818951/50000000000000 : ℝ)^1677 := by
    have hnat : (5360842159 : ℕ)^2189*50000000000000^1677 ≤ 22158274818951^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360842159 10000000000 22158274818951 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5199455937/10000000000 : ℝ)^2189 ≤ (42583154877089/100000000000000 : ℝ)^1677 := by
    have hnat : (5199455937 : ℕ)^2189*100000000000000^1677 ≤ 42583154877089^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199455937 10000000000 42583154877089 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131712259/625000000 : ℝ)^2189 ≤ (20469211691/156250000000 : ℝ)^1677 := by
    have hnat : (131712259 : ℕ)^2189*156250000000^1677 ≤ 20469211691^1677*625000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131712259 625000000 20469211691 156250000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360842159/10000000000 : ℝ), (5199455937/10000000000 : ℝ), (-131712259/625000000 : ℝ)] ![(22158274818951/50000000000000 : ℝ), (42583154877089/100000000000000 : ℝ), (20469211691/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360842159/10000000000 : ℝ)|^2189 ≤ (22158274818951/50000000000000 : ℝ)^1677
        have hw : |(5360842159/10000000000 : ℝ)|=(5360842159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5199455937/10000000000 : ℝ)|^2189 ≤ (42583154877089/100000000000000 : ℝ)^1677
        have hw : |(5199455937/10000000000 : ℝ)|=(5199455937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131712259/625000000 : ℝ)|^2189 ≤ (20469211691/156250000000 : ℝ)^1677
        have hw : |(-131712259/625000000 : ℝ)|=(131712259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s2_3 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4302581563/10000000000 : ℝ)*x 0 + (100736819/250000000 : ℝ)*x 1 + (459229047/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302581563/10000000000 : ℝ)^2189 ≤ (33258603582533/100000000000000 : ℝ)^1677 := by
    have hnat : (4302581563 : ℕ)^2189*100000000000000^1677 ≤ 33258603582533^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302581563 10000000000 33258603582533 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100736819/250000000 : ℝ)^2189 ≤ (30530063380371/100000000000000 : ℝ)^1677 := by
    have hnat : (100736819 : ℕ)^2189*100000000000000^1677 ≤ 30530063380371^1677*250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100736819 250000000 30530063380371 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459229047/1000000000 : ℝ)^2189 ≤ (3621133301929/10000000000000 : ℝ)^1677 := by
    have hnat : (459229047 : ℕ)^2189*10000000000000^1677 ≤ 3621133301929^1677*1000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459229047 1000000000 3621133301929 10000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302581563/10000000000 : ℝ), (100736819/250000000 : ℝ), (459229047/1000000000 : ℝ)] ![(33258603582533/100000000000000 : ℝ), (30530063380371/100000000000000 : ℝ), (3621133301929/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302581563/10000000000 : ℝ)|^2189 ≤ (33258603582533/100000000000000 : ℝ)^1677
        have hw : |(4302581563/10000000000 : ℝ)|=(4302581563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100736819/250000000 : ℝ)|^2189 ≤ (30530063380371/100000000000000 : ℝ)^1677
        have hw : |(100736819/250000000 : ℝ)|=(100736819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(459229047/1000000000 : ℝ)|^2189 ≤ (3621133301929/10000000000000 : ℝ)^1677
        have hw : |(459229047/1000000000 : ℝ)|=(459229047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s2_4 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1972984083/10000000000 : ℝ)*x 0 + (5200966609/10000000000 : ℝ)*x 1 + (5459146569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1972984083/10000000000 : ℝ)^2189 ≤ (12020424618017/100000000000000 : ℝ)^1677 := by
    have hnat : (1972984083 : ℕ)^2189*100000000000000^1677 ≤ 12020424618017^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972984083 10000000000 12020424618017 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5200966609/10000000000 : ℝ)^2189 ≤ (2662456577001/6250000000000 : ℝ)^1677 := by
    have hnat : (5200966609 : ℕ)^2189*6250000000000^1677 ≤ 2662456577001^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200966609 10000000000 2662456577001 6250000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459146569/10000000000 : ℝ)^2189 ≤ (45380270131399/100000000000000 : ℝ)^1677 := by
    have hnat : (5459146569 : ℕ)^2189*100000000000000^1677 ≤ 45380270131399^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459146569 10000000000 45380270131399 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1972984083/10000000000 : ℝ), (5200966609/10000000000 : ℝ), (5459146569/10000000000 : ℝ)] ![(12020424618017/100000000000000 : ℝ), (2662456577001/6250000000000 : ℝ), (45380270131399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1972984083/10000000000 : ℝ)|^2189 ≤ (12020424618017/100000000000000 : ℝ)^1677
        have hw : |(-1972984083/10000000000 : ℝ)|=(1972984083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5200966609/10000000000 : ℝ)|^2189 ≤ (2662456577001/6250000000000 : ℝ)^1677
        have hw : |(5200966609/10000000000 : ℝ)|=(5200966609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459146569/10000000000 : ℝ)|^2189 ≤ (45380270131399/100000000000000 : ℝ)^1677
        have hw : |(5459146569/10000000000 : ℝ)|=(5459146569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s2_5 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1323247259/2500000000 : ℝ)*x 0 + (-1847705081/10000000000 : ℝ)*x 1 + (5459146837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323247259/2500000000 : ℝ)^2189 ≤ (10896448134713/25000000000000 : ℝ)^1677 := by
    have hnat : (1323247259 : ℕ)^2189*25000000000000^1677 ≤ 10896448134713^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323247259 2500000000 10896448134713 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847705081/10000000000 : ℝ)^2189 ≤ (5516967205879/50000000000000 : ℝ)^1677 := by
    have hnat : (1847705081 : ℕ)^2189*50000000000000^1677 ≤ 5516967205879^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847705081 10000000000 5516967205879 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459146837/10000000000 : ℝ)^2189 ≤ (5672534129921/12500000000000 : ℝ)^1677 := by
    have hnat : (5459146837 : ℕ)^2189*12500000000000^1677 ≤ 5672534129921^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459146837 10000000000 5672534129921 12500000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323247259/2500000000 : ℝ), (-1847705081/10000000000 : ℝ), (5459146837/10000000000 : ℝ)] ![(10896448134713/25000000000000 : ℝ), (5516967205879/50000000000000 : ℝ), (5672534129921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323247259/2500000000 : ℝ)|^2189 ≤ (10896448134713/25000000000000 : ℝ)^1677
        have hw : |(1323247259/2500000000 : ℝ)|=(1323247259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1847705081/10000000000 : ℝ)|^2189 ≤ (5516967205879/50000000000000 : ℝ)^1677
        have hw : |(-1847705081/10000000000 : ℝ)|=(1847705081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459146837/10000000000 : ℝ)|^2189 ≤ (5672534129921/12500000000000 : ℝ)^1677
        have hw : |(5459146837/10000000000 : ℝ)|=(5459146837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s2_6 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5292989/10000000 : ℝ)*x 0 + (5459146827/10000000000 : ℝ)*x 1 + (-230963143/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292989/10000000 : ℝ)^2189 ≤ (21792896075949/50000000000000 : ℝ)^1677 := by
    have hnat : (5292989 : ℕ)^2189*50000000000000^1677 ≤ 21792896075949^1677*10000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292989 10000000 21792896075949 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459146827/10000000000 : ℝ)^2189 ≤ (22690136465431/50000000000000 : ℝ)^1677 := by
    have hnat : (5459146827 : ℕ)^2189*50000000000000^1677 ≤ 22690136465431^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459146827 10000000000 22690136465431 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230963143/1250000000 : ℝ)^2189 ≤ (11033934902837/100000000000000 : ℝ)^1677 := by
    have hnat : (230963143 : ℕ)^2189*100000000000000^1677 ≤ 11033934902837^1677*1250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230963143 1250000000 11033934902837 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292989/10000000 : ℝ), (5459146827/10000000000 : ℝ), (-230963143/1250000000 : ℝ)] ![(21792896075949/50000000000000 : ℝ), (22690136465431/50000000000000 : ℝ), (11033934902837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292989/10000000 : ℝ)|^2189 ≤ (21792896075949/50000000000000 : ℝ)^1677
        have hw : |(5292989/10000000 : ℝ)|=(5292989/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459146827/10000000000 : ℝ)|^2189 ≤ (22690136465431/50000000000000 : ℝ)^1677
        have hw : |(5459146827/10000000000 : ℝ)|=(5459146827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-230963143/1250000000 : ℝ)|^2189 ≤ (11033934902837/100000000000000 : ℝ)^1677
        have hw : |(-230963143/1250000000 : ℝ)|=(230963143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s2_7 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4302684163/10000000000 : ℝ)*x 0 + (1147258757/2500000000 : ℝ)*x 1 + (4032755327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302684163/10000000000 : ℝ)^2189 ≤ (8314909702949/25000000000000 : ℝ)^1677 := by
    have hnat : (4302684163 : ℕ)^2189*25000000000000^1677 ≤ 8314909702949^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302684163 10000000000 8314909702949 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147258757/2500000000 : ℝ)^2189 ≤ (36177829470121/100000000000000 : ℝ)^1677 := by
    have hnat : (1147258757 : ℕ)^2189*100000000000000^1677 ≤ 36177829470121^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147258757 2500000000 36177829470121 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032755327/10000000000 : ℝ)^2189 ≤ (30562531697117/100000000000000 : ℝ)^1677 := by
    have hnat : (4032755327 : ℕ)^2189*100000000000000^1677 ≤ 30562531697117^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032755327 10000000000 30562531697117 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302684163/10000000000 : ℝ), (1147258757/2500000000 : ℝ), (4032755327/10000000000 : ℝ)] ![(8314909702949/25000000000000 : ℝ), (36177829470121/100000000000000 : ℝ), (30562531697117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302684163/10000000000 : ℝ)|^2189 ≤ (8314909702949/25000000000000 : ℝ)^1677
        have hw : |(4302684163/10000000000 : ℝ)|=(4302684163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147258757/2500000000 : ℝ)|^2189 ≤ (36177829470121/100000000000000 : ℝ)^1677
        have hw : |(1147258757/2500000000 : ℝ)|=(1147258757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032755327/10000000000 : ℝ)|^2189 ≤ (30562531697117/100000000000000 : ℝ)^1677
        have hw : |(4032755327/10000000000 : ℝ)|=(4032755327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1418_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (473/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (2577/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7917/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (473/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (189/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (473/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (189/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (473/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (189/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (473/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (189/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (473/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (189/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (473/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (189/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (189/2500 : ℝ) ^ (4377/1024 : ℝ) ≤ (8040958047201/500000000000000000 : ℝ) := by
    have hpowers : (189/2500 : ℝ)^4377 ≤ (8040958047201/500000000000000000 : ℝ)^1024 := by
      have hnat : (189 : ℕ)^4377*500000000000000000^1024 ≤ 8040958047201^1024*2500^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        189 2500 8040958047201 500000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (189/2500 : ℝ)) (X := (8040958047201/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (473/2500 : ℝ) ^ (4377/1024 : ℝ) ≤ (81144954039488213/100000000000000000000 : ℝ) := by
    have hpowers : (473/2500 : ℝ)^4377 ≤ (81144954039488213/100000000000000000000 : ℝ)^1024 := by
      have hnat : (473 : ℕ)^4377*100000000000000000000^1024 ≤ 81144954039488213^1024*2500^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        473 2500 81144954039488213 100000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (473/2500 : ℝ)) (X := (81144954039488213/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250008040958047201/250000000000000000 : ℝ) ≤ (1250009405802609/1250000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (250008040958047201/250000000000000000 : ℝ)^1024 ≤ (1250009405802609/1250000000000000 : ℝ)^4377 := by
      have hnat : (250008040958047201 : ℕ)^1024*1250000000000000^4377 ≤ 1250009405802609^4377*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250008040958047201 250000000000000000 1250009405802609 1250000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250009405802609/1250000000000000 : ℝ)) (X := (250008040958047201/250000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100082753145648928413/100000000000000000000 : ℝ) ≤ (10001935398100097/10000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (100082753145648928413/100000000000000000000 : ℝ)^1024 ≤ (10001935398100097/10000000000000000 : ℝ)^4377 := by
      have hnat : (100082753145648928413 : ℕ)^1024*10000000000000000^4377 ≤ 10001935398100097^4377*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100082753145648928413 100000000000000000000 10001935398100097 10000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001935398100097/10000000000000000 : ℝ)) (X := (100082753145648928413/100000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50081144954039488213/50000000000000000000 : ℝ) ≤ (5001897774889661/5000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (50081144954039488213/50000000000000000000 : ℝ)^1024 ≤ (5001897774889661/5000000000000000 : ℝ)^4377 := by
      have hnat : (50081144954039488213 : ℕ)^1024*5000000000000000^4377 ≤ 5001897774889661^4377*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50081144954039488213 50000000000000000000 5001897774889661 5000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001897774889661/5000000000000000 : ℝ)) (X := (50081144954039488213/50000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8040958047201/500000000000000000 : ℝ) ≤ ((1419659116324390299/1420000000000000000 : ℝ)+2*(74406067169/45440000000000 : ℝ)*(189/2500 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (1419659116324390299/1420000000000000000 : ℝ)+2*(74406067169/45440000000000 : ℝ)*(189/2500 : ℝ)=(1250009405802609/1250000000000000 : ℝ) by norm_num, show 1+2*(8040958047201/500000000000000000 : ℝ)=(250008040958047201/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(81144954039488213/100000000000000000000 : ℝ)+(8040958047201/500000000000000000 : ℝ) ≤ ((1419659116324390299/1420000000000000000 : ℝ)+(74406067169/45440000000000 : ℝ)*((473/2500 : ℝ)+(189/2500 : ℝ)))^(4377/1024 : ℝ) := by
    rw [show (1419659116324390299/1420000000000000000 : ℝ)+(74406067169/45440000000000 : ℝ)*((473/2500 : ℝ)+(189/2500 : ℝ))=(10001935398100097/10000000000000000 : ℝ) by norm_num, show 1+(81144954039488213/100000000000000000000 : ℝ)+(8040958047201/500000000000000000 : ℝ)=(100082753145648928413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(81144954039488213/100000000000000000000 : ℝ) ≤ ((1419659116324390299/1420000000000000000 : ℝ)+2*(74406067169/45440000000000 : ℝ)*(473/2500 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (1419659116324390299/1420000000000000000 : ℝ)+2*(74406067169/45440000000000 : ℝ)*(473/2500 : ℝ)=(5001897774889661/5000000000000000 : ℝ) by norm_num, show 1+2*(81144954039488213/100000000000000000000 : ℝ)=(50081144954039488213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1419659116324390299/1420000000000000000 : ℝ)*(X 1 0+X 2 0)+(74406067169/45440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (189/2500 : ℝ)) (hi := (473/2500 : ℝ)) (c := (1419659116324390299/1420000000000000000 : ℝ)) (alpha := (74406067169/45440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1419659116324390299/1420000000000000000 : ℝ)*(X 0 1+X 2 1)+(74406067169/45440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (189/2500 : ℝ)) (hi := (473/2500 : ℝ)) (c := (1419659116324390299/1420000000000000000 : ℝ)) (alpha := (74406067169/45440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1419659116324390299/1420000000000000000 : ℝ)*(X 0 2+X 1 2)+(74406067169/45440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (189/2500 : ℝ)) (hi := (473/2500 : ℝ)) (c := (1419659116324390299/1420000000000000000 : ℝ)) (alpha := (74406067169/45440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-246617043/1250000000 : ℝ)*X 0 0+(1365167553/2500000000 : ℝ)*X 0 1+(2599727819/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680421237/5000000000 : ℝ)*X 1 0+(-2107396193/10000000000 : ℝ)*X 1 1+(259972779/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360842159/10000000000 : ℝ)*X 2 0+(5199455937/10000000000 : ℝ)*X 2 1+(-131712259/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302581563/10000000000 : ℝ)*X 0 0+(100736819/250000000 : ℝ)*X 0 1+(459229047/1000000000 : ℝ)*X 0 2+(4302581563/10000000000 : ℝ)*X 1 0+(100736819/250000000 : ℝ)*X 1 1+(459229047/1000000000 : ℝ)*X 1 2+(4302581563/10000000000 : ℝ)*X 2 0+(100736819/250000000 : ℝ)*X 2 1+(459229047/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1972984083/10000000000 : ℝ)*X 0 0+(5200966609/10000000000 : ℝ)*X 0 1+(5459146569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323247259/2500000000 : ℝ)*X 1 0+(-1847705081/10000000000 : ℝ)*X 1 1+(5459146837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292989/10000000 : ℝ)*X 2 0+(5459146827/10000000000 : ℝ)*X 2 1+(-230963143/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302684163/10000000000 : ℝ)*X 0 0+(1147258757/2500000000 : ℝ)*X 0 1+(4032755327/10000000000 : ℝ)*X 0 2+(4302684163/10000000000 : ℝ)*X 1 0+(1147258757/2500000000 : ℝ)*X 1 1+(4032755327/10000000000 : ℝ)*X 1 2+(4302684163/10000000000 : ℝ)*X 2 0+(1147258757/2500000000 : ℝ)*X 2 1+(4032755327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7387616557260934377507/1136000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17192723/2000000000000 : ℝ)*(base19) + (86875311/20000000000000 : ℝ)*(base23) + (53691947/50000000000000 : ℝ)*(lower2) + (7949507/4000000000000 : ℝ)*(upper3) + (7626153/20000000000000 : ℝ)*(upper5) + (1401267804990347/50000000000000 : ℝ)*(major0) + (1401267804990347/50000000000000 : ℝ)*(major1) + (1401267804990347/50000000000000 : ℝ)*(major2) + (1914140589718577/50000000000000 : ℝ)*(sp0) + (957071925705933/25000000000000 : ℝ)*(sp1) + (29908501000651/781250000000 : ℝ)*(sp2) + (355355501292613/20000000000000 : ℝ)*(sp3) + (7383022727/100000000000000 : ℝ)*(sp4) + (4934265649/100000000000000 : ℝ)*(sp7) + (888391220364357/50000000000000 : ℝ)*(f.failure) + (1914144281229941/50000000000000 : ℝ)*(f.sum) + (6375104944197/1136000000000000000000000000 : ℝ)*base66 + (312885171783787503/71000000000000000000000000000000 : ℝ)*base67 + (240986402308787503/71000000000000000000000000000000 : ℝ)*base69 + (28109253693212497/71000000000000000000000000000000 : ℝ)*base72 + (3543059478613/1136000000000000000000000000 : ℝ)*base74 + (516411260513787503/71000000000000000000000000000000 : ℝ)*base75 + (338140138757212497/71000000000000000000000000000000 : ℝ)*base78 + (99719893311212497/71000000000000000000000000000000 : ℝ)*base80 + (352666236933/1136000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (15688433/2500000000000000000000 : ℝ)*base89 + (15688433/2500000000000000000000 : ℝ)*base91 + (15688433/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (155063568114142935695833041/17750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265244893/25000000000000 : ℝ)*(base19) + (1202315873/100000000000000 : ℝ)*(base23) + (212965187/100000000000000 : ℝ)*(upper3) + (76191389/100000000000000 : ℝ)*(lower4) + (81879851/50000000000000 : ℝ)*(upper5) + (708865262376351/25000000000000 : ℝ)*(major0) + (708865262376351/25000000000000 : ℝ)*(major1) + (708865262376351/25000000000000 : ℝ)*(major2) + (7174164471/50000000000000 : ℝ)*(sp1) + (16199666473/100000000000000 : ℝ)*(sp2) + (242079058358323/6250000000000 : ℝ)*(sp4) + (1936624762212327/50000000000000 : ℝ)*(sp5) + (3873247531750823/100000000000000 : ℝ)*(sp6) + (898828437039221/50000000000000 : ℝ)*(sp7) + (898828437039221/50000000000000 : ℝ)*(f.failure) + (242079058358323/6250000000000 : ℝ)*(f.sum) + (509252030383/568000000000000000000000000 : ℝ)*base65 + (357642689462612301/35500000000000000000000000000000 : ℝ)*base68 + (332885253511612301/35500000000000000000000000000000 : ℝ)*base70 + (87943382017612301/35500000000000000000000000000000 : ℝ)*base72 + (1250260026209/568000000000000000000000000 : ℝ)*base74 + (291620591904612301/35500000000000000000000000000000 : ℝ)*base76 + (302718600520112301/35500000000000000000000000000000 : ℝ)*base78 + (823083243067612301/35500000000000000000000000000000 : ℝ)*base80 + (769510875439/568000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (35559649/2500000000000000000000 : ℝ)*base89 + (35559649/2500000000000000000000 : ℝ)*base91 + (35559649/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1418_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (473/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7917/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1418_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1418_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7917/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1418_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1418_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1418_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7917/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1418_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

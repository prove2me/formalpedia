-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1468_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:32.691219+00:00
-- url     : https://prove2.me/submissions/9c055a71-239b-41f7-bdfd-c2e9b5dc29cd

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
theorem support_rectangle_w1468_s3_0 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1934194869/10000000000 : ℝ)*x 0 + (1361103029/2500000000 : ℝ)*x 1 + (2605121957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1934194869/10000000000 : ℝ)^4433 ≤ (1180805062437/10000000000000 : ℝ)^3409 := by
    have hnat : (1934194869 : ℕ)^4433*10000000000000^3409 ≤ 1180805062437^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934194869 10000000000 1180805062437 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361103029/2500000000 : ℝ)^4433 ≤ (45356088701373/100000000000000 : ℝ)^3409 := by
    have hnat : (1361103029 : ℕ)^4433*100000000000000^3409 ≤ 45356088701373^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361103029 2500000000 45356088701373 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605121957/5000000000 : ℝ)^4433 ≤ (21417930326891/50000000000000 : ℝ)^3409 := by
    have hnat : (2605121957 : ℕ)^4433*50000000000000^3409 ≤ 21417930326891^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605121957 5000000000 21417930326891 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1934194869/10000000000 : ℝ), (1361103029/2500000000 : ℝ), (2605121957/5000000000 : ℝ)] ![(1180805062437/10000000000000 : ℝ), (45356088701373/100000000000000 : ℝ), (21417930326891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1934194869/10000000000 : ℝ)|^4433 ≤ (1180805062437/10000000000000 : ℝ)^3409
        have hw : |(-1934194869/10000000000 : ℝ)|=(1934194869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361103029/2500000000 : ℝ)|^4433 ≤ (45356088701373/100000000000000 : ℝ)^3409
        have hw : |(1361103029/2500000000 : ℝ)|=(1361103029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605121957/5000000000 : ℝ)|^4433 ≤ (21417930326891/50000000000000 : ℝ)^3409
        have hw : |(2605121957/5000000000 : ℝ)|=(2605121957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s3_1 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355314949/10000000000 : ℝ)*x 0 + (-2054371599/10000000000 : ℝ)*x 1 + (5210243923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355314949/10000000000 : ℝ)^4433 ≤ (44393265890123/100000000000000 : ℝ)^3409 := by
    have hnat : (5355314949 : ℕ)^4433*100000000000000^3409 ≤ 44393265890123^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355314949 10000000000 44393265890123 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2054371599/10000000000 : ℝ)^4433 ≤ (6385436672307/50000000000000 : ℝ)^3409 := by
    have hnat : (2054371599 : ℕ)^4433*50000000000000^3409 ≤ 6385436672307^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054371599 10000000000 6385436672307 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5210243923/10000000000 : ℝ)^4433 ≤ (42835860750001/100000000000000 : ℝ)^3409 := by
    have hnat : (5210243923 : ℕ)^4433*100000000000000^3409 ≤ 42835860750001^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210243923 10000000000 42835860750001 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355314949/10000000000 : ℝ), (-2054371599/10000000000 : ℝ), (5210243923/10000000000 : ℝ)] ![(44393265890123/100000000000000 : ℝ), (6385436672307/50000000000000 : ℝ), (42835860750001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355314949/10000000000 : ℝ)|^4433 ≤ (44393265890123/100000000000000 : ℝ)^3409
        have hw : |(5355314949/10000000000 : ℝ)|=(5355314949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2054371599/10000000000 : ℝ)|^4433 ≤ (6385436672307/50000000000000 : ℝ)^3409
        have hw : |(-2054371599/10000000000 : ℝ)|=(2054371599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5210243923/10000000000 : ℝ)|^4433 ≤ (42835860750001/100000000000000 : ℝ)^3409
        have hw : |(5210243923/10000000000 : ℝ)|=(5210243923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s3_2 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66941437/125000000 : ℝ)*x 0 + (5210243917/10000000000 : ℝ)*x 1 + (-256796449/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66941437/125000000 : ℝ)^4433 ≤ (44393266008699/100000000000000 : ℝ)^3409 := by
    have hnat : (66941437 : ℕ)^4433*100000000000000^3409 ≤ 44393266008699^3409*125000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66941437 125000000 44393266008699 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5210243917/10000000000 : ℝ)^4433 ≤ (8567172137171/20000000000000 : ℝ)^3409 := by
    have hnat : (5210243917 : ℕ)^4433*20000000000000^3409 ≤ 8567172137171^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210243917 10000000000 8567172137171 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256796449/1250000000 : ℝ)^4433 ≤ (3192718322007/25000000000000 : ℝ)^3409 := by
    have hnat : (256796449 : ℕ)^4433*25000000000000^3409 ≤ 3192718322007^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256796449 1250000000 3192718322007 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66941437/125000000 : ℝ), (5210243917/10000000000 : ℝ), (-256796449/1250000000 : ℝ)] ![(44393266008699/100000000000000 : ℝ), (8567172137171/20000000000000 : ℝ), (3192718322007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66941437/125000000 : ℝ)|^4433 ≤ (44393266008699/100000000000000 : ℝ)^3409
        have hw : |(66941437/125000000 : ℝ)|=(66941437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5210243917/10000000000 : ℝ)|^4433 ≤ (8567172137171/20000000000000 : ℝ)^3409
        have hw : |(5210243917/10000000000 : ℝ)|=(5210243917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256796449/1250000000 : ℝ)|^4433 ≤ (3192718322007/25000000000000 : ℝ)^3409
        have hw : |(-256796449/1250000000 : ℝ)|=(256796449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s3_3 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134068531/312500000 : ℝ)*x 0 + (403970117/1000000000 : ℝ)*x 1 + (2277138301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134068531/312500000 : ℝ)^4433 ≤ (2079503916451/6250000000000 : ℝ)^3409 := by
    have hnat : (134068531 : ℕ)^4433*6250000000000^3409 ≤ 2079503916451^3409*312500000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134068531 312500000 2079503916451 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403970117/1000000000 : ℝ)^4433 ≤ (961510248547/3125000000000 : ℝ)^3409 := by
    have hnat : (403970117 : ℕ)^4433*3125000000000^3409 ≤ 961510248547^3409*1000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403970117 1000000000 961510248547 3125000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277138301/5000000000 : ℝ)^4433 ≤ (17979804685743/50000000000000 : ℝ)^3409 := by
    have hnat : (2277138301 : ℕ)^4433*50000000000000^3409 ≤ 17979804685743^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277138301 5000000000 17979804685743 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134068531/312500000 : ℝ), (403970117/1000000000 : ℝ), (2277138301/5000000000 : ℝ)] ![(2079503916451/6250000000000 : ℝ), (961510248547/3125000000000 : ℝ), (17979804685743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134068531/312500000 : ℝ)|^4433 ≤ (2079503916451/6250000000000 : ℝ)^3409
        have hw : |(134068531/312500000 : ℝ)|=(134068531/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403970117/1000000000 : ℝ)|^4433 ≤ (961510248547/3125000000000 : ℝ)^3409
        have hw : |(403970117/1000000000 : ℝ)|=(403970117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2277138301/5000000000 : ℝ)|^4433 ≤ (17979804685743/50000000000000 : ℝ)^3409
        have hw : |(2277138301/5000000000 : ℝ)|=(2277138301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s3_4 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1934230069/10000000000 : ℝ)*x 0 + (5211493489/10000000000 : ℝ)*x 1 + (1360788263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1934230069/10000000000 : ℝ)^4433 ≤ (1476041258367/12500000000000 : ℝ)^3409 := by
    have hnat : (1934230069 : ℕ)^4433*12500000000000^3409 ≤ 1476041258367^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934230069 10000000000 1476041258367 12500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5211493489/10000000000 : ℝ)^4433 ≤ (42849220397967/100000000000000 : ℝ)^3409 := by
    have hnat : (5211493489 : ℕ)^4433*100000000000000^3409 ≤ 42849220397967^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211493489 10000000000 42849220397967 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360788263/2500000000 : ℝ)^4433 ≤ (45342449527829/100000000000000 : ℝ)^3409 := by
    have hnat : (1360788263 : ℕ)^4433*100000000000000^3409 ≤ 45342449527829^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360788263 2500000000 45342449527829 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1934230069/10000000000 : ℝ), (5211493489/10000000000 : ℝ), (1360788263/2500000000 : ℝ)] ![(1476041258367/12500000000000 : ℝ), (42849220397967/100000000000000 : ℝ), (45342449527829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1934230069/10000000000 : ℝ)|^4433 ≤ (1476041258367/12500000000000 : ℝ)^3409
        have hw : |(-1934230069/10000000000 : ℝ)|=(1934230069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5211493489/10000000000 : ℝ)|^4433 ≤ (42849220397967/100000000000000 : ℝ)^3409
        have hw : |(5211493489/10000000000 : ℝ)|=(5211493489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360788263/2500000000 : ℝ)|^4433 ≤ (45342449527829/100000000000000 : ℝ)^3409
        have hw : |(1360788263/2500000000 : ℝ)|=(1360788263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s3_5 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264714183/500000000 : ℝ)*x 0 + (-910731273/5000000000 : ℝ)*x 1 + (5443153181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264714183/500000000 : ℝ)^4433 ≤ (8747300367649/20000000000000 : ℝ)^3409 := by
    have hnat : (264714183 : ℕ)^4433*20000000000000^3409 ≤ 8747300367649^3409*500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264714183 500000000 8747300367649 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910731273/5000000000 : ℝ)^4433 ≤ (10921047226367/100000000000000 : ℝ)^3409 := by
    have hnat : (910731273 : ℕ)^4433*100000000000000^3409 ≤ 10921047226367^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910731273 5000000000 10921047226367 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443153181/10000000000 : ℝ)^4433 ≤ (4534245092521/10000000000000 : ℝ)^3409 := by
    have hnat : (5443153181 : ℕ)^4433*10000000000000^3409 ≤ 4534245092521^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443153181 10000000000 4534245092521 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264714183/500000000 : ℝ), (-910731273/5000000000 : ℝ), (5443153181/10000000000 : ℝ)] ![(8747300367649/20000000000000 : ℝ), (10921047226367/100000000000000 : ℝ), (4534245092521/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264714183/500000000 : ℝ)|^4433 ≤ (8747300367649/20000000000000 : ℝ)^3409
        have hw : |(264714183/500000000 : ℝ)|=(264714183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910731273/5000000000 : ℝ)|^4433 ≤ (10921047226367/100000000000000 : ℝ)^3409
        have hw : |(-910731273/5000000000 : ℝ)|=(910731273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443153181/10000000000 : ℝ)|^4433 ≤ (4534245092521/10000000000000 : ℝ)^3409
        have hw : |(5443153181/10000000000 : ℝ)|=(5443153181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s3_6 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294283869/10000000000 : ℝ)*x 0 + (1088630623/2000000000 : ℝ)*x 1 + (-1821462349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294283869/10000000000 : ℝ)^4433 ≤ (43736504083439/100000000000000 : ℝ)^3409 := by
    have hnat : (5294283869 : ℕ)^4433*100000000000000^3409 ≤ 43736504083439^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294283869 10000000000 43736504083439 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088630623/2000000000 : ℝ)^4433 ≤ (4534245021027/10000000000000 : ℝ)^3409 := by
    have hnat : (1088630623 : ℕ)^4433*10000000000000^3409 ≤ 4534245021027^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088630623 2000000000 4534245021027 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1821462349/10000000000 : ℝ)^4433 ≤ (10921045690403/100000000000000 : ℝ)^3409 := by
    have hnat : (1821462349 : ℕ)^4433*100000000000000^3409 ≤ 10921045690403^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821462349 10000000000 10921045690403 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294283869/10000000000 : ℝ), (1088630623/2000000000 : ℝ), (-1821462349/10000000000 : ℝ)] ![(43736504083439/100000000000000 : ℝ), (4534245021027/10000000000000 : ℝ), (10921045690403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294283869/10000000000 : ℝ)|^4433 ≤ (43736504083439/100000000000000 : ℝ)^3409
        have hw : |(5294283869/10000000000 : ℝ)|=(5294283869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088630623/2000000000 : ℝ)|^4433 ≤ (4534245021027/10000000000000 : ℝ)^3409
        have hw : |(1088630623/2000000000 : ℝ)|=(1088630623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1821462349/10000000000 : ℝ)|^4433 ≤ (10921045690403/100000000000000 : ℝ)^3409
        have hw : |(-1821462349/10000000000 : ℝ)|=(1821462349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s3_7 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536283827/1250000000 : ℝ)*x 0 + (4551531121/10000000000 : ℝ)*x 1 + (1010616937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536283827/1250000000 : ℝ)^4433 ≤ (415910568741/1250000000000 : ℝ)^3409 := by
    have hnat : (536283827 : ℕ)^4433*1250000000000^3409 ≤ 415910568741^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536283827 1250000000 415910568741 1250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4551531121/10000000000 : ℝ)^4433 ≤ (4491427824423/12500000000000 : ℝ)^3409 := by
    have hnat : (4551531121 : ℕ)^4433*12500000000000^3409 ≤ 4491427824423^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551531121 10000000000 4491427824423 12500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010616937/2500000000 : ℝ)^4433 ≤ (15397865945431/50000000000000 : ℝ)^3409 := by
    have hnat : (1010616937 : ℕ)^4433*50000000000000^3409 ≤ 15397865945431^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010616937 2500000000 15397865945431 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536283827/1250000000 : ℝ), (4551531121/10000000000 : ℝ), (1010616937/2500000000 : ℝ)] ![(415910568741/1250000000000 : ℝ), (4491427824423/12500000000000 : ℝ), (15397865945431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536283827/1250000000 : ℝ)|^4433 ≤ (415910568741/1250000000000 : ℝ)^3409
        have hw : |(536283827/1250000000 : ℝ)|=(536283827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4551531121/10000000000 : ℝ)|^4433 ≤ (4491427824423/12500000000000 : ℝ)^3409
        have hw : |(4551531121/10000000000 : ℝ)|=(4551531121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010616937/2500000000 : ℝ)|^4433 ≤ (15397865945431/50000000000000 : ℝ)^3409
        have hw : |(1010616937/2500000000 : ℝ)|=(1010616937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1468_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2519/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1063/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3117/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2519/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2519/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2519/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2519/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2519/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2519/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2519/25000 : ℝ) ^ (4431/1024 : ℝ) ≤ (4864967169312977/100000000000000000000 : ℝ) := by
    have hpowers : (2519/25000 : ℝ)^4431 ≤ (4864967169312977/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2519 : ℕ)^4431*100000000000000000000^1024 ≤ 4864967169312977^1024*25000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2519 25000 4864967169312977 100000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2519/25000 : ℝ)) (X := (4864967169312977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16189/100000 : ℝ) ^ (4431/1024 : ℝ) ≤ (18929871362483891/50000000000000000000 : ℝ) := by
    have hpowers : (16189/100000 : ℝ)^4431 ≤ (18929871362483891/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16189 : ℕ)^4431*50000000000000000000^1024 ≤ 18929871362483891^1024*100000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16189 100000 18929871362483891 50000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16189/100000 : ℝ)) (X := (18929871362483891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004864967169312977/50000000000000000000 : ℝ) ≤ (1000022484947153/1000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (50004864967169312977/50000000000000000000 : ℝ)^1024 ≤ (1000022484947153/1000000000000000 : ℝ)^4431 := by
      have hnat : (50004864967169312977 : ℕ)^1024*1000000000000000^4431 ≤ 1000022484947153^4431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004864967169312977 50000000000000000000 1000022484947153 1000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000022484947153/1000000000000000 : ℝ)) (X := (50004864967169312977/50000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042724709894280759/100000000000000000000 : ℝ) ≤ (10000987201953359/10000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (100042724709894280759/100000000000000000000 : ℝ)^1024 ≤ (10000987201953359/10000000000000000 : ℝ)^4431 := by
      have hnat : (100042724709894280759 : ℕ)^1024*10000000000000000^4431 ≤ 10000987201953359^4431*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042724709894280759 100000000000000000000 10000987201953359 10000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000987201953359/10000000000000000 : ℝ)) (X := (100042724709894280759/100000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018929871362483891/25000000000000000000 : ℝ) ≤ (2500437388608797/2500000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (25018929871362483891/25000000000000000000 : ℝ)^1024 ≤ (2500437388608797/2500000000000000 : ℝ)^4431 := by
      have hnat : (25018929871362483891 : ℕ)^1024*2500000000000000^4431 ≤ 2500437388608797^4431*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018929871362483891 25000000000000000000 2500437388608797 2500000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500437388608797/2500000000000000 : ℝ)) (X := (25018929871362483891/25000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4864967169312977/100000000000000000000 : ℝ) ≤ ((30558005788802822441/30565000000000000000 : ℝ)+2*(762352481829/611300000000000 : ℝ)*(2519/25000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (30558005788802822441/30565000000000000000 : ℝ)+2*(762352481829/611300000000000 : ℝ)*(2519/25000 : ℝ)=(1000022484947153/1000000000000000 : ℝ) by norm_num, show 1+2*(4864967169312977/100000000000000000000 : ℝ)=(50004864967169312977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18929871362483891/50000000000000000000 : ℝ)+(4864967169312977/100000000000000000000 : ℝ) ≤ ((30558005788802822441/30565000000000000000 : ℝ)+(762352481829/611300000000000 : ℝ)*((16189/100000 : ℝ)+(2519/25000 : ℝ)))^(4431/1024 : ℝ) := by
    rw [show (30558005788802822441/30565000000000000000 : ℝ)+(762352481829/611300000000000 : ℝ)*((16189/100000 : ℝ)+(2519/25000 : ℝ))=(10000987201953359/10000000000000000 : ℝ) by norm_num, show 1+(18929871362483891/50000000000000000000 : ℝ)+(4864967169312977/100000000000000000000 : ℝ)=(100042724709894280759/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18929871362483891/50000000000000000000 : ℝ) ≤ ((30558005788802822441/30565000000000000000 : ℝ)+2*(762352481829/611300000000000 : ℝ)*(16189/100000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (30558005788802822441/30565000000000000000 : ℝ)+2*(762352481829/611300000000000 : ℝ)*(16189/100000 : ℝ)=(2500437388608797/2500000000000000 : ℝ) by norm_num, show 1+2*(18929871362483891/50000000000000000000 : ℝ)=(25018929871362483891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30558005788802822441/30565000000000000000 : ℝ)*(X 1 0+X 2 0)+(762352481829/611300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2519/25000 : ℝ)) (hi := (16189/100000 : ℝ)) (c := (30558005788802822441/30565000000000000000 : ℝ)) (alpha := (762352481829/611300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30558005788802822441/30565000000000000000 : ℝ)*(X 0 1+X 2 1)+(762352481829/611300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2519/25000 : ℝ)) (hi := (16189/100000 : ℝ)) (c := (30558005788802822441/30565000000000000000 : ℝ)) (alpha := (762352481829/611300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30558005788802822441/30565000000000000000 : ℝ)*(X 0 2+X 1 2)+(762352481829/611300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2519/25000 : ℝ)) (hi := (16189/100000 : ℝ)) (c := (30558005788802822441/30565000000000000000 : ℝ)) (alpha := (762352481829/611300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1934194869/10000000000 : ℝ)*X 0 0+(1361103029/2500000000 : ℝ)*X 0 1+(2605121957/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355314949/10000000000 : ℝ)*X 1 0+(-2054371599/10000000000 : ℝ)*X 1 1+(5210243923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66941437/125000000 : ℝ)*X 2 0+(5210243917/10000000000 : ℝ)*X 2 1+(-256796449/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134068531/312500000 : ℝ)*X 0 0+(403970117/1000000000 : ℝ)*X 0 1+(2277138301/5000000000 : ℝ)*X 0 2+(134068531/312500000 : ℝ)*X 1 0+(403970117/1000000000 : ℝ)*X 1 1+(2277138301/5000000000 : ℝ)*X 1 2+(134068531/312500000 : ℝ)*X 2 0+(403970117/1000000000 : ℝ)*X 2 1+(2277138301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1934230069/10000000000 : ℝ)*X 0 0+(5211493489/10000000000 : ℝ)*X 0 1+(1360788263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264714183/500000000 : ℝ)*X 1 0+(-910731273/5000000000 : ℝ)*X 1 1+(5443153181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294283869/10000000000 : ℝ)*X 2 0+(1088630623/2000000000 : ℝ)*X 2 1+(-1821462349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((536283827/1250000000 : ℝ)*X 0 0+(4551531121/10000000000 : ℝ)*X 0 1+(1010616937/2500000000 : ℝ)*X 0 2+(536283827/1250000000 : ℝ)*X 1 0+(4551531121/10000000000 : ℝ)*X 1 1+(1010616937/2500000000 : ℝ)*X 1 2+(536283827/1250000000 : ℝ)*X 2 0+(4551531121/10000000000 : ℝ)*X 2 1+(1010616937/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (902608590684023068101018963/95515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (426490923/25000000000000 : ℝ)*(base19) + (1600203667/100000000000000 : ℝ)*(base23) + (61335357/100000000000000 : ℝ)*(lower2) + (238753163/100000000000000 : ℝ)*(upper3) + (32054289/20000000000000 : ℝ)*(upper5) + (194183082202653/6250000000000 : ℝ)*(major0) + (194183082202653/6250000000000 : ℝ)*(major1) + (194183082202653/6250000000000 : ℝ)*(major2) + (21352302210667/500000000000 : ℝ)*(sp0) + (4270483733268347/100000000000000 : ℝ)*(sp1) + (4270483839028371/100000000000000 : ℝ)*(sp2) + (60730019717023/3125000000000 : ℝ)*(sp3) + (12498549319/50000000000000 : ℝ)*(sp4) + (489812521/4000000000000 : ℝ)*(sp7) + (12146080476611/625000000000 : ℝ)*(f.failure) + (2135242719616019/50000000000000 : ℝ)*(f.sum) + (26374921602729/15282500000000000000000000000 : ℝ)*base66 + (424963339580982777/191031250000000000000000000000000 : ℝ)*base68 + (258731961498889027/191031250000000000000000000000000 : ℝ)*base70 + (1039405476597982777/191031250000000000000000000000000 : ℝ)*base72 + (27264342730647/7641250000000000000000000000 : ℝ)*base74 + (1936776156157170277/191031250000000000000000000000000 : ℝ)*base76 + (916160252500735973/191031250000000000000000000000000 : ℝ)*base77 + (714781973369264027/191031250000000000000000000000000 : ℝ)*base80 + (68573191230427/7641250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (55949/62500000000000000000 : ℝ)*base90 + (55949/62500000000000000000 : ℝ)*base92 + (55949/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (190816971222967797436077/15282500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1644796319/100000000000000 : ℝ)*(base19) + (1092081293/50000000000000 : ℝ)*(base23) + (55270407/20000000000000 : ℝ)*(upper3) + (134611373/100000000000000 : ℝ)*(lower4) + (92547339/50000000000000 : ℝ)*(upper5) + (1570267258391371/50000000000000 : ℝ)*(major0) + (1570267258391371/50000000000000 : ℝ)*(major1) + (1570267258391371/50000000000000 : ℝ)*(major2) + (22705905951/100000000000000 : ℝ)*(sp1) + (32655981801/100000000000000 : ℝ)*(sp2) + (863335162192509/20000000000000 : ℝ)*(sp4) + (1079162865065069/25000000000000 : ℝ)*(sp5) + (2158320485409079/50000000000000 : ℝ)*(sp6) + (49109820160091/2500000000000 : ℝ)*(sp7) + (49109820160091/2500000000000 : ℝ)*(f.failure) + (863335162192509/20000000000000 : ℝ)*(f.sum) + (77014160553657/30565000000000000000000000000 : ℝ)*base66 + (218249427631256611/1528250000000000000000000000000000 : ℝ)*base67 + (8169229940617493389/1528250000000000000000000000000000 : ℝ)*base70 + (11554080320069243389/1528250000000000000000000000000000 : ℝ)*base72 + (193580979711443/30565000000000000000000000000 : ℝ)*base73 + (11119037289606743389/1528250000000000000000000000000000 : ℝ)*base76 + (7606377585396006611/1528250000000000000000000000000000 : ℝ)*base77 + (7784848721739756611/1528250000000000000000000000000000 : ℝ)*base79 + (21150065920743/7641250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6731/250000000000000000000 : ℝ)*base89 + (6731/250000000000000000000 : ℝ)*base91 + (6731/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1468_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2519/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1063/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3117/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1468_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1468_s4_0 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-483728737/2500000000 : ℝ)*x 0 + (2719888369/5000000000 : ℝ)*x 1 + (1303601271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483728737/2500000000 : ℝ)^4433 ≤ (11813767426171/100000000000000 : ℝ)^3409 := by
    have hnat : (483728737 : ℕ)^4433*100000000000000^3409 ≤ 11813767426171^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483728737 2500000000 11813767426171 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719888369/5000000000 : ℝ)^4433 ≤ (45305879311899/100000000000000 : ℝ)^3409 := by
    have hnat : (2719888369 : ℕ)^4433*100000000000000^3409 ≤ 45305879311899^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719888369 5000000000 45305879311899 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303601271/2500000000 : ℝ)^4433 ≤ (21440176623131/50000000000000 : ℝ)^3409 := by
    have hnat : (1303601271 : ℕ)^4433*50000000000000^3409 ≤ 21440176623131^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303601271 2500000000 21440176623131 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-483728737/2500000000 : ℝ), (2719888369/5000000000 : ℝ), (1303601271/2500000000 : ℝ)] ![(11813767426171/100000000000000 : ℝ), (45305879311899/100000000000000 : ℝ), (21440176623131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-483728737/2500000000 : ℝ)|^4433 ≤ (11813767426171/100000000000000 : ℝ)^3409
        have hw : |(-483728737/2500000000 : ℝ)|=(483728737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719888369/5000000000 : ℝ)|^4433 ≤ (45305879311899/100000000000000 : ℝ)^3409
        have hw : |(2719888369/5000000000 : ℝ)|=(2719888369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303601271/2500000000 : ℝ)|^4433 ≤ (21440176623131/50000000000000 : ℝ)^3409
        have hw : |(1303601271/2500000000 : ℝ)|=(1303601271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s4_1 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338528931/2500000000 : ℝ)*x 0 + (-2050465643/10000000000 : ℝ)*x 1 + (130360127/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338528931/2500000000 : ℝ)^4433 ≤ (8876067830849/20000000000000 : ℝ)^3409 := by
    have hnat : (1338528931 : ℕ)^4433*20000000000000^3409 ≤ 8876067830849^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338528931 2500000000 8876067830849 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050465643/10000000000 : ℝ)^4433 ≤ (2547861526607/20000000000000 : ℝ)^3409 := by
    have hnat : (2050465643 : ℕ)^4433*20000000000000^3409 ≤ 2547861526607^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050465643 10000000000 2547861526607 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130360127/250000000 : ℝ)^4433 ≤ (42880353203487/100000000000000 : ℝ)^3409 := by
    have hnat : (130360127 : ℕ)^4433*100000000000000^3409 ≤ 42880353203487^3409*250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130360127 250000000 42880353203487 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338528931/2500000000 : ℝ), (-2050465643/10000000000 : ℝ), (130360127/250000000 : ℝ)] ![(8876067830849/20000000000000 : ℝ), (2547861526607/20000000000000 : ℝ), (42880353203487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338528931/2500000000 : ℝ)|^4433 ≤ (8876067830849/20000000000000 : ℝ)^3409
        have hw : |(1338528931/2500000000 : ℝ)|=(1338528931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050465643/10000000000 : ℝ)|^4433 ≤ (2547861526607/20000000000000 : ℝ)^3409
        have hw : |(-2050465643/10000000000 : ℝ)|=(2050465643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130360127/250000000 : ℝ)|^4433 ≤ (42880353203487/100000000000000 : ℝ)^3409
        have hw : |(130360127/250000000 : ℝ)|=(130360127/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s4_2 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354115727/10000000000 : ℝ)*x 0 + (5214405083/10000000000 : ℝ)*x 1 + (-410093127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354115727/10000000000 : ℝ)^4433 ≤ (22190169593291/50000000000000 : ℝ)^3409 := by
    have hnat : (5354115727 : ℕ)^4433*50000000000000^3409 ≤ 22190169593291^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354115727 10000000000 22190169593291 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214405083/10000000000 : ℝ)^4433 ≤ (2680022077223/6250000000000 : ℝ)^3409 := by
    have hnat : (5214405083 : ℕ)^4433*6250000000000^3409 ≤ 2680022077223^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214405083 10000000000 2680022077223 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410093127/2000000000 : ℝ)^4433 ≤ (6369653784201/50000000000000 : ℝ)^3409 := by
    have hnat : (410093127 : ℕ)^4433*50000000000000^3409 ≤ 6369653784201^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410093127 2000000000 6369653784201 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354115727/10000000000 : ℝ), (5214405083/10000000000 : ℝ), (-410093127/2000000000 : ℝ)] ![(22190169593291/50000000000000 : ℝ), (2680022077223/6250000000000 : ℝ), (6369653784201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354115727/10000000000 : ℝ)|^4433 ≤ (22190169593291/50000000000000 : ℝ)^3409
        have hw : |(5354115727/10000000000 : ℝ)|=(5354115727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214405083/10000000000 : ℝ)|^4433 ≤ (2680022077223/6250000000000 : ℝ)^3409
        have hw : |(5214405083/10000000000 : ℝ)|=(5214405083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410093127/2000000000 : ℝ)|^4433 ≤ (6369653784201/50000000000000 : ℝ)^3409
        have hw : |(-410093127/2000000000 : ℝ)|=(410093127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s4_3 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4290640509/10000000000 : ℝ)*x 0 + (809862629/2000000000 : ℝ)*x 1 + (1136139661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4290640509/10000000000 : ℝ)^4433 ≤ (3327657591921/10000000000000 : ℝ)^3409 := by
    have hnat : (4290640509 : ℕ)^4433*10000000000000^3409 ≤ 3327657591921^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290640509 10000000000 3327657591921 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (809862629/2000000000 : ℝ)^4433 ≤ (7715890547503/25000000000000 : ℝ)^3409 := by
    have hnat : (809862629 : ℕ)^4433*25000000000000^3409 ≤ 7715890547503^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809862629 2000000000 7715890547503 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136139661/2500000000 : ℝ)^4433 ≤ (35859861867771/100000000000000 : ℝ)^3409 := by
    have hnat : (1136139661 : ℕ)^4433*100000000000000^3409 ≤ 35859861867771^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136139661 2500000000 35859861867771 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4290640509/10000000000 : ℝ), (809862629/2000000000 : ℝ), (1136139661/2500000000 : ℝ)] ![(3327657591921/10000000000000 : ℝ), (7715890547503/25000000000000 : ℝ), (35859861867771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4290640509/10000000000 : ℝ)|^4433 ≤ (3327657591921/10000000000000 : ℝ)^3409
        have hw : |(4290640509/10000000000 : ℝ)|=(4290640509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(809862629/2000000000 : ℝ)|^4433 ≤ (7715890547503/25000000000000 : ℝ)^3409
        have hw : |(809862629/2000000000 : ℝ)|=(809862629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136139661/2500000000 : ℝ)|^4433 ≤ (35859861867771/100000000000000 : ℝ)^3409
        have hw : |(1136139661/2500000000 : ℝ)|=(1136139661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s4_4 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-483736609/2500000000 : ℝ)*x 0 + (5215562747/10000000000 : ℝ)*x 1 + (5438610537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483736609/2500000000 : ℝ)^4433 ≤ (5907008714063/50000000000000 : ℝ)^3409 := by
    have hnat : (483736609 : ℕ)^4433*50000000000000^3409 ≤ 5907008714063^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483736609 2500000000 5907008714063 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215562747/10000000000 : ℝ)^4433 ≤ (42892733254999/100000000000000 : ℝ)^3409 := by
    have hnat : (5215562747 : ℕ)^4433*100000000000000^3409 ≤ 42892733254999^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215562747 10000000000 42892733254999 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438610537/10000000000 : ℝ)^4433 ≤ (45293249303387/100000000000000 : ℝ)^3409 := by
    have hnat : (5438610537 : ℕ)^4433*100000000000000^3409 ≤ 45293249303387^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438610537 10000000000 45293249303387 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-483736609/2500000000 : ℝ), (5215562747/10000000000 : ℝ), (5438610537/10000000000 : ℝ)] ![(5907008714063/50000000000000 : ℝ), (42892733254999/100000000000000 : ℝ), (45293249303387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-483736609/2500000000 : ℝ)|^4433 ≤ (5907008714063/50000000000000 : ℝ)^3409
        have hw : |(-483736609/2500000000 : ℝ)|=(483736609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215562747/10000000000 : ℝ)|^4433 ≤ (42892733254999/100000000000000 : ℝ)^3409
        have hw : |(5215562747/10000000000 : ℝ)|=(5215562747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438610537/10000000000 : ℝ)|^4433 ≤ (45293249303387/100000000000000 : ℝ)^3409
        have hw : |(5438610537/10000000000 : ℝ)|=(5438610537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s4_5 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529538031/1000000000 : ℝ)*x 0 + (-1826260149/10000000000 : ℝ)*x 1 + (2719305261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529538031/1000000000 : ℝ)^4433 ≤ (43748283027179/100000000000000 : ℝ)^3409 := by
    have hnat : (529538031 : ℕ)^4433*100000000000000^3409 ≤ 43748283027179^3409*1000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529538031 1000000000 43748283027179 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1826260149/10000000000 : ℝ)^4433 ≤ (10958467825883/100000000000000 : ℝ)^3409 := by
    have hnat : (1826260149 : ℕ)^4433*100000000000000^3409 ≤ 10958467825883^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826260149 10000000000 10958467825883 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719305261/5000000000 : ℝ)^4433 ≤ (22646624570471/50000000000000 : ℝ)^3409 := by
    have hnat : (2719305261 : ℕ)^4433*50000000000000^3409 ≤ 22646624570471^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719305261 5000000000 22646624570471 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529538031/1000000000 : ℝ), (-1826260149/10000000000 : ℝ), (2719305261/5000000000 : ℝ)] ![(43748283027179/100000000000000 : ℝ), (10958467825883/100000000000000 : ℝ), (22646624570471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529538031/1000000000 : ℝ)|^4433 ≤ (43748283027179/100000000000000 : ℝ)^3409
        have hw : |(529538031/1000000000 : ℝ)|=(529538031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1826260149/10000000000 : ℝ)|^4433 ≤ (10958467825883/100000000000000 : ℝ)^3409
        have hw : |(-1826260149/10000000000 : ℝ)|=(1826260149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719305261/5000000000 : ℝ)|^4433 ≤ (22646624570471/50000000000000 : ℝ)^3409
        have hw : |(2719305261/5000000000 : ℝ)|=(2719305261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s4_6 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059076057/2000000000 : ℝ)*x 0 + (5438610547/10000000000 : ℝ)*x 1 + (-1826260149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059076057/2000000000 : ℝ)^4433 ≤ (43748282758599/100000000000000 : ℝ)^3409 := by
    have hnat : (1059076057 : ℕ)^4433*100000000000000^3409 ≤ 43748282758599^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059076057 2000000000 43748282758599 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438610547/10000000000 : ℝ)^4433 ≤ (11323312352921/25000000000000 : ℝ)^3409 := by
    have hnat : (5438610547 : ℕ)^4433*25000000000000^3409 ≤ 11323312352921^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438610547 10000000000 11323312352921 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1826260149/10000000000 : ℝ)^4433 ≤ (10958467825883/100000000000000 : ℝ)^3409 := by
    have hnat : (1826260149 : ℕ)^4433*100000000000000^3409 ≤ 10958467825883^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826260149 10000000000 10958467825883 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059076057/2000000000 : ℝ), (5438610547/10000000000 : ℝ), (-1826260149/10000000000 : ℝ)] ![(43748282758599/100000000000000 : ℝ), (11323312352921/25000000000000 : ℝ), (10958467825883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059076057/2000000000 : ℝ)|^4433 ≤ (43748282758599/100000000000000 : ℝ)^3409
        have hw : |(1059076057/2000000000 : ℝ)|=(1059076057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438610547/10000000000 : ℝ)|^4433 ≤ (11323312352921/25000000000000 : ℝ)^3409
        have hw : |(5438610547/10000000000 : ℝ)|=(5438610547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1826260149/10000000000 : ℝ)|^4433 ≤ (10958467825883/100000000000000 : ℝ)^3409
        have hw : |(-1826260149/10000000000 : ℝ)|=(1826260149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s4_7 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072677433/2500000000 : ℝ)*x 0 + (4542014733/10000000000 : ℝ)*x 1 + (405187587/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072677433/2500000000 : ℝ)^4433 ≤ (33277274053071/100000000000000 : ℝ)^3409 := by
    have hnat : (1072677433 : ℕ)^4433*100000000000000^3409 ≤ 33277274053071^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072677433 2500000000 33277274053071 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542014733/10000000000 : ℝ)^4433 ≤ (2239610069717/6250000000000 : ℝ)^3409 := by
    have hnat : (4542014733 : ℕ)^4433*6250000000000^3409 ≤ 2239610069717^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542014733 10000000000 2239610069717 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405187587/1000000000 : ℝ)^4433 ≤ (15444482410363/50000000000000 : ℝ)^3409 := by
    have hnat : (405187587 : ℕ)^4433*50000000000000^3409 ≤ 15444482410363^3409*1000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405187587 1000000000 15444482410363 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072677433/2500000000 : ℝ), (4542014733/10000000000 : ℝ), (405187587/1000000000 : ℝ)] ![(33277274053071/100000000000000 : ℝ), (2239610069717/6250000000000 : ℝ), (15444482410363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072677433/2500000000 : ℝ)|^4433 ≤ (33277274053071/100000000000000 : ℝ)^3409
        have hw : |(1072677433/2500000000 : ℝ)|=(1072677433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542014733/10000000000 : ℝ)|^4433 ≤ (2239610069717/6250000000000 : ℝ)^3409
        have hw : |(4542014733/10000000000 : ℝ)|=(4542014733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(405187587/1000000000 : ℝ)|^4433 ≤ (15444482410363/50000000000000 : ℝ)^3409
        have hw : |(405187587/1000000000 : ℝ)|=(405187587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1468_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3117/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1063/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10719/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3117/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1063/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3117/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1063/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3117/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1063/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3117/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1063/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3117/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1063/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3117/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1063/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1063/10000 : ℝ) ^ (4431/1024 : ℝ) ≤ (3066443315351829/50000000000000000000 : ℝ) := by
    have hpowers : (1063/10000 : ℝ)^4431 ≤ (3066443315351829/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1063 : ℕ)^4431*50000000000000000000^1024 ≤ 3066443315351829^1024*10000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1063 10000 3066443315351829 50000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1063/10000 : ℝ)) (X := (3066443315351829/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3117/20000 : ℝ) ^ (4431/1024 : ℝ) ≤ (8029019788755887/25000000000000000000 : ℝ) := by
    have hpowers : (3117/20000 : ℝ)^4431 ≤ (8029019788755887/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3117 : ℕ)^4431*25000000000000000000^1024 ≤ 8029019788755887^1024*20000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3117 20000 8029019788755887 25000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3117/20000 : ℝ)) (X := (8029019788755887/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003066443315351829/25000000000000000000 : ℝ) ≤ (1250035430939907/1250000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (25003066443315351829/25000000000000000000 : ℝ)^1024 ≤ (1250035430939907/1250000000000000 : ℝ)^4431 := by
      have hnat : (25003066443315351829 : ℕ)^1024*1250000000000000^4431 ≤ 1250035430939907^4431*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003066443315351829 25000000000000000000 1250035430939907 1250000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035430939907/1250000000000000 : ℝ)) (X := (25003066443315351829/25000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019124482892863603/50000000000000000000 : ℝ) ≤ (10000883800109007/10000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (50019124482892863603/50000000000000000000 : ℝ)^1024 ≤ (10000883800109007/10000000000000000 : ℝ)^4431 := by
      have hnat : (50019124482892863603 : ℕ)^1024*10000000000000000^4431 ≤ 10000883800109007^4431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019124482892863603 50000000000000000000 10000883800109007 10000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000883800109007/10000000000000000 : ℝ)) (X := (50019124482892863603/50000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508029019788755887/12500000000000000000 : ℝ) ≤ (5000742076349379/5000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (12508029019788755887/12500000000000000000 : ℝ)^1024 ≤ (5000742076349379/5000000000000000 : ℝ)^4431 := by
      have hnat : (12508029019788755887 : ℕ)^1024*5000000000000000^4431 ≤ 5000742076349379^4431*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508029019788755887 12500000000000000000 5000742076349379 5000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000742076349379/5000000000000000 : ℝ)) (X := (12508029019788755887/12500000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3066443315351829/50000000000000000000 : ℝ) ≤ ((2476932049319990361/2477500000000000000 : ℝ)+2*(600352589751/495500000000000 : ℝ)*(1063/10000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (2476932049319990361/2477500000000000000 : ℝ)+2*(600352589751/495500000000000 : ℝ)*(1063/10000 : ℝ)=(1250035430939907/1250000000000000 : ℝ) by norm_num, show 1+2*(3066443315351829/50000000000000000000 : ℝ)=(25003066443315351829/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8029019788755887/25000000000000000000 : ℝ)+(3066443315351829/50000000000000000000 : ℝ) ≤ ((2476932049319990361/2477500000000000000 : ℝ)+(600352589751/495500000000000 : ℝ)*((3117/20000 : ℝ)+(1063/10000 : ℝ)))^(4431/1024 : ℝ) := by
    rw [show (2476932049319990361/2477500000000000000 : ℝ)+(600352589751/495500000000000 : ℝ)*((3117/20000 : ℝ)+(1063/10000 : ℝ))=(10000883800109007/10000000000000000 : ℝ) by norm_num, show 1+(8029019788755887/25000000000000000000 : ℝ)+(3066443315351829/50000000000000000000 : ℝ)=(50019124482892863603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8029019788755887/25000000000000000000 : ℝ) ≤ ((2476932049319990361/2477500000000000000 : ℝ)+2*(600352589751/495500000000000 : ℝ)*(3117/20000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (2476932049319990361/2477500000000000000 : ℝ)+2*(600352589751/495500000000000 : ℝ)*(3117/20000 : ℝ)=(5000742076349379/5000000000000000 : ℝ) by norm_num, show 1+2*(8029019788755887/25000000000000000000 : ℝ)=(12508029019788755887/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2476932049319990361/2477500000000000000 : ℝ)*(X 1 0+X 2 0)+(600352589751/495500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (1063/10000 : ℝ)) (hi := (3117/20000 : ℝ)) (c := (2476932049319990361/2477500000000000000 : ℝ)) (alpha := (600352589751/495500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2476932049319990361/2477500000000000000 : ℝ)*(X 0 1+X 2 1)+(600352589751/495500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (1063/10000 : ℝ)) (hi := (3117/20000 : ℝ)) (c := (2476932049319990361/2477500000000000000 : ℝ)) (alpha := (600352589751/495500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2476932049319990361/2477500000000000000 : ℝ)*(X 0 2+X 1 2)+(600352589751/495500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (1063/10000 : ℝ)) (hi := (3117/20000 : ℝ)) (c := (2476932049319990361/2477500000000000000 : ℝ)) (alpha := (600352589751/495500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-483728737/2500000000 : ℝ)*X 0 0+(2719888369/5000000000 : ℝ)*X 0 1+(1303601271/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338528931/2500000000 : ℝ)*X 1 0+(-2050465643/10000000000 : ℝ)*X 1 1+(130360127/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354115727/10000000000 : ℝ)*X 2 0+(5214405083/10000000000 : ℝ)*X 2 1+(-410093127/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4290640509/10000000000 : ℝ)*X 0 0+(809862629/2000000000 : ℝ)*X 0 1+(1136139661/2500000000 : ℝ)*X 0 2+(4290640509/10000000000 : ℝ)*X 1 0+(809862629/2000000000 : ℝ)*X 1 1+(1136139661/2500000000 : ℝ)*X 1 2+(4290640509/10000000000 : ℝ)*X 2 0+(809862629/2000000000 : ℝ)*X 2 1+(1136139661/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-483736609/2500000000 : ℝ)*X 0 0+(5215562747/10000000000 : ℝ)*X 0 1+(5438610537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529538031/1000000000 : ℝ)*X 1 0+(-1826260149/10000000000 : ℝ)*X 1 1+(2719305261/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059076057/2000000000 : ℝ)*X 2 0+(5438610547/10000000000 : ℝ)*X 2 1+(-1826260149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1072677433/2500000000 : ℝ)*X 0 0+(4542014733/10000000000 : ℝ)*X 0 1+(405187587/1000000000 : ℝ)*X 0 2+(1072677433/2500000000 : ℝ)*X 1 0+(4542014733/10000000000 : ℝ)*X 1 1+(405187587/1000000000 : ℝ)*X 1 2+(1072677433/2500000000 : ℝ)*X 2 0+(4542014733/10000000000 : ℝ)*X 2 1+(405187587/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (641484529474492691230380171/61937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1876814497/100000000000000 : ℝ)*(base19) + (1763438077/100000000000000 : ℝ)*(base23) + (31017099/50000000000000 : ℝ)*(lower2) + (26053529/10000000000000 : ℝ)*(upper3) + (182314969/100000000000000 : ℝ)*(upper5) + (1614100137317237/50000000000000 : ℝ)*(major0) + (1614100137317237/50000000000000 : ℝ)*(major1) + (1614100137317237/50000000000000 : ℝ)*(major2) + (2218572213792199/50000000000000 : ℝ)*(sp0) + (4437170911241317/100000000000000 : ℝ)*(sp1) + (4437171024617737/100000000000000 : ℝ)*(sp2) + (2019213335741183/100000000000000 : ℝ)*(sp3) + (3545058927/12500000000000 : ℝ)*(sp4) + (14080239773/100000000000000 : ℝ)*(sp7) + (504806853995239/25000000000000 : ℝ)*(f.failure) + (2218586394027907/50000000000000 : ℝ)*(f.sum) + (26976706780851/24775000000000000000000000000 : ℝ)*base66 + (163005713498412443/123875000000000000000000000000000 : ℝ)*base68 + (795226992736662443/123875000000000000000000000000000 : ℝ)*base70 + (1243780635268537443/123875000000000000000000000000000 : ℝ)*base72 + (85634190571399/24775000000000000000000000000 : ℝ)*base73 + (399485378366337557/123875000000000000000000000000000 : ℝ)*base75 + (2002723280191162443/123875000000000000000000000000000 : ℝ)*base78 + (1382374093783462557/123875000000000000000000000000000 : ℝ)*base79 + (109213530291451/24775000000000000000000000000 : ℝ)*base82 + (8451799/2500000000000000000000 : ℝ)*base89 + (8451799/2500000000000000000000 : ℝ)*base91 + (8451799/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92325647738023009856155737/12387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1299574267/100000000000000 : ℝ)*(base19) + (347585337/25000000000000 : ℝ)*(base23) + (81217233/50000000000000 : ℝ)*(upper3) + (9847417/20000000000000 : ℝ)*(lower4) + (36857943/25000000000000 : ℝ)*(upper5) + (326179053140987/10000000000000 : ℝ)*(major0) + (326179053140987/10000000000000 : ℝ)*(major1) + (326179053140987/10000000000000 : ℝ)*(major2) + (1889458861/10000000000000 : ℝ)*(sp1) + (10301619783/50000000000000 : ℝ)*(sp2) + (1120835704037697/25000000000000 : ℝ)*(sp4) + (4483322621987911/100000000000000 : ℝ)*(sp5) + (2241660411284937/50000000000000 : ℝ)*(sp6) + (1020118999115639/50000000000000 : ℝ)*(sp7) + (1020118999115639/50000000000000 : ℝ)*(f.failure) + (1120835704037697/25000000000000 : ℝ)*(f.sum) + (6195640962383/2477500000000000000000000000 : ℝ)*base66 + (231008002002461307/24775000000000000000000000000000 : ℝ)*base67 + (357008657213811307/24775000000000000000000000000000 : ℝ)*base69 + (22966873133061307/24775000000000000000000000000000 : ℝ)*base71 + (20549419944699/4955000000000000000000000000 : ℝ)*base73 + (495305551730661307/24775000000000000000000000000000 : ℝ)*base75 + (47641471900511307/24775000000000000000000000000000 : ℝ)*base77 + (434894349596961307/24775000000000000000000000000000 : ℝ)*base79 + (6747338579277/2477500000000000000000000000 : ℝ)*base81 + (17588199/5000000000000000000000 : ℝ)*base89 + (17588199/5000000000000000000000 : ℝ)*base91 + (17588199/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1468_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3117/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1063/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1468_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1468_s5_0 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-967509077/5000000000 : ℝ)*x 0 + (1359778303/2500000000 : ℝ)*x 1 + (40742191/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (967509077/5000000000 : ℝ)^4433 ≤ (2362917368907/20000000000000 : ℝ)^3409 := by
    have hnat : (967509077 : ℕ)^4433*20000000000000^3409 ≤ 2362917368907^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967509077 5000000000 2362917368907 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359778303/2500000000 : ℝ)^4433 ≤ (4529869319617/10000000000000 : ℝ)^3409 := by
    have hnat : (1359778303 : ℕ)^4433*10000000000000^3409 ≤ 4529869319617^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359778303 2500000000 4529869319617 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40742191/78125000 : ℝ)^4433 ≤ (21443359972759/50000000000000 : ℝ)^3409 := by
    have hnat : (40742191 : ℕ)^4433*50000000000000^3409 ≤ 21443359972759^3409*78125000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40742191 78125000 21443359972759 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-967509077/5000000000 : ℝ), (1359778303/2500000000 : ℝ), (40742191/78125000 : ℝ)] ![(2362917368907/20000000000000 : ℝ), (4529869319617/10000000000000 : ℝ), (21443359972759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-967509077/5000000000 : ℝ)|^4433 ≤ (2362917368907/20000000000000 : ℝ)^3409
        have hw : |(-967509077/5000000000 : ℝ)|=(967509077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359778303/2500000000 : ℝ)|^4433 ≤ (4529869319617/10000000000000 : ℝ)^3409
        have hw : |(1359778303/2500000000 : ℝ)|=(1359778303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40742191/78125000 : ℝ)|^4433 ≤ (21443359972759/50000000000000 : ℝ)^3409
        have hw : |(40742191/78125000 : ℝ)|=(40742191/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s5_1 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676971703/5000000000 : ℝ)*x 0 + (-1024953767/5000000000 : ℝ)*x 1 + (13037501/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676971703/5000000000 : ℝ)^4433 ≤ (2773655110523/6250000000000 : ℝ)^3409 := by
    have hnat : (2676971703 : ℕ)^4433*6250000000000^3409 ≤ 2773655110523^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676971703 5000000000 2773655110523 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024953767/5000000000 : ℝ)^4433 ≤ (6367399393897/50000000000000 : ℝ)^3409 := by
    have hnat : (1024953767 : ℕ)^4433*50000000000000^3409 ≤ 6367399393897^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024953767 5000000000 6367399393897 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13037501/25000000 : ℝ)^4433 ≤ (42886719432207/100000000000000 : ℝ)^3409 := by
    have hnat : (13037501 : ℕ)^4433*100000000000000^3409 ≤ 42886719432207^3409*25000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13037501 25000000 42886719432207 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676971703/5000000000 : ℝ), (-1024953767/5000000000 : ℝ), (13037501/25000000 : ℝ)] ![(2773655110523/6250000000000 : ℝ), (6367399393897/50000000000000 : ℝ), (42886719432207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676971703/5000000000 : ℝ)|^4433 ≤ (2773655110523/6250000000000 : ℝ)^3409
        have hw : |(2676971703/5000000000 : ℝ)|=(2676971703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024953767/5000000000 : ℝ)|^4433 ≤ (6367399393897/50000000000000 : ℝ)^3409
        have hw : |(-1024953767/5000000000 : ℝ)|=(1024953767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13037501/25000000 : ℝ)|^4433 ≤ (42886719432207/100000000000000 : ℝ)^3409
        have hw : |(13037501/25000000 : ℝ)|=(13037501/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s5_2 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338485843/2500000000 : ℝ)*x 0 + (104300009/200000000 : ℝ)*x 1 + (-2049907513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338485843/2500000000 : ℝ)^4433 ≤ (44378481401889/100000000000000 : ℝ)^3409 := by
    have hnat : (1338485843 : ℕ)^4433*100000000000000^3409 ≤ 44378481401889^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338485843 2500000000 44378481401889 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104300009/200000000 : ℝ)^4433 ≤ (21443359983453/50000000000000 : ℝ)^3409 := by
    have hnat : (104300009 : ℕ)^4433*50000000000000^3409 ≤ 21443359983453^3409*200000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104300009 200000000 21443359983453 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049907513/10000000000 : ℝ)^4433 ≤ (12734798618147/100000000000000 : ℝ)^3409 := by
    have hnat : (2049907513 : ℕ)^4433*100000000000000^3409 ≤ 12734798618147^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049907513 10000000000 12734798618147 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338485843/2500000000 : ℝ), (104300009/200000000 : ℝ), (-2049907513/10000000000 : ℝ)] ![(44378481401889/100000000000000 : ℝ), (21443359983453/50000000000000 : ℝ), (12734798618147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338485843/2500000000 : ℝ)|^4433 ≤ (44378481401889/100000000000000 : ℝ)^3409
        have hw : |(1338485843/2500000000 : ℝ)|=(1338485843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104300009/200000000 : ℝ)|^4433 ≤ (21443359983453/50000000000000 : ℝ)^3409
        have hw : |(104300009/200000000 : ℝ)|=(104300009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049907513/10000000000 : ℝ)|^4433 ≤ (12734798618147/100000000000000 : ℝ)^3409
        have hw : |(-2049907513/10000000000 : ℝ)|=(2049907513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s5_3 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2145351591/5000000000 : ℝ)*x 0 + (506336117/1250000000 : ℝ)*x 1 + (4543167989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145351591/5000000000 : ℝ)^4433 ≤ (33277207994293/100000000000000 : ℝ)^3409 := by
    have hnat : (2145351591 : ℕ)^4433*100000000000000^3409 ≤ 33277207994293^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145351591 5000000000 33277207994293 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506336117/1250000000 : ℝ)^4433 ≤ (7719299728417/25000000000000 : ℝ)^3409 := by
    have hnat : (506336117 : ℕ)^4433*25000000000000^3409 ≤ 7719299728417^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506336117 1250000000 7719299728417 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4543167989/10000000000 : ℝ)^4433 ≤ (17922796540133/50000000000000 : ℝ)^3409 := by
    have hnat : (4543167989 : ℕ)^4433*50000000000000^3409 ≤ 17922796540133^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543167989 10000000000 17922796540133 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145351591/5000000000 : ℝ), (506336117/1250000000 : ℝ), (4543167989/10000000000 : ℝ)] ![(33277207994293/100000000000000 : ℝ), (7719299728417/25000000000000 : ℝ), (17922796540133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145351591/5000000000 : ℝ)|^4433 ≤ (33277207994293/100000000000000 : ℝ)^3409
        have hw : |(2145351591/5000000000 : ℝ)|=(2145351591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506336117/1250000000 : ℝ)|^4433 ≤ (7719299728417/25000000000000 : ℝ)^3409
        have hw : |(506336117/1250000000 : ℝ)|=(506336117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4543167989/10000000000 : ℝ)|^4433 ≤ (17922796540133/50000000000000 : ℝ)^3409
        have hw : |(4543167989/10000000000 : ℝ)|=(4543167989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s5_4 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-483762383/2500000000 : ℝ)*x 0 + (260807221/500000000 : ℝ)*x 1 + (543796053/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483762383/2500000000 : ℝ)^4433 ≤ (2953708994281/25000000000000 : ℝ)^3409 := by
    have hnat : (483762383 : ℕ)^4433*25000000000000^3409 ≤ 2953708994281^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483762383 2500000000 2953708994281 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260807221/500000000 : ℝ)^4433 ≤ (42898953957851/100000000000000 : ℝ)^3409 := by
    have hnat : (260807221 : ℕ)^4433*100000000000000^3409 ≤ 42898953957851^3409*500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260807221 500000000 42898953957851 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543796053/1000000000 : ℝ)^4433 ≤ (45286210051829/100000000000000 : ℝ)^3409 := by
    have hnat : (543796053 : ℕ)^4433*100000000000000^3409 ≤ 45286210051829^3409*1000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543796053 1000000000 45286210051829 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-483762383/2500000000 : ℝ), (260807221/500000000 : ℝ), (543796053/1000000000 : ℝ)] ![(2953708994281/25000000000000 : ℝ), (42898953957851/100000000000000 : ℝ), (45286210051829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-483762383/2500000000 : ℝ)|^4433 ≤ (2953708994281/25000000000000 : ℝ)^3409
        have hw : |(-483762383/2500000000 : ℝ)|=(483762383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260807221/500000000 : ℝ)|^4433 ≤ (42898953957851/100000000000000 : ℝ)^3409
        have hw : |(260807221/500000000 : ℝ)|=(260807221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543796053/1000000000 : ℝ)|^4433 ≤ (45286210051829/100000000000000 : ℝ)^3409
        have hw : |(543796053/1000000000 : ℝ)|=(543796053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s5_5 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5171423/9765625 : ℝ)*x 0 + (-228368527/1250000000 : ℝ)*x 1 + (543795913/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171423/9765625 : ℝ)^4433 ≤ (21874984011621/50000000000000 : ℝ)^3409 := by
    have hnat : (5171423 : ℕ)^4433*50000000000000^3409 ≤ 21874984011621^3409*9765625^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171423 9765625 21874984011621 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228368527/1250000000 : ℝ)^4433 ≤ (5481918535471/50000000000000 : ℝ)^3409 := by
    have hnat : (228368527 : ℕ)^4433*50000000000000^3409 ≤ 5481918535471^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228368527 1250000000 5481918535471 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543795913/1000000000 : ℝ)^4433 ≤ (113215487227/250000000000 : ℝ)^3409 := by
    have hnat : (543795913 : ℕ)^4433*250000000000^3409 ≤ 113215487227^3409*1000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543795913 1000000000 113215487227 250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171423/9765625 : ℝ), (-228368527/1250000000 : ℝ), (543795913/1000000000 : ℝ)] ![(21874984011621/50000000000000 : ℝ), (5481918535471/50000000000000 : ℝ), (113215487227/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171423/9765625 : ℝ)|^4433 ≤ (21874984011621/50000000000000 : ℝ)^3409
        have hw : |(5171423/9765625 : ℝ)|=(5171423/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-228368527/1250000000 : ℝ)|^4433 ≤ (5481918535471/50000000000000 : ℝ)^3409
        have hw : |(-228368527/1250000000 : ℝ)|=(228368527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543795913/1000000000 : ℝ)|^4433 ≤ (113215487227/250000000000 : ℝ)^3409
        have hw : |(543795913/1000000000 : ℝ)|=(543795913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s5_6 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295536929/10000000000 : ℝ)*x 0 + (5437959539/10000000000 : ℝ)*x 1 + (-913473977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295536929/10000000000 : ℝ)^4433 ≤ (21874982813741/50000000000000 : ℝ)^3409 := by
    have hnat : (5295536929 : ℕ)^4433*50000000000000^3409 ≤ 21874982813741^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295536929 10000000000 21874982813741 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437959539/10000000000 : ℝ)^4433 ≤ (22643099659993/50000000000000 : ℝ)^3409 := by
    have hnat : (5437959539 : ℕ)^4433*50000000000000^3409 ≤ 22643099659993^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437959539 10000000000 22643099659993 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (913473977/5000000000 : ℝ)^4433 ≤ (5481917513171/50000000000000 : ℝ)^3409 := by
    have hnat : (913473977 : ℕ)^4433*50000000000000^3409 ≤ 5481917513171^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913473977 5000000000 5481917513171 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295536929/10000000000 : ℝ), (5437959539/10000000000 : ℝ), (-913473977/5000000000 : ℝ)] ![(21874982813741/50000000000000 : ℝ), (22643099659993/50000000000000 : ℝ), (5481917513171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295536929/10000000000 : ℝ)|^4433 ≤ (21874982813741/50000000000000 : ℝ)^3409
        have hw : |(5295536929/10000000000 : ℝ)|=(5295536929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437959539/10000000000 : ℝ)|^4433 ≤ (22643099659993/50000000000000 : ℝ)^3409
        have hw : |(5437959539/10000000000 : ℝ)|=(5437959539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-913473977/5000000000 : ℝ)|^4433 ≤ (5481917513171/50000000000000 : ℝ)^3409
        have hw : |(-913473977/5000000000 : ℝ)|=(913473977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s5_7 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072692903/2500000000 : ℝ)*x 0 + (4540652439/10000000000 : ℝ)*x 1 + (2026611309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072692903/2500000000 : ℝ)^4433 ≤ (3327789813353/10000000000000 : ℝ)^3409 := by
    have hnat : (1072692903 : ℕ)^4433*10000000000000^3409 ≤ 3327789813353^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072692903 2500000000 3327789813353 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4540652439/10000000000 : ℝ)^4433 ≤ (35819785663437/100000000000000 : ℝ)^3409 := by
    have hnat : (4540652439 : ℕ)^4433*100000000000000^3409 ≤ 35819785663437^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540652439 10000000000 35819785663437 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026611309/5000000000 : ℝ)^4433 ≤ (30902316194951/100000000000000 : ℝ)^3409 := by
    have hnat : (2026611309 : ℕ)^4433*100000000000000^3409 ≤ 30902316194951^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026611309 5000000000 30902316194951 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072692903/2500000000 : ℝ), (4540652439/10000000000 : ℝ), (2026611309/5000000000 : ℝ)] ![(3327789813353/10000000000000 : ℝ), (35819785663437/100000000000000 : ℝ), (30902316194951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072692903/2500000000 : ℝ)|^4433 ≤ (3327789813353/10000000000000 : ℝ)^3409
        have hw : |(1072692903/2500000000 : ℝ)|=(1072692903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4540652439/10000000000 : ℝ)|^4433 ≤ (35819785663437/100000000000000 : ℝ)^3409
        have hw : |(4540652439/10000000000 : ℝ)|=(4540652439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2026611309/5000000000 : ℝ)|^4433 ≤ (30902316194951/100000000000000 : ℝ)^3409
        have hw : |(2026611309/5000000000 : ℝ)|=(2026611309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1468_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2683/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7737/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10719/100000 : ℝ) ^ (4431/1024 : ℝ) ≤ (1589547745708627/25000000000000000000 : ℝ) := by
    have hpowers : (10719/100000 : ℝ)^4431 ≤ (1589547745708627/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10719 : ℕ)^4431*25000000000000000000^1024 ≤ 1589547745708627^1024*100000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10719 100000 1589547745708627 25000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10719/100000 : ℝ)) (X := (1589547745708627/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4431/1024 : ℝ) ≤ (31260045150592031/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4431 ≤ (31260045150592031/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4431*100000000000000000000^1024 ≤ 31260045150592031^1024*3125^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 31260045150592031 100000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (31260045150592031/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501589547745708627/12500000000000000000 : ℝ) ≤ (10000293860044671/10000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (12501589547745708627/12500000000000000000 : ℝ)^1024 ≤ (10000293860044671/10000000000000000 : ℝ)^4431 := by
      have hnat : (12501589547745708627 : ℕ)^1024*10000000000000000^4431 ≤ 10000293860044671^4431*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501589547745708627 12500000000000000000 10000293860044671 10000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000293860044671/10000000000000000 : ℝ)) (X := (12501589547745708627/12500000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037618236133426539/100000000000000000000 : ℝ) ≤ (2500217307063779/2500000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (100037618236133426539/100000000000000000000 : ℝ)^1024 ≤ (2500217307063779/2500000000000000 : ℝ)^4431 := by
      have hnat : (100037618236133426539 : ℕ)^1024*2500000000000000^4431 ≤ 2500217307063779^4431*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037618236133426539 100000000000000000000 2500217307063779 2500000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500217307063779/2500000000000000 : ℝ)) (X := (100037618236133426539/100000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031260045150592031/50000000000000000000 : ℝ) ≤ (10001444596465561/10000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (50031260045150592031/50000000000000000000 : ℝ)^1024 ≤ (10001444596465561/10000000000000000 : ℝ)^4431 := by
      have hnat : (50031260045150592031 : ℕ)^1024*10000000000000000^4431 ≤ 10001444596465561^4431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031260045150592031 50000000000000000000 10001444596465561 10000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001444596465561/10000000000000000 : ℝ)) (X := (50031260045150592031/50000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1589547745708627/25000000000000000000 : ℝ) ≤ ((47679066674857516089/47690000000000000000 : ℝ)+2*(115073642089/95380000000000 : ℝ)*(10719/100000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (47679066674857516089/47690000000000000000 : ℝ)+2*(115073642089/95380000000000 : ℝ)*(10719/100000 : ℝ)=(10000293860044671/10000000000000000 : ℝ) by norm_num, show 1+2*(1589547745708627/25000000000000000000 : ℝ)=(12501589547745708627/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31260045150592031/100000000000000000000 : ℝ)+(1589547745708627/25000000000000000000 : ℝ) ≤ ((47679066674857516089/47690000000000000000 : ℝ)+(115073642089/95380000000000 : ℝ)*((484/3125 : ℝ)+(10719/100000 : ℝ)))^(4431/1024 : ℝ) := by
    rw [show (47679066674857516089/47690000000000000000 : ℝ)+(115073642089/95380000000000 : ℝ)*((484/3125 : ℝ)+(10719/100000 : ℝ))=(2500217307063779/2500000000000000 : ℝ) by norm_num, show 1+(31260045150592031/100000000000000000000 : ℝ)+(1589547745708627/25000000000000000000 : ℝ)=(100037618236133426539/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31260045150592031/100000000000000000000 : ℝ) ≤ ((47679066674857516089/47690000000000000000 : ℝ)+2*(115073642089/95380000000000 : ℝ)*(484/3125 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (47679066674857516089/47690000000000000000 : ℝ)+2*(115073642089/95380000000000 : ℝ)*(484/3125 : ℝ)=(10001444596465561/10000000000000000 : ℝ) by norm_num, show 1+2*(31260045150592031/100000000000000000000 : ℝ)=(50031260045150592031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47679066674857516089/47690000000000000000 : ℝ)*(X 1 0+X 2 0)+(115073642089/95380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47679066674857516089/47690000000000000000 : ℝ)) (alpha := (115073642089/95380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47679066674857516089/47690000000000000000 : ℝ)*(X 0 1+X 2 1)+(115073642089/95380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47679066674857516089/47690000000000000000 : ℝ)) (alpha := (115073642089/95380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47679066674857516089/47690000000000000000 : ℝ)*(X 0 2+X 1 2)+(115073642089/95380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47679066674857516089/47690000000000000000 : ℝ)) (alpha := (115073642089/95380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-967509077/5000000000 : ℝ)*X 0 0+(1359778303/2500000000 : ℝ)*X 0 1+(40742191/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676971703/5000000000 : ℝ)*X 1 0+(-1024953767/5000000000 : ℝ)*X 1 1+(13037501/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338485843/2500000000 : ℝ)*X 2 0+(104300009/200000000 : ℝ)*X 2 1+(-2049907513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2145351591/5000000000 : ℝ)*X 0 0+(506336117/1250000000 : ℝ)*X 0 1+(4543167989/10000000000 : ℝ)*X 0 2+(2145351591/5000000000 : ℝ)*X 1 0+(506336117/1250000000 : ℝ)*X 1 1+(4543167989/10000000000 : ℝ)*X 1 2+(2145351591/5000000000 : ℝ)*X 2 0+(506336117/1250000000 : ℝ)*X 2 1+(4543167989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-483762383/2500000000 : ℝ)*X 0 0+(260807221/500000000 : ℝ)*X 0 1+(543796053/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171423/9765625 : ℝ)*X 1 0+(-228368527/1250000000 : ℝ)*X 1 1+(543795913/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295536929/10000000000 : ℝ)*X 2 0+(5437959539/10000000000 : ℝ)*X 2 1+(-913473977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1072692903/2500000000 : ℝ)*X 0 0+(4540652439/10000000000 : ℝ)*X 0 1+(2026611309/5000000000 : ℝ)*X 0 2+(1072692903/2500000000 : ℝ)*X 1 0+(4540652439/10000000000 : ℝ)*X 1 1+(2026611309/5000000000 : ℝ)*X 1 2+(1072692903/2500000000 : ℝ)*X 2 0+(4540652439/10000000000 : ℝ)*X 2 1+(2026611309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18581254420160065079247/2384500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1466815159/100000000000000 : ℝ)*(base19) + (668844647/50000000000000 : ℝ)*(base23) + (53962177/100000000000000 : ℝ)*(lower2) + (199671317/100000000000000 : ℝ)*(upper3) + (27914351/20000000000000 : ℝ)*(upper5) + (3246323491878587/100000000000000 : ℝ)*(major0) + (3246323491878587/100000000000000 : ℝ)*(major1) + (3246323491878587/100000000000000 : ℝ)*(major2) + (2231030869310893/50000000000000 : ℝ)*(sp0) + (446208183538317/10000000000000 : ℝ)*(sp1) + (1115520491127259/25000000000000 : ℝ)*(sp2) + (1015276413966791/50000000000000 : ℝ)*(sp3) + (21563576543/100000000000000 : ℝ)*(sp4) + (10593874719/100000000000000 : ℝ)*(sp7) + (2030563421808301/100000000000000 : ℝ)*(f.failure) + (446208330219833/10000000000000 : ℝ)*(f.sum) + (6944643936073/953800000000000000000000000 : ℝ)*base66 + (24070165529056413757/4769000000000000000000000000000000 : ℝ)*base68 + (28721818432493413757/4769000000000000000000000000000000 : ℝ)*base70 + (12479942216840586243/4769000000000000000000000000000000 : ℝ)*base71 + (12985412295077/2384500000000000000000000000 : ℝ)*base74 + (36409081836448586243/4769000000000000000000000000000000 : ℝ)*base75 + (92540268765227413757/4769000000000000000000000000000000 : ℝ)*base78 + (24320450607291586243/4769000000000000000000000000000000 : ℝ)*base79 + (1065287171989/190760000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (99913341/10000000000000000000000 : ℝ)*base89 + (99913341/10000000000000000000000 : ℝ)*base91 + (99913341/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3061391267050739930499940329/1192250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1969307547/100000000000000 : ℝ)*(base19) + (1927218581/100000000000000 : ℝ)*(base23) + (43388617/50000000000000 : ℝ)*(upper2) + (193647709/50000000000000 : ℝ)*(upper5) + (3279911149116613/100000000000000 : ℝ)*(major0) + (3279911149116613/100000000000000 : ℝ)*(major1) + (3279911149116613/100000000000000 : ℝ)*(major2) + (305998211/25000000000000 : ℝ)*(sp0) + (825661013/6250000000000 : ℝ)*(sp1) + (11749791533/100000000000000 : ℝ)*(sp2) + (4508248610591401/100000000000000 : ℝ)*(sp4) + (450823465470049/10000000000000 : ℝ)*(sp5) + (1127059039393533/25000000000000 : ℝ)*(sp6) + (256446547257193/12500000000000 : ℝ)*(sp7) + (256446547257193/12500000000000 : ℝ)*(f.failure) + (2254124917292123/50000000000000 : ℝ)*(f.sum) + (2850300276223/4769000000000000000000000000 : ℝ)*base66 + (20846066562947186557/4769000000000000000000000000000000 : ℝ)*base67 + (51341963226717186557/4769000000000000000000000000000000 : ℝ)*base69 + (19126400014799186557/4769000000000000000000000000000000 : ℝ)*base71 + (13733914945381/4769000000000000000000000000 : ℝ)*base73 + (62991389056315186557/4769000000000000000000000000000000 : ℝ)*base75 + (4902211139744813443/4769000000000000000000000000000000 : ℝ)*base78 + (107688375520097186557/4769000000000000000000000000000000 : ℝ)*base79 + (9872991869221/2384500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (8466087/1250000000000000000000 : ℝ)*base90 + (8466087/1250000000000000000000 : ℝ)*base92 + (8466087/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1468_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1468_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1468_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2519/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1468_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1468_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1468_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2519/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1468_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

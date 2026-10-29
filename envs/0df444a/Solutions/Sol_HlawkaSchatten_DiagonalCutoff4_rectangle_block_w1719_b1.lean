-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1719_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:55:28.161986+00:00
-- url     : https://prove2.me/submissions/790f89d2-7dd4-4f14-8c32-174cad263ce5

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
theorem support_rectangle_w1719_s3_0 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1380213089/10000000000 : ℝ)*x 0 + (5464335993/10000000000 : ℝ)*x 1 + (2569664607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380213089/10000000000 : ℝ)^5375 ≤ (2165080389941/25000000000000 : ℝ)^4351 := by
    have hnat : (1380213089 : ℕ)^5375*25000000000000^4351 ≤ 2165080389941^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380213089 10000000000 2165080389941 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464335993/10000000000 : ℝ)^5375 ≤ (23699397183077/50000000000000 : ℝ)^4351 := by
    have hnat : (5464335993 : ℕ)^5375*50000000000000^4351 ≤ 23699397183077^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464335993 10000000000 23699397183077 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569664607/5000000000 : ℝ)^5375 ≤ (4394088406223/10000000000000 : ℝ)^4351 := by
    have hnat : (2569664607 : ℕ)^5375*10000000000000^4351 ≤ 4394088406223^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569664607 5000000000 4394088406223 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1380213089/10000000000 : ℝ), (5464335993/10000000000 : ℝ), (2569664607/5000000000 : ℝ)] ![(2165080389941/25000000000000 : ℝ), (23699397183077/50000000000000 : ℝ), (4394088406223/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1380213089/10000000000 : ℝ)|^5375 ≤ (2165080389941/25000000000000 : ℝ)^4351
        have hw : |(-1380213089/10000000000 : ℝ)|=(1380213089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464335993/10000000000 : ℝ)|^5375 ≤ (23699397183077/50000000000000 : ℝ)^4351
        have hw : |(5464335993/10000000000 : ℝ)|=(5464335993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569664607/5000000000 : ℝ)|^5375 ≤ (4394088406223/10000000000000 : ℝ)^4351
        have hw : |(2569664607/5000000000 : ℝ)|=(2569664607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s3_1 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340490811/10000000000 : ℝ)*x 0 + (-387153567/2500000000 : ℝ)*x 1 + (5139329193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340490811/10000000000 : ℝ)^5375 ≤ (460752703869/1000000000000 : ℝ)^4351 := by
    have hnat : (5340490811 : ℕ)^5375*1000000000000^4351 ≤ 460752703869^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340490811 10000000000 460752703869 1000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387153567/2500000000 : ℝ)^5375 ≤ (1996769152621/20000000000000 : ℝ)^4351 := by
    have hnat : (387153567 : ℕ)^5375*20000000000000^4351 ≤ 1996769152621^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387153567 2500000000 1996769152621 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139329193/10000000000 : ℝ)^5375 ≤ (1757635353617/4000000000000 : ℝ)^4351 := by
    have hnat : (5139329193 : ℕ)^5375*4000000000000^4351 ≤ 1757635353617^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139329193 10000000000 1757635353617 4000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340490811/10000000000 : ℝ), (-387153567/2500000000 : ℝ), (5139329193/10000000000 : ℝ)] ![(460752703869/1000000000000 : ℝ), (1996769152621/20000000000000 : ℝ), (1757635353617/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340490811/10000000000 : ℝ)|^5375 ≤ (460752703869/1000000000000 : ℝ)^4351
        have hw : |(5340490811/10000000000 : ℝ)|=(5340490811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-387153567/2500000000 : ℝ)|^5375 ≤ (1996769152621/20000000000000 : ℝ)^4351
        have hw : |(-387153567/2500000000 : ℝ)|=(387153567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139329193/10000000000 : ℝ)|^5375 ≤ (1757635353617/4000000000000 : ℝ)^4351
        have hw : |(5139329193/10000000000 : ℝ)|=(5139329193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s3_2 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83445169/156250000 : ℝ)*x 0 + (642416147/1250000000 : ℝ)*x 1 + (-1548614283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83445169/156250000 : ℝ)^5375 ≤ (4607527044019/10000000000000 : ℝ)^4351 := by
    have hnat : (83445169 : ℕ)^5375*10000000000000^4351 ≤ 4607527044019^4351*156250000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83445169 156250000 4607527044019 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642416147/1250000000 : ℝ)^5375 ≤ (43940883660869/100000000000000 : ℝ)^4351 := by
    have hnat : (642416147 : ℕ)^5375*100000000000000^4351 ≤ 43940883660869^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642416147 1250000000 43940883660869 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1548614283/10000000000 : ℝ)^5375 ≤ (1247980735321/12500000000000 : ℝ)^4351 := by
    have hnat : (1548614283 : ℕ)^5375*12500000000000^4351 ≤ 1247980735321^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548614283 10000000000 1247980735321 12500000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83445169/156250000 : ℝ), (642416147/1250000000 : ℝ), (-1548614283/10000000000 : ℝ)] ![(4607527044019/10000000000000 : ℝ), (43940883660869/100000000000000 : ℝ), (1247980735321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83445169/156250000 : ℝ)|^5375 ≤ (4607527044019/10000000000000 : ℝ)^4351
        have hw : |(83445169/156250000 : ℝ)|=(83445169/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642416147/1250000000 : ℝ)|^5375 ≤ (43940883660869/100000000000000 : ℝ)^4351
        have hw : |(642416147/1250000000 : ℝ)|=(642416147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1548614283/10000000000 : ℝ)|^5375 ≤ (1247980735321/12500000000000 : ℝ)^4351
        have hw : |(-1548614283/10000000000 : ℝ)|=(1548614283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s3_3 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4093320613/10000000000 : ℝ)*x 0 + (1814976073/5000000000 : ℝ)*x 1 + (4591590729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4093320613/10000000000 : ℝ)^5375 ≤ (16586261087171/50000000000000 : ℝ)^4351 := by
    have hnat : (4093320613 : ℕ)^5375*50000000000000^4351 ≤ 16586261087171^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093320613 10000000000 16586261087171 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1814976073/5000000000 : ℝ)^5375 ≤ (571945129671/2000000000000 : ℝ)^4351 := by
    have hnat : (1814976073 : ℕ)^5375*2000000000000^4351 ≤ 571945129671^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814976073 5000000000 571945129671 2000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4591590729/10000000000 : ℝ)^5375 ≤ (19115110665103/50000000000000 : ℝ)^4351 := by
    have hnat : (4591590729 : ℕ)^5375*50000000000000^4351 ≤ 19115110665103^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4591590729 10000000000 19115110665103 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4093320613/10000000000 : ℝ), (1814976073/5000000000 : ℝ), (4591590729/10000000000 : ℝ)] ![(16586261087171/50000000000000 : ℝ), (571945129671/2000000000000 : ℝ), (19115110665103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4093320613/10000000000 : ℝ)|^5375 ≤ (16586261087171/50000000000000 : ℝ)^4351
        have hw : |(4093320613/10000000000 : ℝ)|=(4093320613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1814976073/5000000000 : ℝ)|^5375 ≤ (571945129671/2000000000000 : ℝ)^4351
        have hw : |(1814976073/5000000000 : ℝ)|=(1814976073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4591590729/10000000000 : ℝ)|^5375 ≤ (19115110665103/50000000000000 : ℝ)^4351
        have hw : |(4591590729/10000000000 : ℝ)|=(4591590729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s3_4 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21568111/156250000 : ℝ)*x 0 + (1285739253/2500000000 : ℝ)*x 1 + (5460653961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21568111/156250000 : ℝ)^5375 ≤ (8661453387/100000000000 : ℝ)^4351 := by
    have hnat : (21568111 : ℕ)^5375*100000000000^4351 ≤ 8661453387^4351*156250000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21568111 156250000 8661453387 100000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285739253/2500000000 : ℝ)^5375 ≤ (21989602269371/50000000000000 : ℝ)^4351 := by
    have hnat : (1285739253 : ℕ)^5375*50000000000000^4351 ≤ 21989602269371^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285739253 2500000000 21989602269371 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460653961/10000000000 : ℝ)^5375 ≤ (23679671029759/50000000000000 : ℝ)^4351 := by
    have hnat : (5460653961 : ℕ)^5375*50000000000000^4351 ≤ 23679671029759^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460653961 10000000000 23679671029759 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21568111/156250000 : ℝ), (1285739253/2500000000 : ℝ), (5460653961/10000000000 : ℝ)] ![(8661453387/100000000000 : ℝ), (21989602269371/50000000000000 : ℝ), (23679671029759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21568111/156250000 : ℝ)|^5375 ≤ (8661453387/100000000000 : ℝ)^4351
        have hw : |(-21568111/156250000 : ℝ)|=(21568111/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285739253/2500000000 : ℝ)|^5375 ≤ (21989602269371/50000000000000 : ℝ)^4351
        have hw : |(1285739253/2500000000 : ℝ)|=(1285739253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460653961/10000000000 : ℝ)|^5375 ≤ (23679671029759/50000000000000 : ℝ)^4351
        have hw : |(5460653961/10000000000 : ℝ)|=(5460653961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s3_5 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262674401/500000000 : ℝ)*x 0 + (-613644553/5000000000 : ℝ)*x 1 + (5460654949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262674401/500000000 : ℝ)^5375 ≤ (5643722359559/12500000000000 : ℝ)^4351 := by
    have hnat : (262674401 : ℕ)^5375*12500000000000^4351 ≤ 5643722359559^4351*500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262674401 500000000 5643722359559 12500000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613644553/5000000000 : ℝ)^5375 ≤ (7490868461009/100000000000000 : ℝ)^4351 := by
    have hnat : (613644553 : ℕ)^5375*100000000000000^4351 ≤ 7490868461009^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613644553 5000000000 7490868461009 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460654949/10000000000 : ℝ)^5375 ≤ (47359352644919/100000000000000 : ℝ)^4351 := by
    have hnat : (5460654949 : ℕ)^5375*100000000000000^4351 ≤ 47359352644919^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460654949 10000000000 47359352644919 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262674401/500000000 : ℝ), (-613644553/5000000000 : ℝ), (5460654949/10000000000 : ℝ)] ![(5643722359559/12500000000000 : ℝ), (7490868461009/100000000000000 : ℝ), (47359352644919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262674401/500000000 : ℝ)|^5375 ≤ (5643722359559/12500000000000 : ℝ)^4351
        have hw : |(262674401/500000000 : ℝ)|=(262674401/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-613644553/5000000000 : ℝ)|^5375 ≤ (7490868461009/100000000000000 : ℝ)^4351
        have hw : |(-613644553/5000000000 : ℝ)|=(613644553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460654949/10000000000 : ℝ)|^5375 ≤ (47359352644919/100000000000000 : ℝ)^4351
        have hw : |(5460654949/10000000000 : ℝ)|=(5460654949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s3_6 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626744161/5000000000 : ℝ)*x 0 + (682581827/1250000000 : ℝ)*x 1 + (-613644577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626744161/5000000000 : ℝ)^5375 ≤ (45149782082773/100000000000000 : ℝ)^4351 := by
    have hnat : (2626744161 : ℕ)^5375*100000000000000^4351 ≤ 45149782082773^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626744161 5000000000 45149782082773 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682581827/1250000000 : ℝ)^5375 ≤ (2959959317323/6250000000000 : ℝ)^4351 := by
    have hnat : (682581827 : ℕ)^5375*6250000000000^4351 ≤ 2959959317323^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682581827 1250000000 2959959317323 6250000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (613644577/5000000000 : ℝ)^5375 ≤ (7490868822931/100000000000000 : ℝ)^4351 := by
    have hnat : (613644577 : ℕ)^5375*100000000000000^4351 ≤ 7490868822931^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613644577 5000000000 7490868822931 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626744161/5000000000 : ℝ), (682581827/1250000000 : ℝ), (-613644577/5000000000 : ℝ)] ![(45149782082773/100000000000000 : ℝ), (2959959317323/6250000000000 : ℝ), (7490868822931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626744161/5000000000 : ℝ)|^5375 ≤ (45149782082773/100000000000000 : ℝ)^4351
        have hw : |(2626744161/5000000000 : ℝ)|=(2626744161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682581827/1250000000 : ℝ)|^5375 ≤ (2959959317323/6250000000000 : ℝ)^4351
        have hw : |(682581827/1250000000 : ℝ)|=(682581827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-613644577/5000000000 : ℝ)|^5375 ≤ (7490868822931/100000000000000 : ℝ)^4351
        have hw : |(-613644577/5000000000 : ℝ)|=(613644577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s3_7 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2046875867/5000000000 : ℝ)*x 0 + (916171439/2000000000 : ℝ)*x 1 + (3640845603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046875867/5000000000 : ℝ)^5375 ≤ (33176838325801/100000000000000 : ℝ)^4351 := by
    have hnat : (2046875867 : ℕ)^5375*100000000000000^4351 ≤ 33176838325801^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046875867 5000000000 33176838325801 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916171439/2000000000 : ℝ)^5375 ≤ (9529962504253/25000000000000 : ℝ)^4351 := by
    have hnat : (916171439 : ℕ)^5375*25000000000000^4351 ≤ 9529962504253^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916171439 2000000000 9529962504253 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3640845603/10000000000 : ℝ)^5375 ≤ (14351655821549/50000000000000 : ℝ)^4351 := by
    have hnat : (3640845603 : ℕ)^5375*50000000000000^4351 ≤ 14351655821549^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3640845603 10000000000 14351655821549 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2046875867/5000000000 : ℝ), (916171439/2000000000 : ℝ), (3640845603/10000000000 : ℝ)] ![(33176838325801/100000000000000 : ℝ), (9529962504253/25000000000000 : ℝ), (14351655821549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2046875867/5000000000 : ℝ)|^5375 ≤ (33176838325801/100000000000000 : ℝ)^4351
        have hw : |(2046875867/5000000000 : ℝ)|=(2046875867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916171439/2000000000 : ℝ)|^5375 ≤ (9529962504253/25000000000000 : ℝ)^4351
        have hw : |(916171439/2000000000 : ℝ)|=(916171439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3640845603/10000000000 : ℝ)|^5375 ≤ (14351655821549/50000000000000 : ℝ)^4351
        have hw : |(3640845603/10000000000 : ℝ)|=(3640845603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1719_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4259/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10079/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4257/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4259/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1259/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4259/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1259/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4259/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1259/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4259/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1259/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4259/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1259/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4259/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1259/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1259/12500 : ℝ) ^ (5367/1024 : ℝ) ≤ (595825646703521/100000000000000000000 : ℝ) := by
    have hpowers : (1259/12500 : ℝ)^5367 ≤ (595825646703521/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1259 : ℕ)^5367*100000000000000000000^1024 ≤ 595825646703521^1024*12500^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1259 12500 595825646703521 100000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1259/12500 : ℝ)) (X := (595825646703521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4259/25000 : ℝ) ^ (5367/1024 : ℝ) ≤ (9363444115168307/100000000000000000000 : ℝ) := by
    have hpowers : (4259/25000 : ℝ)^5367 ≤ (9363444115168307/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4259 : ℕ)^5367*100000000000000000000^1024 ≤ 9363444115168307^1024*25000^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4259 25000 9363444115168307 100000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4259/25000 : ℝ)) (X := (9363444115168307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000595825646703521/50000000000000000000 : ℝ) ≤ (500001136803653/500000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (50000595825646703521/50000000000000000000 : ℝ)^1024 ≤ (500001136803653/500000000000000 : ℝ)^5367 := by
      have hnat : (50000595825646703521 : ℕ)^1024*500000000000000^5367 ≤ 500001136803653^5367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000595825646703521 50000000000000000000 500001136803653 500000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500001136803653/500000000000000 : ℝ)) (X := (50000595825646703521/50000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25002489817440467957/25000000000000000000 : ℝ) ≤ (10000190010831309/10000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (25002489817440467957/25000000000000000000 : ℝ)^1024 ≤ (10000190010831309/10000000000000000 : ℝ)^5367 := by
      have hnat : (25002489817440467957 : ℕ)^1024*10000000000000000^5367 ≤ 10000190010831309^5367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002489817440467957 25000000000000000000 10000190010831309 10000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000190010831309/10000000000000000 : ℝ)) (X := (25002489817440467957/25000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009363444115168307/50000000000000000000 : ℝ) ≤ (5000178642794779/5000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (50009363444115168307/50000000000000000000 : ℝ)^1024 ≤ (5000178642794779/5000000000000000 : ℝ)^5367 := by
      have hnat : (50009363444115168307 : ℕ)^1024*5000000000000000^5367 ≤ 5000178642794779^5367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009363444115168307 50000000000000000000 5000178642794779 5000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000178642794779/5000000000000000 : ℝ)) (X := (50009363444115168307/50000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(595825646703521/100000000000000000000 : ℝ) ≤ ((2176149648477581937/2176250000000000000 : ℝ)+2*(167274758249/696400000000000 : ℝ)*(1259/12500 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (2176149648477581937/2176250000000000000 : ℝ)+2*(167274758249/696400000000000 : ℝ)*(1259/12500 : ℝ)=(500001136803653/500000000000000 : ℝ) by norm_num, show 1+2*(595825646703521/100000000000000000000 : ℝ)=(50000595825646703521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9363444115168307/100000000000000000000 : ℝ)+(595825646703521/100000000000000000000 : ℝ) ≤ ((2176149648477581937/2176250000000000000 : ℝ)+(167274758249/696400000000000 : ℝ)*((4259/25000 : ℝ)+(1259/12500 : ℝ)))^(5367/1024 : ℝ) := by
    rw [show (2176149648477581937/2176250000000000000 : ℝ)+(167274758249/696400000000000 : ℝ)*((4259/25000 : ℝ)+(1259/12500 : ℝ))=(10000190010831309/10000000000000000 : ℝ) by norm_num, show 1+(9363444115168307/100000000000000000000 : ℝ)+(595825646703521/100000000000000000000 : ℝ)=(25002489817440467957/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9363444115168307/100000000000000000000 : ℝ) ≤ ((2176149648477581937/2176250000000000000 : ℝ)+2*(167274758249/696400000000000 : ℝ)*(4259/25000 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (2176149648477581937/2176250000000000000 : ℝ)+2*(167274758249/696400000000000 : ℝ)*(4259/25000 : ℝ)=(5000178642794779/5000000000000000 : ℝ) by norm_num, show 1+2*(9363444115168307/100000000000000000000 : ℝ)=(50009363444115168307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2176149648477581937/2176250000000000000 : ℝ)*(X 1 0+X 2 0)+(167274758249/696400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (4259/25000 : ℝ)) (c := (2176149648477581937/2176250000000000000 : ℝ)) (alpha := (167274758249/696400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2176149648477581937/2176250000000000000 : ℝ)*(X 0 1+X 2 1)+(167274758249/696400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (4259/25000 : ℝ)) (c := (2176149648477581937/2176250000000000000 : ℝ)) (alpha := (167274758249/696400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2176149648477581937/2176250000000000000 : ℝ)*(X 0 2+X 1 2)+(167274758249/696400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (4259/25000 : ℝ)) (c := (2176149648477581937/2176250000000000000 : ℝ)) (alpha := (167274758249/696400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1380213089/10000000000 : ℝ)*X 0 0+(5464335993/10000000000 : ℝ)*X 0 1+(2569664607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5340490811/10000000000 : ℝ)*X 1 0+(-387153567/2500000000 : ℝ)*X 1 1+(5139329193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83445169/156250000 : ℝ)*X 2 0+(642416147/1250000000 : ℝ)*X 2 1+(-1548614283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4093320613/10000000000 : ℝ)*X 0 0+(1814976073/5000000000 : ℝ)*X 0 1+(4591590729/10000000000 : ℝ)*X 0 2+(4093320613/10000000000 : ℝ)*X 1 0+(1814976073/5000000000 : ℝ)*X 1 1+(4591590729/10000000000 : ℝ)*X 1 2+(4093320613/10000000000 : ℝ)*X 2 0+(1814976073/5000000000 : ℝ)*X 2 1+(4591590729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21568111/156250000 : ℝ)*X 0 0+(1285739253/2500000000 : ℝ)*X 0 1+(5460653961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262674401/500000000 : ℝ)*X 1 0+(-613644553/5000000000 : ℝ)*X 1 1+(5460654949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626744161/5000000000 : ℝ)*X 2 0+(682581827/1250000000 : ℝ)*X 2 1+(-613644577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2046875867/5000000000 : ℝ)*X 0 0+(916171439/2000000000 : ℝ)*X 0 1+(3640845603/10000000000 : ℝ)*X 0 2+(2046875867/5000000000 : ℝ)*X 1 0+(916171439/2000000000 : ℝ)*X 1 1+(3640845603/10000000000 : ℝ)*X 1 2+(2046875867/5000000000 : ℝ)*X 2 0+(916171439/2000000000 : ℝ)*X 2 1+(3640845603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (345673770150795180464253/34820000000000000000000000000 : ℝ) := by norm_num
    linear_combination (384576299/25000000000000 : ℝ)*(base19) + (1443316159/100000000000000 : ℝ)*(base23) + (13066813/25000000000000 : ℝ)*(lower2) + (9672427/4000000000000 : ℝ)*(upper3) + (6516221/4000000000000 : ℝ)*(upper5) + (2058396559412479/100000000000000 : ℝ)*(major0) + (2058396559412479/100000000000000 : ℝ)*(major1) + (2058396559412479/100000000000000 : ℝ)*(major2) + (1538437469206459/50000000000000 : ℝ)*(sp0) + (3076888943491031/100000000000000 : ℝ)*(sp1) + (769222259620017/25000000000000 : ℝ)*(sp2) + (103989663950557/10000000000000 : ℝ)*(sp3) + (1554338331/10000000000000 : ℝ)*(sp4) + (566660819/10000000000000 : ℝ)*(sp7) + (6499389413211/625000000000 : ℝ)*(f.failure) + (769222620449057/25000000000000 : ℝ)*(f.sum) + (97626832663689/34820000000000000000000000000 : ℝ)*base66 + (526628149048118151/108812500000000000000000000000000 : ℝ)*base68 + (356033967886743151/108812500000000000000000000000000 : ℝ)*base70 + (403422272062694349/108812500000000000000000000000000 : ℝ)*base71 + (27334724887569/34820000000000000000000000000 : ℝ)*base74 + (341803377665694349/108812500000000000000000000000000 : ℝ)*base75 + (79339546882743151/108812500000000000000000000000000 : ℝ)*base78 + (596856922862256849/108812500000000000000000000000000 : ℝ)*base79 + (19522970643351/34820000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16613/3125000000000000000 : ℝ)*base90 + (16613/3125000000000000000 : ℝ)*base92 + (16613/3125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72152260076894949015777123/13601562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (41272677/10000000000000 : ℝ)*(base19) + (381188069/50000000000000 : ℝ)*(base23) + (290908207/100000000000000 : ℝ)*(lower1) + (3294709/5000000000000 : ℝ)*(upper2) + (207429731/100000000000000 : ℝ)*(upper3) + (44982041/50000000000000 : ℝ)*(upper5) + (526432033391461/25000000000000 : ℝ)*(major0) + (526432033391461/25000000000000 : ℝ)*(major1) + (526432033391461/25000000000000 : ℝ)*(major2) + (1306568067/50000000000000 : ℝ)*(sp2) + (3147641864555357/100000000000000 : ℝ)*(sp4) + (786910362957147/25000000000000 : ℝ)*(sp5) + (786909622260771/25000000000000 : ℝ)*(sp6) + (33244194554777/3125000000000 : ℝ)*(sp7) + (33244194554777/3125000000000 : ℝ)*(f.failure) + (3147641864555357/100000000000000 : ℝ)*(f.sum) + (31352537436051/8705000000000000000000000000 : ℝ)*base66 + (53523911062322209/27203125000000000000000000000000 : ℝ)*base68 + (105075757695262667/13601562500000000000000000000000 : ℝ)*base70 + (69448951553759709/27203125000000000000000000000000 : ℝ)*base72 + (22699315681371/8705000000000000000000000000 : ℝ)*base74 + (440182852419197209/27203125000000000000000000000000 : ℝ)*base76 + (7206880410115291/27203125000000000000000000000000 : ℝ)*base77 + (249839679490740291/27203125000000000000000000000000 : ℝ)*base79 + (86914794774681/8705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (14059/15625000000000000000 : ℝ)*base89 + (14059/15625000000000000000 : ℝ)*base91 + (14059/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1719_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4259/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4257/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1719_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1719_box_0 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-267101647/2500000000 : ℝ)*x 0 + (54125143/100000000 : ℝ)*x 1 + (5412514559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267101647/2500000000 : ℝ)^5375 ≤ (6311774266099/100000000000000 : ℝ)^4351 := by
    have hnat : (267101647 : ℕ)^5375*100000000000000^4351 ≤ 6311774266099^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267101647 2500000000 6311774266099 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54125143/100000000 : ℝ)^5375 ≤ (46844111474241/100000000000000 : ℝ)^4351 := by
    have hnat : (54125143 : ℕ)^5375*100000000000000^4351 ≤ 46844111474241^4351*100000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54125143 100000000 46844111474241 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412514559/10000000000 : ℝ)^5375 ≤ (23422057121691/50000000000000 : ℝ)^4351 := by
    have hnat : (5412514559 : ℕ)^5375*50000000000000^4351 ≤ 23422057121691^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412514559 10000000000 23422057121691 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267101647/2500000000 : ℝ), (54125143/100000000 : ℝ), (5412514559/10000000000 : ℝ)] ![(6311774266099/100000000000000 : ℝ), (46844111474241/100000000000000 : ℝ), (23422057121691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267101647/2500000000 : ℝ)|^5375 ≤ (6311774266099/100000000000000 : ℝ)^4351
        have hw : |(-267101647/2500000000 : ℝ)|=(267101647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54125143/100000000 : ℝ)|^5375 ≤ (46844111474241/100000000000000 : ℝ)^4351
        have hw : |(54125143/100000000 : ℝ)|=(54125143/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412514559/10000000000 : ℝ)|^5375 ≤ (23422057121691/50000000000000 : ℝ)^4351
        have hw : |(5412514559/10000000000 : ℝ)|=(5412514559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_1 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653114199/1250000000 : ℝ)*x 0 + (-1334747937/10000000000 : ℝ)*x 1 + (2706257323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653114199/1250000000 : ℝ)^5375 ≤ (22423300897269/50000000000000 : ℝ)^4351 := by
    have hnat : (653114199 : ℕ)^5375*50000000000000^4351 ≤ 22423300897269^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653114199 1250000000 22423300897269 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1334747937/10000000000 : ℝ)^5375 ≤ (8309283021177/100000000000000 : ℝ)^4351 := by
    have hnat : (1334747937 : ℕ)^5375*100000000000000^4351 ≤ 8309283021177^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334747937 10000000000 8309283021177 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706257323/5000000000 : ℝ)^5375 ≤ (46844115173557/100000000000000 : ℝ)^4351 := by
    have hnat : (2706257323 : ℕ)^5375*100000000000000^4351 ≤ 46844115173557^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706257323 5000000000 46844115173557 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653114199/1250000000 : ℝ), (-1334747937/10000000000 : ℝ), (2706257323/5000000000 : ℝ)] ![(22423300897269/50000000000000 : ℝ), (8309283021177/100000000000000 : ℝ), (46844115173557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653114199/1250000000 : ℝ)|^5375 ≤ (22423300897269/50000000000000 : ℝ)^4351
        have hw : |(653114199/1250000000 : ℝ)|=(653114199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1334747937/10000000000 : ℝ)|^5375 ≤ (8309283021177/100000000000000 : ℝ)^4351
        have hw : |(-1334747937/10000000000 : ℝ)|=(1334747937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706257323/5000000000 : ℝ)|^5375 ≤ (46844115173557/100000000000000 : ℝ)^4351
        have hw : |(2706257323/5000000000 : ℝ)|=(2706257323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_2 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224914053/10000000000 : ℝ)*x 0 + (135312853/250000000 : ℝ)*x 1 + (-1334748031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224914053/10000000000 : ℝ)^5375 ≤ (8969321336529/20000000000000 : ℝ)^4351 := by
    have hnat : (5224914053 : ℕ)^5375*20000000000000^4351 ≤ 8969321336529^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224914053 10000000000 8969321336529 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135312853/250000000 : ℝ)^5375 ≤ (46844109549741/100000000000000 : ℝ)^4351 := by
    have hnat : (135312853 : ℕ)^5375*100000000000000^4351 ≤ 46844109549741^4351*250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135312853 250000000 46844109549741 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1334748031/10000000000 : ℝ)^5375 ≤ (8309283744083/100000000000000 : ℝ)^4351 := by
    have hnat : (1334748031 : ℕ)^5375*100000000000000^4351 ≤ 8309283744083^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334748031 10000000000 8309283744083 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224914053/10000000000 : ℝ), (135312853/250000000 : ℝ), (-1334748031/10000000000 : ℝ)] ![(8969321336529/20000000000000 : ℝ), (46844109549741/100000000000000 : ℝ), (8309283744083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224914053/10000000000 : ℝ)|^5375 ≤ (8969321336529/20000000000000 : ℝ)^4351
        have hw : |(5224914053/10000000000 : ℝ)|=(5224914053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135312853/250000000 : ℝ)|^5375 ≤ (46844109549741/100000000000000 : ℝ)^4351
        have hw : |(135312853/250000000 : ℝ)|=(135312853/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1334748031/10000000000 : ℝ)|^5375 ≤ (8309283744083/100000000000000 : ℝ)^4351
        have hw : |(-1334748031/10000000000 : ℝ)|=(1334748031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_3 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4474268077/10000000000 : ℝ)*x 0 + (1962035201/5000000000 : ℝ)*x 1 + (1962035287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4474268077/10000000000 : ℝ)^5375 ≤ (37027130318617/100000000000000 : ℝ)^4351 := by
    have hnat : (4474268077 : ℕ)^5375*100000000000000^4351 ≤ 37027130318617^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474268077 10000000000 37027130318617 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1962035201/5000000000 : ℝ)^5375 ≤ (6297286796381/20000000000000 : ℝ)^4351 := by
    have hnat : (1962035201 : ℕ)^5375*20000000000000^4351 ≤ 6297286796381^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962035201 5000000000 6297286796381 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1962035287/5000000000 : ℝ)^5375 ≤ (31486435686827/100000000000000 : ℝ)^4351 := by
    have hnat : (1962035287 : ℕ)^5375*100000000000000^4351 ≤ 31486435686827^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962035287 5000000000 31486435686827 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4474268077/10000000000 : ℝ), (1962035201/5000000000 : ℝ), (1962035287/5000000000 : ℝ)] ![(37027130318617/100000000000000 : ℝ), (6297286796381/20000000000000 : ℝ), (31486435686827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4474268077/10000000000 : ℝ)|^5375 ≤ (37027130318617/100000000000000 : ℝ)^4351
        have hw : |(4474268077/10000000000 : ℝ)|=(4474268077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1962035201/5000000000 : ℝ)|^5375 ≤ (6297286796381/20000000000000 : ℝ)^4351
        have hw : |(1962035201/5000000000 : ℝ)|=(1962035201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1962035287/5000000000 : ℝ)|^5375 ≤ (31486435686827/100000000000000 : ℝ)^4351
        have hw : |(1962035287/5000000000 : ℝ)|=(1962035287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_4 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107031971/625000000 : ℝ)*x 0 + (2588896479/5000000000 : ℝ)*x 1 + (5177792951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107031971/625000000 : ℝ)^5375 ≤ (1130499914797/10000000000000 : ℝ)^4351 := by
    have hnat : (107031971 : ℕ)^5375*10000000000000^4351 ≤ 1130499914797^4351*625000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107031971 625000000 1130499914797 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588896479/5000000000 : ℝ)^5375 ≤ (22173750225573/50000000000000 : ℝ)^4351 := by
    have hnat : (2588896479 : ℕ)^5375*50000000000000^4351 ≤ 22173750225573^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588896479 5000000000 22173750225573 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177792951/10000000000 : ℝ)^5375 ≤ (44347500377081/100000000000000 : ℝ)^4351 := by
    have hnat : (5177792951 : ℕ)^5375*100000000000000^4351 ≤ 44347500377081^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177792951 10000000000 44347500377081 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107031971/625000000 : ℝ), (2588896479/5000000000 : ℝ), (5177792951/10000000000 : ℝ)] ![(1130499914797/10000000000000 : ℝ), (22173750225573/50000000000000 : ℝ), (44347500377081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107031971/625000000 : ℝ)|^5375 ≤ (1130499914797/10000000000000 : ℝ)^4351
        have hw : |(-107031971/625000000 : ℝ)|=(107031971/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588896479/5000000000 : ℝ)|^5375 ≤ (22173750225573/50000000000000 : ℝ)^4351
        have hw : |(2588896479/5000000000 : ℝ)|=(2588896479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177792951/10000000000 : ℝ)|^5375 ≤ (44347500377081/100000000000000 : ℝ)^4351
        have hw : |(5177792951/10000000000 : ℝ)|=(5177792951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_5 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383757437/10000000000 : ℝ)*x 0 + (-719333677/5000000000 : ℝ)*x 1 + (2588896441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383757437/10000000000 : ℝ)^5375 ≤ (727138206571/1562500000000 : ℝ)^4351 := by
    have hnat : (5383757437 : ℕ)^5375*1562500000000^4351 ≤ 727138206571^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383757437 10000000000 727138206571 1562500000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719333677/5000000000 : ℝ)^5375 ≤ (4557827556521/50000000000000 : ℝ)^4351 := by
    have hnat : (719333677 : ℕ)^5375*50000000000000^4351 ≤ 4557827556521^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719333677 5000000000 4557827556521 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588896441/5000000000 : ℝ)^5375 ≤ (22173749823507/50000000000000 : ℝ)^4351 := by
    have hnat : (2588896441 : ℕ)^5375*50000000000000^4351 ≤ 22173749823507^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588896441 5000000000 22173749823507 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383757437/10000000000 : ℝ), (-719333677/5000000000 : ℝ), (2588896441/5000000000 : ℝ)] ![(727138206571/1562500000000 : ℝ), (4557827556521/50000000000000 : ℝ), (22173749823507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383757437/10000000000 : ℝ)|^5375 ≤ (727138206571/1562500000000 : ℝ)^4351
        have hw : |(5383757437/10000000000 : ℝ)|=(5383757437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-719333677/5000000000 : ℝ)|^5375 ≤ (4557827556521/50000000000000 : ℝ)^4351
        have hw : |(-719333677/5000000000 : ℝ)|=(719333677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588896441/5000000000 : ℝ)|^5375 ≤ (22173749823507/50000000000000 : ℝ)^4351
        have hw : |(2588896441/5000000000 : ℝ)|=(2588896441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_6 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84121209/156250000 : ℝ)*x 0 + (5177792987/10000000000 : ℝ)*x 1 + (-44958353/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84121209/156250000 : ℝ)^5375 ≤ (4653684456917/10000000000000 : ℝ)^4351 := by
    have hnat : (84121209 : ℕ)^5375*10000000000000^4351 ≤ 4653684456917^4351*156250000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84121209 156250000 4653684456917 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177792987/10000000000 : ℝ)^5375 ≤ (22173750378993/50000000000000 : ℝ)^4351 := by
    have hnat : (5177792987 : ℕ)^5375*50000000000000^4351 ≤ 22173750378993^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177792987 10000000000 22173750378993 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44958353/312500000 : ℝ)^5375 ≤ (9115654659053/100000000000000 : ℝ)^4351 := by
    have hnat : (44958353 : ℕ)^5375*100000000000000^4351 ≤ 9115654659053^4351*312500000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44958353 312500000 9115654659053 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84121209/156250000 : ℝ), (5177792987/10000000000 : ℝ), (-44958353/312500000 : ℝ)] ![(4653684456917/10000000000000 : ℝ), (22173750378993/50000000000000 : ℝ), (9115654659053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84121209/156250000 : ℝ)|^5375 ≤ (4653684456917/10000000000000 : ℝ)^4351
        have hw : |(84121209/156250000 : ℝ)|=(84121209/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177792987/10000000000 : ℝ)|^5375 ≤ (22173750378993/50000000000000 : ℝ)^4351
        have hw : |(5177792987/10000000000 : ℝ)|=(5177792987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44958353/312500000 : ℝ)|^5375 ≤ (9115654659053/100000000000000 : ℝ)^4351
        have hw : |(-44958353/312500000 : ℝ)|=(44958353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_7 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1848131183/5000000000 : ℝ)*x 0 + (269516233/625000000 : ℝ)*x 1 + (2156129889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1848131183/5000000000 : ℝ)^5375 ≤ (5848796873293/20000000000000 : ℝ)^4351 := by
    have hnat : (1848131183 : ℕ)^5375*20000000000000^4351 ≤ 5848796873293^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848131183 5000000000 5848796873293 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269516233/625000000 : ℝ)^5375 ≤ (8844501888873/25000000000000 : ℝ)^4351 := by
    have hnat : (269516233 : ℕ)^5375*25000000000000^4351 ≤ 8844501888873^4351*625000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269516233 625000000 8844501888873 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156129889/5000000000 : ℝ)^5375 ≤ (7075601612447/20000000000000 : ℝ)^4351 := by
    have hnat : (2156129889 : ℕ)^5375*20000000000000^4351 ≤ 7075601612447^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156129889 5000000000 7075601612447 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1848131183/5000000000 : ℝ), (269516233/625000000 : ℝ), (2156129889/5000000000 : ℝ)] ![(5848796873293/20000000000000 : ℝ), (8844501888873/25000000000000 : ℝ), (7075601612447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1848131183/5000000000 : ℝ)|^5375 ≤ (5848796873293/20000000000000 : ℝ)^4351
        have hw : |(1848131183/5000000000 : ℝ)|=(1848131183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269516233/625000000 : ℝ)|^5375 ≤ (8844501888873/25000000000000 : ℝ)^4351
        have hw : |(269516233/625000000 : ℝ)|=(269516233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2156129889/5000000000 : ℝ)|^5375 ≤ (7075601612447/20000000000000 : ℝ)^4351
        have hw : |(2156129889/5000000000 : ℝ)|=(2156129889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_8 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-786929321/5000000000 : ℝ)*x 0 + (2502055847/5000000000 : ℝ)*x 1 + (5454887499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (786929321/5000000000 : ℝ)^5375 ≤ (1018528193031/10000000000000 : ℝ)^4351 := by
    have hnat : (786929321 : ℕ)^5375*10000000000000^4351 ≤ 1018528193031^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786929321 5000000000 1018528193031 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2502055847/5000000000 : ℝ)^5375 ≤ (42517150016447/100000000000000 : ℝ)^4351 := by
    have hnat : (2502055847 : ℕ)^5375*100000000000000^4351 ≤ 42517150016447^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502055847 5000000000 42517150016447 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454887499/10000000000 : ℝ)^5375 ≤ (9459513608637/20000000000000 : ℝ)^4351 := by
    have hnat : (5454887499 : ℕ)^5375*20000000000000^4351 ≤ 9459513608637^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454887499 10000000000 9459513608637 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-786929321/5000000000 : ℝ), (2502055847/5000000000 : ℝ), (5454887499/10000000000 : ℝ)] ![(1018528193031/10000000000000 : ℝ), (42517150016447/100000000000000 : ℝ), (9459513608637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-786929321/5000000000 : ℝ)|^5375 ≤ (1018528193031/10000000000000 : ℝ)^4351
        have hw : |(-786929321/5000000000 : ℝ)|=(786929321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2502055847/5000000000 : ℝ)|^5375 ≤ (42517150016447/100000000000000 : ℝ)^4351
        have hw : |(2502055847/5000000000 : ℝ)|=(2502055847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454887499/10000000000 : ℝ)|^5375 ≤ (9459513608637/20000000000000 : ℝ)^4351
        have hw : |(5454887499/10000000000 : ℝ)|=(5454887499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_9 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649532467/1250000000 : ℝ)*x 0 + (-657615833/5000000000 : ℝ)*x 1 + (170465251/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649532467/1250000000 : ℝ)^5375 ≤ (44542973571099/100000000000000 : ℝ)^4351 := by
    have hnat : (649532467 : ℕ)^5375*100000000000000^4351 ≤ 44542973571099^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649532467 1250000000 44542973571099 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657615833/5000000000 : ℝ)^5375 ≤ (4079726330637/50000000000000 : ℝ)^4351 := by
    have hnat : (657615833 : ℕ)^5375*50000000000000^4351 ≤ 4079726330637^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657615833 5000000000 4079726330637 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170465251/312500000 : ℝ)^5375 ≤ (47297573752311/100000000000000 : ℝ)^4351 := by
    have hnat : (170465251 : ℕ)^5375*100000000000000^4351 ≤ 47297573752311^4351*312500000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170465251 312500000 47297573752311 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649532467/1250000000 : ℝ), (-657615833/5000000000 : ℝ), (170465251/312500000 : ℝ)] ![(44542973571099/100000000000000 : ℝ), (4079726330637/50000000000000 : ℝ), (47297573752311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649532467/1250000000 : ℝ)|^5375 ≤ (44542973571099/100000000000000 : ℝ)^4351
        have hw : |(649532467/1250000000 : ℝ)|=(649532467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-657615833/5000000000 : ℝ)|^5375 ≤ (4079726330637/50000000000000 : ℝ)^4351
        have hw : |(-657615833/5000000000 : ℝ)|=(657615833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170465251/312500000 : ℝ)|^5375 ≤ (47297573752311/100000000000000 : ℝ)^4351
        have hw : |(170465251/312500000 : ℝ)|=(170465251/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_10 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196260841/10000000000 : ℝ)*x 0 + (5454887391/10000000000 : ℝ)*x 1 + (-263046207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196260841/10000000000 : ℝ)^5375 ≤ (22271492636279/50000000000000 : ℝ)^4351 := by
    have hnat : (5196260841 : ℕ)^5375*50000000000000^4351 ≤ 22271492636279^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196260841 10000000000 22271492636279 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454887391/10000000000 : ℝ)^5375 ≤ (11824391721591/25000000000000 : ℝ)^4351 := by
    have hnat : (5454887391 : ℕ)^5375*25000000000000^4351 ≤ 11824391721591^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454887391 10000000000 11824391721591 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263046207/2000000000 : ℝ)^5375 ≤ (2039861956343/25000000000000 : ℝ)^4351 := by
    have hnat : (263046207 : ℕ)^5375*25000000000000^4351 ≤ 2039861956343^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263046207 2000000000 2039861956343 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196260841/10000000000 : ℝ), (5454887391/10000000000 : ℝ), (-263046207/2000000000 : ℝ)] ![(22271492636279/50000000000000 : ℝ), (11824391721591/25000000000000 : ℝ), (2039861956343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196260841/10000000000 : ℝ)|^5375 ≤ (22271492636279/50000000000000 : ℝ)^4351
        have hw : |(5196260841/10000000000 : ℝ)|=(5196260841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454887391/10000000000 : ℝ)|^5375 ≤ (11824391721591/25000000000000 : ℝ)^4351
        have hw : |(5454887391/10000000000 : ℝ)|=(5454887391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263046207/2000000000 : ℝ)|^5375 ≤ (2039861956343/25000000000000 : ℝ)^4351
        have hw : |(-263046207/2000000000 : ℝ)|=(263046207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_11 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4609753273/10000000000 : ℝ)*x 0 + (1926904403/5000000000 : ℝ)*x 1 + (770761247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4609753273/10000000000 : ℝ)^5375 ≤ (19208561161571/50000000000000 : ℝ)^4351 := by
    have hnat : (4609753273 : ℕ)^5375*50000000000000^4351 ≤ 19208561161571^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609753273 10000000000 19208561161571 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926904403/5000000000 : ℝ)^5375 ≤ (6158290303893/20000000000000 : ℝ)^4351 := by
    have hnat : (1926904403 : ℕ)^5375*20000000000000^4351 ≤ 6158290303893^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926904403 5000000000 6158290303893 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (770761247/2000000000 : ℝ)^5375 ≤ (15395713071491/50000000000000 : ℝ)^4351 := by
    have hnat : (770761247 : ℕ)^5375*50000000000000^4351 ≤ 15395713071491^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770761247 2000000000 15395713071491 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4609753273/10000000000 : ℝ), (1926904403/5000000000 : ℝ), (770761247/2000000000 : ℝ)] ![(19208561161571/50000000000000 : ℝ), (6158290303893/20000000000000 : ℝ), (15395713071491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4609753273/10000000000 : ℝ)|^5375 ≤ (19208561161571/50000000000000 : ℝ)^4351
        have hw : |(4609753273/10000000000 : ℝ)|=(4609753273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1926904403/5000000000 : ℝ)|^5375 ≤ (6158290303893/20000000000000 : ℝ)^4351
        have hw : |(1926904403/5000000000 : ℝ)|=(1926904403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(770761247/2000000000 : ℝ)|^5375 ≤ (15395713071491/50000000000000 : ℝ)^4351
        have hw : |(770761247/2000000000 : ℝ)|=(770761247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_12 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-75084853/625000000 : ℝ)*x 0 + (1115628253/2000000000 : ℝ)*x 1 + (5152770881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75084853/625000000 : ℝ)^5375 ≤ (1823958138021/25000000000000 : ℝ)^4351 := by
    have hnat : (75084853 : ℕ)^5375*25000000000000^4351 ≤ 1823958138021^4351*625000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75084853 625000000 1823958138021 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115628253/2000000000 : ℝ)^5375 ≤ (9724253398229/20000000000000 : ℝ)^4351 := by
    have hnat : (1115628253 : ℕ)^5375*20000000000000^4351 ≤ 9724253398229^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115628253 2000000000 9724253398229 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152770881/10000000000 : ℝ)^5375 ≤ (2204145021861/5000000000000 : ℝ)^4351 := by
    have hnat : (5152770881 : ℕ)^5375*5000000000000^4351 ≤ 2204145021861^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152770881 10000000000 2204145021861 5000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-75084853/625000000 : ℝ), (1115628253/2000000000 : ℝ), (5152770881/10000000000 : ℝ)] ![(1823958138021/25000000000000 : ℝ), (9724253398229/20000000000000 : ℝ), (2204145021861/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-75084853/625000000 : ℝ)|^5375 ≤ (1823958138021/25000000000000 : ℝ)^4351
        have hw : |(-75084853/625000000 : ℝ)|=(75084853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115628253/2000000000 : ℝ)|^5375 ≤ (9724253398229/20000000000000 : ℝ)^4351
        have hw : |(1115628253/2000000000 : ℝ)|=(1115628253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152770881/10000000000 : ℝ)|^5375 ≤ (2204145021861/5000000000000 : ℝ)^4351
        have hw : |(5152770881/10000000000 : ℝ)|=(5152770881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_13 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350180661/2500000000 : ℝ)*x 0 + (-1449309303/10000000000 : ℝ)*x 1 + (5032003/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350180661/2500000000 : ℝ)^5375 ≤ (11679517844819/25000000000000 : ℝ)^4351 := by
    have hnat : (1350180661 : ℕ)^5375*25000000000000^4351 ≤ 11679517844819^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350180661 2500000000 11679517844819 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1449309303/10000000000 : ℝ)^5375 ≤ (9199026151453/100000000000000 : ℝ)^4351 := by
    have hnat : (1449309303 : ℕ)^5375*100000000000000^4351 ≤ 9199026151453^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449309303 10000000000 9199026151453 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5032003/9765625 : ℝ)^5375 ≤ (11020725613957/25000000000000 : ℝ)^4351 := by
    have hnat : (5032003 : ℕ)^5375*25000000000000^4351 ≤ 11020725613957^4351*9765625^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032003 9765625 11020725613957 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350180661/2500000000 : ℝ), (-1449309303/10000000000 : ℝ), (5032003/9765625 : ℝ)] ![(11679517844819/25000000000000 : ℝ), (9199026151453/100000000000000 : ℝ), (11020725613957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350180661/2500000000 : ℝ)|^5375 ≤ (11679517844819/25000000000000 : ℝ)^4351
        have hw : |(1350180661/2500000000 : ℝ)|=(1350180661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1449309303/10000000000 : ℝ)|^5375 ≤ (9199026151453/100000000000000 : ℝ)^4351
        have hw : |(-1449309303/10000000000 : ℝ)|=(1449309303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5032003/9765625 : ℝ)|^5375 ≤ (11020725613957/25000000000000 : ℝ)^4351
        have hw : |(5032003/9765625 : ℝ)|=(5032003/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_14 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400722727/10000000000 : ℝ)*x 0 + (5152770821/10000000000 : ℝ)*x 1 + (-181163691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400722727/10000000000 : ℝ)^5375 ≤ (46718072266229/100000000000000 : ℝ)^4351 := by
    have hnat : (5400722727 : ℕ)^5375*100000000000000^4351 ≤ 46718072266229^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400722727 10000000000 46718072266229 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152770821/10000000000 : ℝ)^5375 ≤ (22041449901551/50000000000000 : ℝ)^4351 := by
    have hnat : (5152770821 : ℕ)^5375*50000000000000^4351 ≤ 22041449901551^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152770821 10000000000 22041449901551 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181163691/1250000000 : ℝ)^5375 ≤ (9199027915673/100000000000000 : ℝ)^4351 := by
    have hnat : (181163691 : ℕ)^5375*100000000000000^4351 ≤ 9199027915673^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181163691 1250000000 9199027915673 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400722727/10000000000 : ℝ), (5152770821/10000000000 : ℝ), (-181163691/1250000000 : ℝ)] ![(46718072266229/100000000000000 : ℝ), (22041449901551/50000000000000 : ℝ), (9199027915673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400722727/10000000000 : ℝ)|^5375 ≤ (46718072266229/100000000000000 : ℝ)^4351
        have hw : |(5400722727/10000000000 : ℝ)|=(5400722727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152770821/10000000000 : ℝ)|^5375 ≤ (22041449901551/50000000000000 : ℝ)^4351
        have hw : |(5152770821/10000000000 : ℝ)|=(5152770821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181163691/1250000000 : ℝ)|^5375 ≤ (9199027915673/100000000000000 : ℝ)^4351
        have hw : |(-181163691/1250000000 : ℝ)|=(181163691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_box_15 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (722068259/2000000000 : ℝ)*x 0 + (2176764559/5000000000 : ℝ)*x 1 + (2176764829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (722068259/2000000000 : ℝ)^5375 ≤ (28406520457241/100000000000000 : ℝ)^4351 := by
    have hnat : (722068259 : ℕ)^5375*100000000000000^4351 ≤ 28406520457241^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722068259 2000000000 28406520457241 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176764559/5000000000 : ℝ)^5375 ≤ (447459212757/1250000000000 : ℝ)^4351 := by
    have hnat : (2176764559 : ℕ)^5375*1250000000000^4351 ≤ 447459212757^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176764559 5000000000 447459212757 1250000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176764829/5000000000 : ℝ)^5375 ≤ (8949185626417/25000000000000 : ℝ)^4351 := by
    have hnat : (2176764829 : ℕ)^5375*25000000000000^4351 ≤ 8949185626417^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176764829 5000000000 8949185626417 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(722068259/2000000000 : ℝ), (2176764559/5000000000 : ℝ), (2176764829/5000000000 : ℝ)] ![(28406520457241/100000000000000 : ℝ), (447459212757/1250000000000 : ℝ), (8949185626417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(722068259/2000000000 : ℝ)|^5375 ≤ (28406520457241/100000000000000 : ℝ)^4351
        have hw : |(722068259/2000000000 : ℝ)|=(722068259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2176764559/5000000000 : ℝ)|^5375 ≤ (447459212757/1250000000000 : ℝ)^4351
        have hw : |(2176764559/5000000000 : ℝ)|=(2176764559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2176764829/5000000000 : ℝ)|^5375 ≤ (8949185626417/25000000000000 : ℝ)^4351
        have hw : |(2176764829/5000000000 : ℝ)|=(2176764829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1719_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4257/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66833/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58613/100000 : ℝ) ∧ (81769/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (1811/2000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4257/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4257/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4257/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4257/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4257/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4257/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10079/100000 : ℝ) ^ (5367/1024 : ℝ) ≤ (298999607352871/50000000000000000000 : ℝ) := by
    have hpowers : (10079/100000 : ℝ)^5367 ≤ (298999607352871/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10079 : ℕ)^5367*50000000000000000000^1024 ≤ 298999607352871^1024*100000^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10079 100000 298999607352871 50000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10079/100000 : ℝ)) (X := (298999607352871/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4257/25000 : ℝ) ^ (5367/1024 : ℝ) ≤ (9340421368189173/100000000000000000000 : ℝ) := by
    have hpowers : (4257/25000 : ℝ)^5367 ≤ (9340421368189173/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4257 : ℕ)^5367*100000000000000000000^1024 ≤ 9340421368189173^1024*25000^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4257 25000 9340421368189173 100000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4257/25000 : ℝ)) (X := (9340421368189173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000298999607352871/25000000000000000000 : ℝ) ≤ (5000011409506851/5000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (25000298999607352871/25000000000000000000 : ℝ)^1024 ≤ (5000011409506851/5000000000000000 : ℝ)^5367 := by
      have hnat : (25000298999607352871 : ℕ)^1024*5000000000000000^5367 ≤ 5000011409506851^5367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000298999607352871 25000000000000000000 5000011409506851 5000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000011409506851/5000000000000000 : ℝ)) (X := (25000298999607352871/25000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001987684116578983/20000000000000000000 : ℝ) ≤ (2500047403267541/2500000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (20001987684116578983/20000000000000000000 : ℝ)^1024 ≤ (2500047403267541/2500000000000000 : ℝ)^5367 := by
      have hnat : (20001987684116578983 : ℕ)^1024*2500000000000000^5367 ≤ 2500047403267541^5367*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001987684116578983 20000000000000000000 2500047403267541 2500000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500047403267541/2500000000000000 : ℝ)) (X := (20001987684116578983/20000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009340421368189173/50000000000000000000 : ℝ) ≤ (5000178203563313/5000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (50009340421368189173/50000000000000000000 : ℝ)^1024 ≤ (5000178203563313/5000000000000000 : ℝ)^5367 := by
      have hnat : (50009340421368189173 : ℕ)^1024*5000000000000000^5367 ≤ 5000178203563313^5367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009340421368189173 50000000000000000000 5000178203563313 5000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000178203563313/5000000000000000 : ℝ)) (X := (50009340421368189173/50000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(298999607352871/50000000000000000000 : ℝ) ≤ ((34743398167368027101/34745000000000000000 : ℝ)+2*(83397028231/347450000000000 : ℝ)*(10079/100000 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (34743398167368027101/34745000000000000000 : ℝ)+2*(83397028231/347450000000000 : ℝ)*(10079/100000 : ℝ)=(5000011409506851/5000000000000000 : ℝ) by norm_num, show 1+2*(298999607352871/50000000000000000000 : ℝ)=(25000298999607352871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9340421368189173/100000000000000000000 : ℝ)+(298999607352871/50000000000000000000 : ℝ) ≤ ((34743398167368027101/34745000000000000000 : ℝ)+(83397028231/347450000000000 : ℝ)*((4257/25000 : ℝ)+(10079/100000 : ℝ)))^(5367/1024 : ℝ) := by
    rw [show (34743398167368027101/34745000000000000000 : ℝ)+(83397028231/347450000000000 : ℝ)*((4257/25000 : ℝ)+(10079/100000 : ℝ))=(2500047403267541/2500000000000000 : ℝ) by norm_num, show 1+(9340421368189173/100000000000000000000 : ℝ)+(298999607352871/50000000000000000000 : ℝ)=(20001987684116578983/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9340421368189173/100000000000000000000 : ℝ) ≤ ((34743398167368027101/34745000000000000000 : ℝ)+2*(83397028231/347450000000000 : ℝ)*(4257/25000 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (34743398167368027101/34745000000000000000 : ℝ)+2*(83397028231/347450000000000 : ℝ)*(4257/25000 : ℝ)=(5000178203563313/5000000000000000 : ℝ) by norm_num, show 1+2*(9340421368189173/100000000000000000000 : ℝ)=(50009340421368189173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34743398167368027101/34745000000000000000 : ℝ)*(X 1 0+X 2 0)+(83397028231/347450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (10079/100000 : ℝ)) (hi := (4257/25000 : ℝ)) (c := (34743398167368027101/34745000000000000000 : ℝ)) (alpha := (83397028231/347450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34743398167368027101/34745000000000000000 : ℝ)*(X 0 1+X 2 1)+(83397028231/347450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (10079/100000 : ℝ)) (hi := (4257/25000 : ℝ)) (c := (34743398167368027101/34745000000000000000 : ℝ)) (alpha := (83397028231/347450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34743398167368027101/34745000000000000000 : ℝ)*(X 0 2+X 1 2)+(83397028231/347450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (10079/100000 : ℝ)) (hi := (4257/25000 : ℝ)) (c := (34743398167368027101/34745000000000000000 : ℝ)) (alpha := (83397028231/347450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-267101647/2500000000 : ℝ)*X 0 0+(54125143/100000000 : ℝ)*X 0 1+(5412514559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((653114199/1250000000 : ℝ)*X 1 0+(-1334747937/10000000000 : ℝ)*X 1 1+(2706257323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5224914053/10000000000 : ℝ)*X 2 0+(135312853/250000000 : ℝ)*X 2 1+(-1334748031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4474268077/10000000000 : ℝ)*X 0 0+(1962035201/5000000000 : ℝ)*X 0 1+(1962035287/5000000000 : ℝ)*X 0 2+(4474268077/10000000000 : ℝ)*X 1 0+(1962035201/5000000000 : ℝ)*X 1 1+(1962035287/5000000000 : ℝ)*X 1 2+(4474268077/10000000000 : ℝ)*X 2 0+(1962035201/5000000000 : ℝ)*X 2 1+(1962035287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107031971/625000000 : ℝ)*X 0 0+(2588896479/5000000000 : ℝ)*X 0 1+(5177792951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5383757437/10000000000 : ℝ)*X 1 0+(-719333677/5000000000 : ℝ)*X 1 1+(2588896441/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((84121209/156250000 : ℝ)*X 2 0+(5177792987/10000000000 : ℝ)*X 2 1+(-44958353/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1848131183/5000000000 : ℝ)*X 0 0+(269516233/625000000 : ℝ)*X 0 1+(2156129889/5000000000 : ℝ)*X 0 2+(1848131183/5000000000 : ℝ)*X 1 0+(269516233/625000000 : ℝ)*X 1 1+(2156129889/5000000000 : ℝ)*X 1 2+(1848131183/5000000000 : ℝ)*X 2 0+(269516233/625000000 : ℝ)*X 2 1+(2156129889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-786929321/5000000000 : ℝ)*X 0 0+(2502055847/5000000000 : ℝ)*X 0 1+(5454887499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((649532467/1250000000 : ℝ)*X 1 0+(-657615833/5000000000 : ℝ)*X 1 1+(170465251/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196260841/10000000000 : ℝ)*X 2 0+(5454887391/10000000000 : ℝ)*X 2 1+(-263046207/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4609753273/10000000000 : ℝ)*X 0 0+(1926904403/5000000000 : ℝ)*X 0 1+(770761247/2000000000 : ℝ)*X 0 2+(4609753273/10000000000 : ℝ)*X 1 0+(1926904403/5000000000 : ℝ)*X 1 1+(770761247/2000000000 : ℝ)*X 1 2+(4609753273/10000000000 : ℝ)*X 2 0+(1926904403/5000000000 : ℝ)*X 2 1+(770761247/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-75084853/625000000 : ℝ)*X 0 0+(1115628253/2000000000 : ℝ)*X 0 1+(5152770881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1350180661/2500000000 : ℝ)*X 1 0+(-1449309303/10000000000 : ℝ)*X 1 1+(5032003/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5400722727/10000000000 : ℝ)*X 2 0+(5152770821/10000000000 : ℝ)*X 2 1+(-181163691/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((722068259/2000000000 : ℝ)*X 0 0+(2176764559/5000000000 : ℝ)*X 0 1+(2176764829/5000000000 : ℝ)*X 0 2+(722068259/2000000000 : ℝ)*X 1 0+(2176764559/5000000000 : ℝ)*X 1 1+(2176764829/5000000000 : ℝ)*X 1 2+(722068259/2000000000 : ℝ)*X 2 0+(2176764559/5000000000 : ℝ)*X 2 1+(2176764829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66833/100000 : ℝ) ≤ (-23220163863347892758841870459/34745000000000000000000000000 : ℝ) := by norm_num
    linear_combination (511239/50000000000000 : ℝ)*(upper1) + (308611/2000000000000 : ℝ)*(upper3) + (11854043/50000000000000 : ℝ)*(upper5) + (689686824024503/50000000000000 : ℝ)*(major0) + (689686824024503/50000000000000 : ℝ)*(major1) + (689686824024503/50000000000000 : ℝ)*(major2) + (1427156309/100000000000000 : ℝ)*(sp1) + (626787307/100000000000000 : ℝ)*(sp2) + (356313281/100000000000000 : ℝ)*(sp3) + (1042082029389413/50000000000000 : ℝ)*(sp4) + (521040700397079/25000000000000 : ℝ)*(sp5) + (2084163601957319/100000000000000 : ℝ)*(sp6) + (348429727402503/50000000000000 : ℝ)*(sp7) + (849829/500000000000 : ℝ)*(sp8) + (696859811118287/100000000000000 : ℝ)*(f.failure) + (1042082114372313/50000000000000 : ℝ)*(f.sum) + (29587268521493/34745000000000000000000000000 : ℝ)*base66 + (4036654986845855803/1737250000000000000000000000000000 : ℝ)*base67 + (9220911014566644197/1737250000000000000000000000000000 : ℝ)*base70 + (4667949026537105803/1737250000000000000000000000000000 : ℝ)*base71 + (876020489687/34745000000000000000000000000 : ℝ)*base73 + (3175099812583355803/1737250000000000000000000000000000 : ℝ)*base75 + (2819254836726644197/1737250000000000000000000000000000 : ℝ)*base78 + (3717428678545394197/1737250000000000000000000000000000 : ℝ)*base80 + (86343417952873/34745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1364229/500000000000000000000 : ℝ)*base89 + (1364229/500000000000000000000 : ℝ)*base91 + (1364229/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58613/100000 : ℝ) ≤ (4073178235916313480536585247/6949000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9195057/100000000000000 : ℝ)*(upper0) + (6902849/25000000000000 : ℝ)*(upper4) + (32733583/100000000000000 : ℝ)*(upper5) + (7433982250637/500000000000 : ℝ)*(major0) + (7433982250637/500000000000 : ℝ)*(major1) + (7433982250637/500000000000 : ℝ)*(major2) + (44058479965271/2000000000000 : ℝ)*(sp0) + (2202923114167053/100000000000000 : ℝ)*(sp1) + (2202907241321673/100000000000000 : ℝ)*(sp2) + (187782134865329/25000000000000 : ℝ)*(sp3) + (1518030713/100000000000000 : ℝ)*(sp5) + (17390876093/100000000000000 : ℝ)*(sp10) + (20160607/1562500000000 : ℝ)*(sp11) + (79241777/12500000000000 : ℝ)*(sp12) + (187782457435041/25000000000000 : ℝ)*(f.failure) + (1101462316098883/50000000000000 : ℝ)*(f.sum) + (4922851969157/1737250000000000000000000000 : ℝ)*base65 + (29709968732113337/17372500000000000000000000000000 : ℝ)*base67 + (72767431990011663/17372500000000000000000000000000 : ℝ)*base70 + (40716610866320837/17372500000000000000000000000000 : ℝ)*base71 + (22298575467067/6949000000000000000000000000 : ℝ)*base73 + (92112655074366663/17372500000000000000000000000000 : ℝ)*base76 + (30228868664258337/17372500000000000000000000000000 : ℝ)*base77 + (172067760040304163/17372500000000000000000000000000 : ℝ)*base80 + (4615597883803/3474500000000000000000000000 : ℝ)*base81 + (1075253/125000000000000000000 : ℝ)*base90 + (1075253/125000000000000000000 : ℝ)*base92 + (1075253/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81769/100000 : ℝ) ≤ (1420571777505633484976873975828409/1737250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1533177/3125000000000 : ℝ)*(upper0) + (17141747/50000000000000 : ℝ)*(upper1) + (1165637/1000000000000 : ℝ)*(upper3) + (313604171/100000000000000 : ℝ)*(upper4) + (1502313038861503/100000000000000 : ℝ)*(major0) + (1502313038861503/100000000000000 : ℝ)*(major1) + (1502313038861503/100000000000000 : ℝ)*(major2) + (1697316499/20000000000000 : ℝ)*(sp1) + (32383204799/100000000000000 : ℝ)*(sp2) + (7191283199/50000000000000 : ℝ)*(sp3) + (138650010446003/6250000000000 : ℝ)*(sp8) + (2218391680553553/100000000000000 : ℝ)*(sp9) + (138647986495703/6250000000000 : ℝ)*(sp10) + (189738607637097/25000000000000 : ℝ)*(sp11) + (379484406557393/50000000000000 : ℝ)*(f.failure) + (138650010446003/6250000000000 : ℝ)*(f.sum) + (16100644643793/4343125000000000000000000000 : ℝ)*base66 + (19079555964673107197/3474500000000000000000000000000000 : ℝ)*base68 + (37926750327199107197/3474500000000000000000000000000000 : ℝ)*base70 + (28910176255832107197/3474500000000000000000000000000000 : ℝ)*base72 + (64326285373191/34745000000000000000000000000 : ℝ)*base73 + (14307222720592107197/3474500000000000000000000000000000 : ℝ)*base76 + (8995278049276392803/3474500000000000000000000000000000 : ℝ)*base77 + (14693937227994892803/3474500000000000000000000000000000 : ℝ)*base79 + (107543490480949/34745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (366331/250000000000000000000 : ℝ)*base89 + (366331/250000000000000000000 : ℝ)*base91 + (366331/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-1811/2000 : ℝ) ≤ (-786515498380466025639036808376241/868625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4476939/20000000000000 : ℝ)*(lower1) + (5472151/25000000000000 : ℝ)*(upper3) + (36274701/100000000000000 : ℝ)*(lower4) + (479147/2000000000000 : ℝ)*(upper5) + (776261556196651/50000000000000 : ℝ)*(major0) + (776261556196651/50000000000000 : ℝ)*(major1) + (776261556196651/50000000000000 : ℝ)*(major2) + (31410829/12500000000000 : ℝ)*(sp4) + (32882973563/100000000000000 : ℝ)*(sp6) + (3693774997/50000000000000 : ℝ)*(sp7) + (117544670891851/5000000000000 : ℝ)*(sp12) + (587723417280913/25000000000000 : ℝ)*(sp13) + (235086078615009/10000000000000 : ℝ)*(sp14) + (392163781799661/50000000000000 : ℝ)*(sp15) + (196083737787329/25000000000000 : ℝ)*(f.failure) + (587723417280913/25000000000000 : ℝ)*(f.sum) + (22655742585783/17372500000000000000000000000 : ℝ)*base66 + (24747485228362461249/1737250000000000000000000000000000 : ℝ)*base68 + (19126459065043461249/1737250000000000000000000000000000 : ℝ)*base70 + (338664612062961249/1737250000000000000000000000000000 : ℝ)*base72 + (3898981952279/8686250000000000000000000000 : ℝ)*base74 + (201985547570461249/1737250000000000000000000000000000 : ℝ)*base76 + (2975758394130461249/1737250000000000000000000000000000 : ℝ)*base78 + (5586588529721211249/1737250000000000000000000000000000 : ℝ)*base80 + (5864810343069/8686250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (635957/125000000000000000000 : ℝ)*base90 + (635957/125000000000000000000 : ℝ)*base92 + (635957/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1719_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4257/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66833/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58613/100000 : ℝ) else (81769/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1811/2000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1719_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1719_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4259/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66833/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58613/100000 : ℝ) else (81769/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1811/2000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1719_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1719_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4259/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66833/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58613/100000 : ℝ) else (81769/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1811/2000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1719_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

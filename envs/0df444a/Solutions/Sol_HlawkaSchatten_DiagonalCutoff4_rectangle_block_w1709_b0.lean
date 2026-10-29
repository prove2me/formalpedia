-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1709_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:06.019809+00:00
-- url     : https://prove2.me/submissions/22a18b7e-07cd-442d-8a99-b7edf01f2d9b

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
theorem support_rectangle_w1709_s0_0 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53581607/400000000 : ℝ)*x 0 + (44530113/78125000 : ℝ)*x 1 + (4959144719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53581607/400000000 : ℝ)^5295 ≤ (8272517801233/100000000000000 : ℝ)^4271 := by
    have hnat : (53581607 : ℕ)^5295*100000000000000^4271 ≤ 8272517801233^4271*400000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53581607 400000000 8272517801233 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44530113/78125000 : ℝ)^5295 ≤ (49811603071617/100000000000000 : ℝ)^4271 := by
    have hnat : (44530113 : ℕ)^5295*100000000000000^4271 ≤ 49811603071617^4271*78125000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44530113 78125000 49811603071617 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4959144719/10000000000 : ℝ)^5295 ≤ (8383175822397/20000000000000 : ℝ)^4271 := by
    have hnat : (4959144719 : ℕ)^5295*20000000000000^4271 ≤ 8383175822397^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4959144719 10000000000 8383175822397 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53581607/400000000 : ℝ), (44530113/78125000 : ℝ), (4959144719/10000000000 : ℝ)] ![(8272517801233/100000000000000 : ℝ), (49811603071617/100000000000000 : ℝ), (8383175822397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53581607/400000000 : ℝ)|^5295 ≤ (8272517801233/100000000000000 : ℝ)^4271
        have hw : |(-53581607/400000000 : ℝ)|=(53581607/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44530113/78125000 : ℝ)|^5295 ≤ (49811603071617/100000000000000 : ℝ)^4271
        have hw : |(44530113/78125000 : ℝ)|=(44530113/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4959144719/10000000000 : ℝ)|^5295 ≤ (8383175822397/20000000000000 : ℝ)^4271
        have hw : |(4959144719/10000000000 : ℝ)|=(4959144719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s0_1 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54049749/100000000 : ℝ)*x 0 + (-87038159/500000000 : ℝ)*x 1 + (2479572073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54049749/100000000 : ℝ)^5295 ≤ (4663685229589/10000000000000 : ℝ)^4271 := by
    have hnat : (54049749 : ℕ)^5295*10000000000000^4271 ≤ 4663685229589^4271*100000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54049749 100000000 4663685229589 10000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87038159/500000000 : ℝ)^5295 ≤ (11447274578787/100000000000000 : ℝ)^4271 := by
    have hnat : (87038159 : ℕ)^5295*100000000000000^4271 ≤ 11447274578787^4271*500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87038159 500000000 11447274578787 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2479572073/5000000000 : ℝ)^5295 ≤ (41915873107679/100000000000000 : ℝ)^4271 := by
    have hnat : (2479572073 : ℕ)^5295*100000000000000^4271 ≤ 41915873107679^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479572073 5000000000 41915873107679 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54049749/100000000 : ℝ), (-87038159/500000000 : ℝ), (2479572073/5000000000 : ℝ)] ![(4663685229589/10000000000000 : ℝ), (11447274578787/100000000000000 : ℝ), (41915873107679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54049749/100000000 : ℝ)|^5295 ≤ (4663685229589/10000000000000 : ℝ)^4271
        have hw : |(54049749/100000000 : ℝ)|=(54049749/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87038159/500000000 : ℝ)|^5295 ≤ (11447274578787/100000000000000 : ℝ)^4271
        have hw : |(-87038159/500000000 : ℝ)|=(87038159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2479572073/5000000000 : ℝ)|^5295 ≤ (41915873107679/100000000000000 : ℝ)^4271
        have hw : |(2479572073/5000000000 : ℝ)|=(2479572073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s0_2 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135124351/250000000 : ℝ)*x 0 + (154973271/312500000 : ℝ)*x 1 + (-1740763633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135124351/250000000 : ℝ)^5295 ≤ (2331842154813/5000000000000 : ℝ)^4271 := by
    have hnat : (135124351 : ℕ)^5295*5000000000000^4271 ≤ 2331842154813^4271*250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135124351 250000000 2331842154813 5000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154973271/312500000 : ℝ)^5295 ≤ (8383175723897/20000000000000 : ℝ)^4271 := by
    have hnat : (154973271 : ℕ)^5295*20000000000000^4271 ≤ 8383175723897^4271*312500000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154973271 312500000 8383175723897 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1740763633/10000000000 : ℝ)^5295 ≤ (5723639135969/50000000000000 : ℝ)^4271 := by
    have hnat : (1740763633 : ℕ)^5295*50000000000000^4271 ≤ 5723639135969^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740763633 10000000000 5723639135969 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135124351/250000000 : ℝ), (154973271/312500000 : ℝ), (-1740763633/10000000000 : ℝ)] ![(2331842154813/5000000000000 : ℝ), (8383175723897/20000000000000 : ℝ), (5723639135969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135124351/250000000 : ℝ)|^5295 ≤ (2331842154813/5000000000000 : ℝ)^4271
        have hw : |(135124351/250000000 : ℝ)|=(135124351/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154973271/312500000 : ℝ)|^5295 ≤ (8383175723897/20000000000000 : ℝ)^4271
        have hw : |(154973271/312500000 : ℝ)|=(154973271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1740763633/10000000000 : ℝ)|^5295 ≤ (5723639135969/50000000000000 : ℝ)^4271
        have hw : |(-1740763633/10000000000 : ℝ)|=(1740763633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s0_3 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2020204547/5000000000 : ℝ)*x 0 + (382300269/1250000000 : ℝ)*x 1 + (1300248157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020204547/5000000000 : ℝ)^5295 ≤ (650269304107/2000000000000 : ℝ)^4271 := by
    have hnat : (2020204547 : ℕ)^5295*2000000000000^4271 ≤ 650269304107^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020204547 5000000000 650269304107 2000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (382300269/1250000000 : ℝ)^5295 ≤ (23021762845087/100000000000000 : ℝ)^4271 := by
    have hnat : (382300269 : ℕ)^5295*100000000000000^4271 ≤ 23021762845087^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382300269 1250000000 23021762845087 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300248157/2500000000 : ℝ)^5295 ≤ (44464771936963/100000000000000 : ℝ)^4271 := by
    have hnat : (1300248157 : ℕ)^5295*100000000000000^4271 ≤ 44464771936963^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300248157 2500000000 44464771936963 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2020204547/5000000000 : ℝ), (382300269/1250000000 : ℝ), (1300248157/2500000000 : ℝ)] ![(650269304107/2000000000000 : ℝ), (23021762845087/100000000000000 : ℝ), (44464771936963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2020204547/5000000000 : ℝ)|^5295 ≤ (650269304107/2000000000000 : ℝ)^4271
        have hw : |(2020204547/5000000000 : ℝ)|=(2020204547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(382300269/1250000000 : ℝ)|^5295 ≤ (23021762845087/100000000000000 : ℝ)^4271
        have hw : |(382300269/1250000000 : ℝ)|=(382300269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300248157/2500000000 : ℝ)|^5295 ≤ (44464771936963/100000000000000 : ℝ)^4271
        have hw : |(1300248157/2500000000 : ℝ)|=(1300248157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s0_4 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67061299/500000000 : ℝ)*x 0 + (1244341703/2500000000 : ℝ)*x 1 + (5681023809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67061299/500000000 : ℝ)^5295 ≤ (8285426759363/100000000000000 : ℝ)^4271 := by
    have hnat : (67061299 : ℕ)^5295*100000000000000^4271 ≤ 8285426759363^4271*500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67061299 500000000 8285426759363 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1244341703/2500000000 : ℝ)^5295 ≤ (10526726833053/25000000000000 : ℝ)^4271 := by
    have hnat : (1244341703 : ℕ)^5295*25000000000000^4271 ≤ 10526726833053^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244341703 2500000000 10526726833053 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5681023809/10000000000 : ℝ)^5295 ≤ (24803832949481/50000000000000 : ℝ)^4271 := by
    have hnat : (5681023809 : ℕ)^5295*50000000000000^4271 ≤ 24803832949481^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681023809 10000000000 24803832949481 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67061299/500000000 : ℝ), (1244341703/2500000000 : ℝ), (5681023809/10000000000 : ℝ)] ![(8285426759363/100000000000000 : ℝ), (10526726833053/25000000000000 : ℝ), (24803832949481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67061299/500000000 : ℝ)|^5295 ≤ (8285426759363/100000000000000 : ℝ)^4271
        have hw : |(-67061299/500000000 : ℝ)|=(67061299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1244341703/2500000000 : ℝ)|^5295 ≤ (10526726833053/25000000000000 : ℝ)^4271
        have hw : |(1244341703/2500000000 : ℝ)|=(1244341703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5681023809/10000000000 : ℝ)|^5295 ≤ (24803832949481/50000000000000 : ℝ)^4271
        have hw : |(5681023809/10000000000 : ℝ)|=(5681023809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s0_5 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301069851/2500000000 : ℝ)*x 0 + (-509441779/5000000000 : ℝ)*x 1 + (2840511933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301069851/2500000000 : ℝ)^5295 ≤ (22249805610661/50000000000000 : ℝ)^4271 := by
    have hnat : (1301069851 : ℕ)^5295*50000000000000^4271 ≤ 22249805610661^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301069851 2500000000 22249805610661 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509441779/5000000000 : ℝ)^5295 ≤ (1178544449733/20000000000000 : ℝ)^4271 := by
    have hnat : (509441779 : ℕ)^5295*20000000000000^4271 ≤ 1178544449733^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509441779 5000000000 1178544449733 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2840511933/5000000000 : ℝ)^5295 ≤ (49607666516031/100000000000000 : ℝ)^4271 := by
    have hnat : (2840511933 : ℕ)^5295*100000000000000^4271 ≤ 49607666516031^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840511933 5000000000 49607666516031 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301069851/2500000000 : ℝ), (-509441779/5000000000 : ℝ), (2840511933/5000000000 : ℝ)] ![(22249805610661/50000000000000 : ℝ), (1178544449733/20000000000000 : ℝ), (49607666516031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301069851/2500000000 : ℝ)|^5295 ≤ (22249805610661/50000000000000 : ℝ)^4271
        have hw : |(1301069851/2500000000 : ℝ)|=(1301069851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509441779/5000000000 : ℝ)|^5295 ≤ (1178544449733/20000000000000 : ℝ)^4271
        have hw : |(-509441779/5000000000 : ℝ)|=(509441779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2840511933/5000000000 : ℝ)|^5295 ≤ (49607666516031/100000000000000 : ℝ)^4271
        have hw : |(2840511933/5000000000 : ℝ)|=(2840511933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s0_6 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2602139537/5000000000 : ℝ)*x 0 + (1420256151/2500000000 : ℝ)*x 1 + (-254720733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2602139537/5000000000 : ℝ)^5295 ≤ (5562450965389/12500000000000 : ℝ)^4271 := by
    have hnat : (2602139537 : ℕ)^5295*12500000000000^4271 ≤ 5562450965389^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602139537 5000000000 5562450965389 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1420256151/2500000000 : ℝ)^5295 ≤ (9921534901089/20000000000000 : ℝ)^4271 := by
    have hnat : (1420256151 : ℕ)^5295*20000000000000^4271 ≤ 9921534901089^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420256151 2500000000 9921534901089 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254720733/2500000000 : ℝ)^5295 ≤ (1473179440039/25000000000000 : ℝ)^4271 := by
    have hnat : (254720733 : ℕ)^5295*25000000000000^4271 ≤ 1473179440039^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254720733 2500000000 1473179440039 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2602139537/5000000000 : ℝ), (1420256151/2500000000 : ℝ), (-254720733/2500000000 : ℝ)] ![(5562450965389/12500000000000 : ℝ), (9921534901089/20000000000000 : ℝ), (1473179440039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2602139537/5000000000 : ℝ)|^5295 ≤ (5562450965389/12500000000000 : ℝ)^4271
        have hw : |(2602139537/5000000000 : ℝ)|=(2602139537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1420256151/2500000000 : ℝ)|^5295 ≤ (9921534901089/20000000000000 : ℝ)^4271
        have hw : |(1420256151/2500000000 : ℝ)|=(1420256151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254720733/2500000000 : ℝ)|^5295 ≤ (1473179440039/25000000000000 : ℝ)^4271
        have hw : |(-254720733/2500000000 : ℝ)|=(254720733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s0_7 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4045281103/10000000000 : ℝ)*x 0 + (643535383/1250000000 : ℝ)*x 1 + (3112869659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4045281103/10000000000 : ℝ)^5295 ≤ (1628103869547/5000000000000 : ℝ)^4271 := by
    have hnat : (4045281103 : ℕ)^5295*5000000000000^4271 ≤ 1628103869547^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4045281103 10000000000 1628103869547 5000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643535383/1250000000 : ℝ)^5295 ≤ (8781356407859/20000000000000 : ℝ)^4271 := by
    have hnat : (643535383 : ℕ)^5295*20000000000000^4271 ≤ 8781356407859^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643535383 1250000000 8781356407859 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3112869659/10000000000 : ℝ)^5295 ≤ (23531140549859/100000000000000 : ℝ)^4271 := by
    have hnat : (3112869659 : ℕ)^5295*100000000000000^4271 ≤ 23531140549859^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3112869659 10000000000 23531140549859 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4045281103/10000000000 : ℝ), (643535383/1250000000 : ℝ), (3112869659/10000000000 : ℝ)] ![(1628103869547/5000000000000 : ℝ), (8781356407859/20000000000000 : ℝ), (23531140549859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4045281103/10000000000 : ℝ)|^5295 ≤ (1628103869547/5000000000000 : ℝ)^4271
        have hw : |(4045281103/10000000000 : ℝ)|=(4045281103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643535383/1250000000 : ℝ)|^5295 ≤ (8781356407859/20000000000000 : ℝ)^4271
        have hw : |(643535383/1250000000 : ℝ)|=(643535383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3112869659/10000000000 : ℝ)|^5295 ≤ (23531140549859/100000000000000 : ℝ)^4271
        have hw : |(3112869659/10000000000 : ℝ)|=(3112869659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1709_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6021/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2743/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5287/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5287 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5287*1^1024 ≤ 0^1024*1^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5287/1024 : ℝ) ≤ (881863844318401917/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5287 ≤ (881863844318401917/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5287*100000000000000000000^1024 ≤ 881863844318401917^1024*5^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 881863844318401917 100000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (881863844318401917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5287 := by
      have hnat : (1 : ℕ)^1024*1^5287 ≤ 1^5287*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100881863844318401917/100000000000000000000 : ℝ) ≤ (10017019764929793/10000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (100881863844318401917/100000000000000000000 : ℝ)^1024 ≤ (10017019764929793/10000000000000000 : ℝ)^5287 := by
      have hnat : (100881863844318401917 : ℕ)^1024*10000000000000000^5287 ≤ 10017019764929793^5287*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100881863844318401917 100000000000000000000 10017019764929793 10000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017019764929793/10000000000000000 : ℝ)) (X := (100881863844318401917/100000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50881863844318401917/50000000000000000000 : ℝ) ≤ (5017019764929793/5000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (50881863844318401917/50000000000000000000 : ℝ)^1024 ≤ (5017019764929793/5000000000000000 : ℝ)^5287 := by
      have hnat : (50881863844318401917 : ℕ)^1024*5000000000000000^5287 ≤ 5017019764929793^5287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50881863844318401917 50000000000000000000 5017019764929793 5000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017019764929793/5000000000000000 : ℝ)) (X := (50881863844318401917/50000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(17019764929793/4000000000000000 : ℝ)*(0 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17019764929793/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(881863844318401917/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(17019764929793/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5287/1024 : ℝ) := by
    rw [show (1 : ℝ)+(17019764929793/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10017019764929793/10000000000000000 : ℝ) by norm_num, show 1+(881863844318401917/100000000000000000000 : ℝ)+(0 : ℝ)=(100881863844318401917/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(881863844318401917/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(17019764929793/4000000000000000 : ℝ)*(2/5 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17019764929793/4000000000000000 : ℝ)*(2/5 : ℝ)=(5017019764929793/5000000000000000 : ℝ) by norm_num, show 1+2*(881863844318401917/100000000000000000000 : ℝ)=(50881863844318401917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(17019764929793/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17019764929793/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(17019764929793/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17019764929793/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(17019764929793/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17019764929793/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53581607/400000000 : ℝ)*X 0 0+(44530113/78125000 : ℝ)*X 0 1+(4959144719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((54049749/100000000 : ℝ)*X 1 0+(-87038159/500000000 : ℝ)*X 1 1+(2479572073/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((135124351/250000000 : ℝ)*X 2 0+(154973271/312500000 : ℝ)*X 2 1+(-1740763633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2020204547/5000000000 : ℝ)*X 0 0+(382300269/1250000000 : ℝ)*X 0 1+(1300248157/2500000000 : ℝ)*X 0 2+(2020204547/5000000000 : ℝ)*X 1 0+(382300269/1250000000 : ℝ)*X 1 1+(1300248157/2500000000 : ℝ)*X 1 2+(2020204547/5000000000 : ℝ)*X 2 0+(382300269/1250000000 : ℝ)*X 2 1+(1300248157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-67061299/500000000 : ℝ)*X 0 0+(1244341703/2500000000 : ℝ)*X 0 1+(5681023809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1301069851/2500000000 : ℝ)*X 1 0+(-509441779/5000000000 : ℝ)*X 1 1+(2840511933/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2602139537/5000000000 : ℝ)*X 2 0+(1420256151/2500000000 : ℝ)*X 2 1+(-254720733/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4045281103/10000000000 : ℝ)*X 0 0+(643535383/1250000000 : ℝ)*X 0 1+(3112869659/10000000000 : ℝ)*X 0 2+(4045281103/10000000000 : ℝ)*X 1 0+(643535383/1250000000 : ℝ)*X 1 1+(3112869659/10000000000 : ℝ)*X 1 2+(4045281103/10000000000 : ℝ)*X 2 0+(643535383/1250000000 : ℝ)*X 2 1+(3112869659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25612186904731767003891/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189026329/100000000000000 : ℝ)*(base1) + (1005108181/50000000000000 : ℝ)*(base19) + (1795403243/100000000000000 : ℝ)*(base23) + (98181333/25000000000000 : ℝ)*(upper3) + (33270877/20000000000000 : ℝ)*(upper5) + (45420027533871/5000000000000 : ℝ)*(major0) + (45420027533871/5000000000000 : ℝ)*(major1) + (45420027533871/5000000000000 : ℝ)*(major2) + (1350064960327401/100000000000000 : ℝ)*(sp0) + (675034493915533/50000000000000 : ℝ)*(sp1) + (675034601322093/50000000000000 : ℝ)*(sp2) + (466726792580417/100000000000000 : ℝ)*(sp3) + (1556686589/25000000000000 : ℝ)*(sp4) + (86881401/3125000000000 : ℝ)*(sp7) + (466729761811577/100000000000000 : ℝ)*(f.failure) + (337517749511857/25000000000000 : ℝ)*(f.sum) + (14070866128703/10000000000000000000000000000 : ℝ)*base65 + (77884689158703/20000000000000000000000000000 : ℝ)*base67 + (60641374778703/20000000000000000000000000000 : ℝ)*base69 + (108042338638703/20000000000000000000000000000 : ℝ)*base71 + (27392516998703/10000000000000000000000000000 : ℝ)*base73 + (61227288518703/20000000000000000000000000000 : ℝ)*base75 + (42291422161297/20000000000000000000000000000 : ℝ)*base78 + (16634747961297/20000000000000000000000000000 : ℝ)*base80 + (61842540258703/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (47369079/5000000000000000000000 : ℝ)*base90 + (47369079/5000000000000000000000 : ℝ)*base92 + (47369079/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (308860155304857821564031/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1985078627/100000000000000 : ℝ)*(base19) + (2220884669/100000000000000 : ℝ)*(base23) + (32279411/25000000000000 : ℝ)*(upper2) + (11194489/3125000000000 : ℝ)*(upper3) + (319412197/100000000000000 : ℝ)*(upper5) + (239055807336789/25000000000000 : ℝ)*(major0) + (239055807336789/25000000000000 : ℝ)*(major1) + (239055807336789/25000000000000 : ℝ)*(major2) + (7026483619/100000000000000 : ℝ)*(sp1) + (2261124221/25000000000000 : ℝ)*(sp2) + (355286384442017/25000000000000 : ℝ)*(sp4) + (1421136526205821/100000000000000 : ℝ)*(sp5) + (284226854477303/20000000000000 : ℝ)*(sp6) + (491300715019469/100000000000000 : ℝ)*(sp7) + (491300715019469/100000000000000 : ℝ)*(f.failure) + (355286384442017/25000000000000 : ℝ)*(f.sum) + (76770492295323/50000000000000000000000000000 : ℝ)*base66 + (143615667854677/100000000000000000000000000000 : ℝ)*base67 + (533663317245323/100000000000000000000000000000 : ℝ)*base70 + (233847918045323/100000000000000000000000000000 : ℝ)*base72 + (197877217154677/50000000000000000000000000000 : ℝ)*base73 + (196657052045323/100000000000000000000000000000 : ℝ)*base76 + (482228386645323/100000000000000000000000000000 : ℝ)*base78 + (706930121345323/100000000000000000000000000000 : ℝ)*base80 + (175823415104677/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (29943837/5000000000000000000000 : ℝ)*base89 + (29943837/5000000000000000000000 : ℝ)*base91 + (29943837/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1709_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6021/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2743/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1709_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1709_s1_0 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1411987939/10000000000 : ℝ)*x 0 + (1371455207/2500000000 : ℝ)*x 1 + (256275031/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1411987939/10000000000 : ℝ)^5295 ≤ (1766149399733/20000000000000 : ℝ)^4271 := by
    have hnat : (1411987939 : ℕ)^5295*20000000000000^4271 ≤ 1766149399733^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1411987939 10000000000 1766149399733 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371455207/2500000000 : ℝ)^5295 ≤ (23751612939877/50000000000000 : ℝ)^4271 := by
    have hnat : (1371455207 : ℕ)^5295*50000000000000^4271 ≤ 23751612939877^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371455207 2500000000 23751612939877 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256275031/500000000 : ℝ)^5295 ≤ (2183301355549/5000000000000 : ℝ)^4271 := by
    have hnat : (256275031 : ℕ)^5295*5000000000000^4271 ≤ 2183301355549^4271*500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256275031 500000000 2183301355549 5000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1411987939/10000000000 : ℝ), (1371455207/2500000000 : ℝ), (256275031/500000000 : ℝ)] ![(1766149399733/20000000000000 : ℝ), (23751612939877/50000000000000 : ℝ), (2183301355549/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1411987939/10000000000 : ℝ)|^5295 ≤ (1766149399733/20000000000000 : ℝ)^4271
        have hw : |(-1411987939/10000000000 : ℝ)|=(1411987939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371455207/2500000000 : ℝ)|^5295 ≤ (23751612939877/50000000000000 : ℝ)^4271
        have hw : |(1371455207/2500000000 : ℝ)|=(1371455207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256275031/500000000 : ℝ)|^5295 ≤ (2183301355549/5000000000000 : ℝ)^4271
        have hw : |(256275031/500000000 : ℝ)|=(256275031/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s1_1 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347960813/10000000000 : ℝ)*x 0 + (-799700119/5000000000 : ℝ)*x 1 + (2562749837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347960813/10000000000 : ℝ)^5295 ≤ (46027731939197/100000000000000 : ℝ)^4271 := by
    have hnat : (5347960813 : ℕ)^5295*100000000000000^4271 ≤ 46027731939197^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347960813 10000000000 46027731939197 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (799700119/5000000000 : ℝ)^5295 ≤ (644140683449/6250000000000 : ℝ)^4271 := by
    have hnat : (799700119 : ℕ)^5295*6250000000000^4271 ≤ 644140683449^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799700119 5000000000 644140683449 6250000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2562749837/5000000000 : ℝ)^5295 ≤ (43666017119383/100000000000000 : ℝ)^4271 := by
    have hnat : (2562749837 : ℕ)^5295*100000000000000^4271 ≤ 43666017119383^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562749837 5000000000 43666017119383 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347960813/10000000000 : ℝ), (-799700119/5000000000 : ℝ), (2562749837/5000000000 : ℝ)] ![(46027731939197/100000000000000 : ℝ), (644140683449/6250000000000 : ℝ), (43666017119383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347960813/10000000000 : ℝ)|^5295 ≤ (46027731939197/100000000000000 : ℝ)^4271
        have hw : |(5347960813/10000000000 : ℝ)|=(5347960813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-799700119/5000000000 : ℝ)|^5295 ≤ (644140683449/6250000000000 : ℝ)^4271
        have hw : |(-799700119/5000000000 : ℝ)|=(799700119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2562749837/5000000000 : ℝ)|^5295 ≤ (43666017119383/100000000000000 : ℝ)^4271
        have hw : |(2562749837/5000000000 : ℝ)|=(2562749837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s1_2 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347959419/10000000000 : ℝ)*x 0 + (64068761/125000000 : ℝ)*x 1 + (-199925063/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347959419/10000000000 : ℝ)^5295 ≤ (46027717065103/100000000000000 : ℝ)^4271 := by
    have hnat : (5347959419 : ℕ)^5295*100000000000000^4271 ≤ 46027717065103^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347959419 10000000000 46027717065103 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64068761/125000000 : ℝ)^5295 ≤ (8733205971417/20000000000000 : ℝ)^4271 := by
    have hnat : (64068761 : ℕ)^5295*20000000000000^4271 ≤ 8733205971417^4271*125000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64068761 125000000 8733205971417 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199925063/1250000000 : ℝ)^5295 ≤ (10306253060197/100000000000000 : ℝ)^4271 := by
    have hnat : (199925063 : ℕ)^5295*100000000000000^4271 ≤ 10306253060197^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199925063 1250000000 10306253060197 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347959419/10000000000 : ℝ), (64068761/125000000 : ℝ), (-199925063/1250000000 : ℝ)] ![(46027717065103/100000000000000 : ℝ), (8733205971417/20000000000000 : ℝ), (10306253060197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347959419/10000000000 : ℝ)|^5295 ≤ (46027717065103/100000000000000 : ℝ)^4271
        have hw : |(5347959419/10000000000 : ℝ)|=(5347959419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64068761/125000000 : ℝ)|^5295 ≤ (8733205971417/20000000000000 : ℝ)^4271
        have hw : |(64068761/125000000 : ℝ)|=(64068761/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199925063/1250000000 : ℝ)|^5295 ≤ (10306253060197/100000000000000 : ℝ)^4271
        have hw : |(-199925063/1250000000 : ℝ)|=(199925063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s1_3 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1025782691/2500000000 : ℝ)*x 0 + (3602973129/10000000000 : ℝ)*x 1 + (4645240957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025782691/2500000000 : ℝ)^5295 ≤ (33140362243147/100000000000000 : ℝ)^4271 := by
    have hnat : (1025782691 : ℕ)^5295*100000000000000^4271 ≤ 33140362243147^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025782691 2500000000 33140362243147 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3602973129/10000000000 : ℝ)^5295 ≤ (3525962068647/12500000000000 : ℝ)^4271 := by
    have hnat : (3602973129 : ℕ)^5295*12500000000000^4271 ≤ 3525962068647^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3602973129 10000000000 3525962068647 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4645240957/10000000000 : ℝ)^5295 ≤ (19325970596481/50000000000000 : ℝ)^4271 := by
    have hnat : (4645240957 : ℕ)^5295*50000000000000^4271 ≤ 19325970596481^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4645240957 10000000000 19325970596481 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025782691/2500000000 : ℝ), (3602973129/10000000000 : ℝ), (4645240957/10000000000 : ℝ)] ![(33140362243147/100000000000000 : ℝ), (3525962068647/12500000000000 : ℝ), (19325970596481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025782691/2500000000 : ℝ)|^5295 ≤ (33140362243147/100000000000000 : ℝ)^4271
        have hw : |(1025782691/2500000000 : ℝ)|=(1025782691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3602973129/10000000000 : ℝ)|^5295 ≤ (3525962068647/12500000000000 : ℝ)^4271
        have hw : |(3602973129/10000000000 : ℝ)|=(3602973129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4645240957/10000000000 : ℝ)|^5295 ≤ (19325970596481/50000000000000 : ℝ)^4271
        have hw : |(4645240957/10000000000 : ℝ)|=(4645240957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s1_4 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1412180917/10000000000 : ℝ)*x 0 + (5129817613/10000000000 : ℝ)*x 1 + (2740716677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1412180917/10000000000 : ℝ)^5295 ≤ (4416121647763/50000000000000 : ℝ)^4271 := by
    have hnat : (1412180917 : ℕ)^5295*50000000000000^4271 ≤ 4416121647763^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412180917 10000000000 4416121647763 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129817613/10000000000 : ℝ)^5295 ≤ (21855813771941/50000000000000 : ℝ)^4271 := by
    have hnat : (5129817613 : ℕ)^5295*50000000000000^4271 ≤ 21855813771941^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129817613 10000000000 21855813771941 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740716677/5000000000 : ℝ)^5295 ≤ (23728064573293/50000000000000 : ℝ)^4271 := by
    have hnat : (2740716677 : ℕ)^5295*50000000000000^4271 ≤ 23728064573293^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740716677 5000000000 23728064573293 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1412180917/10000000000 : ℝ), (5129817613/10000000000 : ℝ), (2740716677/5000000000 : ℝ)] ![(4416121647763/50000000000000 : ℝ), (21855813771941/50000000000000 : ℝ), (23728064573293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1412180917/10000000000 : ℝ)|^5295 ≤ (4416121647763/50000000000000 : ℝ)^4271
        have hw : |(-1412180917/10000000000 : ℝ)|=(1412180917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129817613/10000000000 : ℝ)|^5295 ≤ (21855813771941/50000000000000 : ℝ)^4271
        have hw : |(5129817613/10000000000 : ℝ)|=(5129817613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740716677/5000000000 : ℝ)|^5295 ≤ (23728064573293/50000000000000 : ℝ)^4271
        have hw : |(2740716677/5000000000 : ℝ)|=(2740716677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s1_5 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312869221/2500000000 : ℝ)*x 0 + (-248693379/2000000000 : ℝ)*x 1 + (2740716567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312869221/2500000000 : ℝ)^5295 ≤ (45000477315359/100000000000000 : ℝ)^4271 := by
    have hnat : (1312869221 : ℕ)^5295*100000000000000^4271 ≤ 45000477315359^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312869221 2500000000 45000477315359 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248693379/2000000000 : ℝ)^5295 ≤ (15086791789/200000000000 : ℝ)^4271 := by
    have hnat : (248693379 : ℕ)^5295*200000000000^4271 ≤ 15086791789^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248693379 2000000000 15086791789 200000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740716567/5000000000 : ℝ)^5295 ≤ (47456126785253/100000000000000 : ℝ)^4271 := by
    have hnat : (2740716567 : ℕ)^5295*100000000000000^4271 ≤ 47456126785253^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740716567 5000000000 47456126785253 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312869221/2500000000 : ℝ), (-248693379/2000000000 : ℝ), (2740716567/5000000000 : ℝ)] ![(45000477315359/100000000000000 : ℝ), (15086791789/200000000000 : ℝ), (47456126785253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312869221/2500000000 : ℝ)|^5295 ≤ (45000477315359/100000000000000 : ℝ)^4271
        have hw : |(1312869221/2500000000 : ℝ)|=(1312869221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248693379/2000000000 : ℝ)|^5295 ≤ (15086791789/200000000000 : ℝ)^4271
        have hw : |(-248693379/2000000000 : ℝ)|=(248693379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740716567/5000000000 : ℝ)|^5295 ≤ (47456126785253/100000000000000 : ℝ)^4271
        have hw : |(2740716567/5000000000 : ℝ)|=(2740716567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s1_6 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251476937/10000000000 : ℝ)*x 0 + (68517911/125000000 : ℝ)*x 1 + (-1243467181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251476937/10000000000 : ℝ)^5295 ≤ (4500047787841/10000000000000 : ℝ)^4271 := by
    have hnat : (5251476937 : ℕ)^5295*10000000000000^4271 ≤ 4500047787841^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251476937 10000000000 4500047787841 10000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68517911/125000000 : ℝ)^5295 ≤ (47456124058987/100000000000000 : ℝ)^4271 := by
    have hnat : (68517911 : ℕ)^5295*100000000000000^4271 ≤ 47456124058987^4271*125000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68517911 125000000 47456124058987 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1243467181/10000000000 : ℝ)^5295 ≤ (3771699022737/50000000000000 : ℝ)^4271 := by
    have hnat : (1243467181 : ℕ)^5295*50000000000000^4271 ≤ 3771699022737^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1243467181 10000000000 3771699022737 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251476937/10000000000 : ℝ), (68517911/125000000 : ℝ), (-1243467181/10000000000 : ℝ)] ![(4500047787841/10000000000000 : ℝ), (47456124058987/100000000000000 : ℝ), (3771699022737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251476937/10000000000 : ℝ)|^5295 ≤ (4500047787841/10000000000000 : ℝ)^4271
        have hw : |(5251476937/10000000000 : ℝ)|=(5251476937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68517911/125000000 : ℝ)|^5295 ≤ (47456124058987/100000000000000 : ℝ)^4271
        have hw : |(68517911/125000000 : ℝ)|=(68517911/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1243467181/10000000000 : ℝ)|^5295 ≤ (3771699022737/50000000000000 : ℝ)^4271
        have hw : |(-1243467181/10000000000 : ℝ)|=(1243467181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s1_7 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4103686987/10000000000 : ℝ)*x 0 + (4632752611/10000000000 : ℝ)*x 1 + (3615662419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103686987/10000000000 : ℝ)^5295 ≤ (6629186394999/20000000000000 : ℝ)^4271 := by
    have hnat : (4103686987 : ℕ)^5295*20000000000000^4271 ≤ 6629186394999^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103686987 10000000000 6629186394999 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4632752611/10000000000 : ℝ)^5295 ≤ (7704631297111/20000000000000 : ℝ)^4271 := by
    have hnat : (4632752611 : ℕ)^5295*20000000000000^4271 ≤ 7704631297111^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4632752611 10000000000 7704631297111 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3615662419/10000000000 : ℝ)^5295 ≤ (28330911518173/100000000000000 : ℝ)^4271 := by
    have hnat : (3615662419 : ℕ)^5295*100000000000000^4271 ≤ 28330911518173^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615662419 10000000000 28330911518173 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103686987/10000000000 : ℝ), (4632752611/10000000000 : ℝ), (3615662419/10000000000 : ℝ)] ![(6629186394999/20000000000000 : ℝ), (7704631297111/20000000000000 : ℝ), (28330911518173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103686987/10000000000 : ℝ)|^5295 ≤ (6629186394999/20000000000000 : ℝ)^4271
        have hw : |(4103686987/10000000000 : ℝ)|=(4103686987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4632752611/10000000000 : ℝ)|^5295 ≤ (7704631297111/20000000000000 : ℝ)^4271
        have hw : |(4632752611/10000000000 : ℝ)|=(4632752611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3615662419/10000000000 : ℝ)|^5295 ≤ (28330911518173/100000000000000 : ℝ)^4271
        have hw : |(3615662419/10000000000 : ℝ)|=(3615662419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1709_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2743/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6021/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4863/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8709/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2743/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6021/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2743/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6021/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2743/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6021/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2743/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6021/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2743/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6021/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2743/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6021/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6021/100000 : ℝ) ^ (5287/1024 : ℝ) ≤ (12510200170533/25000000000000000000 : ℝ) := by
    have hpowers : (6021/100000 : ℝ)^5287 ≤ (12510200170533/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6021 : ℕ)^5287*25000000000000000000^1024 ≤ 12510200170533^1024*100000^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6021 100000 12510200170533 25000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6021/100000 : ℝ)) (X := (12510200170533/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2743/12500 : ℝ) ^ (5287/1024 : ℝ) ≤ (39733501778736023/100000000000000000000 : ℝ) := by
    have hpowers : (2743/12500 : ℝ)^5287 ≤ (39733501778736023/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2743 : ℕ)^5287*100000000000000000000^1024 ≤ 39733501778736023^1024*12500^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2743 12500 39733501778736023 100000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2743/12500 : ℝ)) (X := (39733501778736023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500012510200170533/12500000000000000000 : ℝ) ≤ (625000121150367/625000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (12500012510200170533/12500000000000000000 : ℝ)^1024 ≤ (625000121150367/625000000000000 : ℝ)^5287 := by
      have hnat : (12500012510200170533 : ℕ)^1024*625000000000000^5287 ≤ 625000121150367^5287*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500012510200170533 12500000000000000000 625000121150367 625000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000121150367/625000000000000 : ℝ)) (X := (12500012510200170533/12500000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007956708515883631/20000000000000000000 : ℝ) ≤ (5000385207254677/5000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (20007956708515883631/20000000000000000000 : ℝ)^1024 ≤ (5000385207254677/5000000000000000 : ℝ)^5287 := by
      have hnat : (20007956708515883631 : ℕ)^1024*5000000000000000^5287 ≤ 5000385207254677^5287*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007956708515883631 20000000000000000000 5000385207254677 5000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000385207254677/5000000000000000 : ℝ)) (X := (20007956708515883631/20000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039733501778736023/50000000000000000000 : ℝ) ≤ (2500384722653209/2500000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (50039733501778736023/50000000000000000000 : ℝ)^1024 ≤ (2500384722653209/2500000000000000 : ℝ)^5287 := by
      have hnat : (50039733501778736023 : ℕ)^1024*2500000000000000^5287 ≤ 2500384722653209^5287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039733501778736023 50000000000000000000 2500384722653209 2500000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500384722653209/2500000000000000 : ℝ)) (X := (50039733501778736023/50000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12510200170533/25000000000000000000 : ℝ) ≤ ((39805194218999642403/39807500000000000000 : ℝ)+2*(384238051741/796150000000000 : ℝ)*(6021/100000 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (39805194218999642403/39807500000000000000 : ℝ)+2*(384238051741/796150000000000 : ℝ)*(6021/100000 : ℝ)=(625000121150367/625000000000000 : ℝ) by norm_num, show 1+2*(12510200170533/25000000000000000000 : ℝ)=(12500012510200170533/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39733501778736023/100000000000000000000 : ℝ)+(12510200170533/25000000000000000000 : ℝ) ≤ ((39805194218999642403/39807500000000000000 : ℝ)+(384238051741/796150000000000 : ℝ)*((2743/12500 : ℝ)+(6021/100000 : ℝ)))^(5287/1024 : ℝ) := by
    rw [show (39805194218999642403/39807500000000000000 : ℝ)+(384238051741/796150000000000 : ℝ)*((2743/12500 : ℝ)+(6021/100000 : ℝ))=(5000385207254677/5000000000000000 : ℝ) by norm_num, show 1+(39733501778736023/100000000000000000000 : ℝ)+(12510200170533/25000000000000000000 : ℝ)=(20007956708515883631/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39733501778736023/100000000000000000000 : ℝ) ≤ ((39805194218999642403/39807500000000000000 : ℝ)+2*(384238051741/796150000000000 : ℝ)*(2743/12500 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (39805194218999642403/39807500000000000000 : ℝ)+2*(384238051741/796150000000000 : ℝ)*(2743/12500 : ℝ)=(2500384722653209/2500000000000000 : ℝ) by norm_num, show 1+2*(39733501778736023/100000000000000000000 : ℝ)=(50039733501778736023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39805194218999642403/39807500000000000000 : ℝ)*(X 1 0+X 2 0)+(384238051741/796150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (6021/100000 : ℝ)) (hi := (2743/12500 : ℝ)) (c := (39805194218999642403/39807500000000000000 : ℝ)) (alpha := (384238051741/796150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39805194218999642403/39807500000000000000 : ℝ)*(X 0 1+X 2 1)+(384238051741/796150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (6021/100000 : ℝ)) (hi := (2743/12500 : ℝ)) (c := (39805194218999642403/39807500000000000000 : ℝ)) (alpha := (384238051741/796150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39805194218999642403/39807500000000000000 : ℝ)*(X 0 2+X 1 2)+(384238051741/796150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (6021/100000 : ℝ)) (hi := (2743/12500 : ℝ)) (c := (39805194218999642403/39807500000000000000 : ℝ)) (alpha := (384238051741/796150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1411987939/10000000000 : ℝ)*X 0 0+(1371455207/2500000000 : ℝ)*X 0 1+(256275031/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347960813/10000000000 : ℝ)*X 1 0+(-799700119/5000000000 : ℝ)*X 1 1+(2562749837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347959419/10000000000 : ℝ)*X 2 0+(64068761/125000000 : ℝ)*X 2 1+(-199925063/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1025782691/2500000000 : ℝ)*X 0 0+(3602973129/10000000000 : ℝ)*X 0 1+(4645240957/10000000000 : ℝ)*X 0 2+(1025782691/2500000000 : ℝ)*X 1 0+(3602973129/10000000000 : ℝ)*X 1 1+(4645240957/10000000000 : ℝ)*X 1 2+(1025782691/2500000000 : ℝ)*X 2 0+(3602973129/10000000000 : ℝ)*X 2 1+(4645240957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1412180917/10000000000 : ℝ)*X 0 0+(5129817613/10000000000 : ℝ)*X 0 1+(2740716677/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1312869221/2500000000 : ℝ)*X 1 0+(-248693379/2000000000 : ℝ)*X 1 1+(2740716567/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251476937/10000000000 : ℝ)*X 2 0+(68517911/125000000 : ℝ)*X 2 1+(-1243467181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4103686987/10000000000 : ℝ)*X 0 0+(4632752611/10000000000 : ℝ)*X 0 1+(3615662419/10000000000 : ℝ)*X 0 2+(4103686987/10000000000 : ℝ)*X 1 0+(4632752611/10000000000 : ℝ)*X 1 1+(3615662419/10000000000 : ℝ)*X 1 2+(4103686987/10000000000 : ℝ)*X 2 0+(4632752611/10000000000 : ℝ)*X 2 1+(3615662419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (217243758793840207992651/15923000000000000000000000000 : ℝ) := by norm_num
    linear_combination (333820127/20000000000000 : ℝ)*(base19) + (216330859/25000000000000 : ℝ)*(base23) + (109888971/100000000000000 : ℝ)*(lower2) + (82277121/25000000000000 : ℝ)*(upper3) + (6691283/10000000000000 : ℝ)*(lower4) + (93369543683413/5000000000000 : ℝ)*(major0) + (93369543683413/5000000000000 : ℝ)*(major1) + (93369543683413/5000000000000 : ℝ)*(major2) + (173457679184009/6250000000000 : ℝ)*(sp0) + (346915929191417/12500000000000 : ℝ)*(sp1) + (346916029663567/12500000000000 : ℝ)*(sp2) + (59965536759221/6250000000000 : ℝ)*(sp3) + (6235687827/100000000000000 : ℝ)*(sp4) + (720355443/20000000000000 : ℝ)*(sp7) + (959452189924751/100000000000000 : ℝ)*(f.failure) + (2775329102631971/100000000000000 : ℝ)*(f.sum) + (16273439881709/7961500000000000000000000000 : ℝ)*base66 + (1266658813335261439/199037500000000000000000000000000 : ℝ)*base67 + (362068907108601061/199037500000000000000000000000000 : ℝ)*base70 + (494833547463323939/199037500000000000000000000000000 : ℝ)*base71 + (564387181921/15923000000000000000000000000 : ℝ)*base73 + (702389877636076061/199037500000000000000000000000000 : ℝ)*base76 + (1455236375013723939/199037500000000000000000000000000 : ℝ)*base77 + (349004904448876061/199037500000000000000000000000000 : ℝ)*base80 + (2296865728759/636920000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (22027777/5000000000000000000000 : ℝ)*base90 + (22027777/5000000000000000000000 : ℝ)*base92 + (22027777/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3125228624178137616046315971/995187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444859327/50000000000000 : ℝ)*(base19) + (15843177/1562500000000 : ℝ)*(base23) + (32732661/50000000000000 : ℝ)*(upper2) + (56618781/50000000000000 : ℝ)*(upper3) + (26866931/20000000000000 : ℝ)*(upper5) + (956802494108827/50000000000000 : ℝ)*(major0) + (956802494108827/50000000000000 : ℝ)*(major1) + (956802494108827/50000000000000 : ℝ)*(major2) + (127113349/2000000000000 : ℝ)*(sp1) + (2385417169/50000000000000 : ℝ)*(sp2) + (1422006598731957/50000000000000 : ℝ)*(sp4) + (284400595207781/10000000000000 : ℝ)*(sp5) + (355500926583281/12500000000000 : ℝ)*(sp6) + (983196674293333/100000000000000 : ℝ)*(sp7) + (983196674293333/100000000000000 : ℝ)*(f.failure) + (1422006598731957/50000000000000 : ℝ)*(f.sum) + (15192418383567/79615000000000000000000000000 : ℝ)*base66 + (5733119090601766281/1990375000000000000000000000000000 : ℝ)*base67 + (10441987400355016281/1990375000000000000000000000000000 : ℝ)*base69 + (20179701079705766281/1990375000000000000000000000000000 : ℝ)*base71 + (313880899344767/79615000000000000000000000000 : ℝ)*base74 + (9453606417588516281/1990375000000000000000000000000000 : ℝ)*base75 + (13408303798120266281/1990375000000000000000000000000000 : ℝ)*base77 + (15610286563182516281/1990375000000000000000000000000000 : ℝ)*base79 + (318701577563277/79615000000000000000000000000 : ℝ)*base82 + (58358491/5000000000000000000000 : ℝ)*base90 + (58358491/5000000000000000000000 : ℝ)*base92 + (58358491/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1709_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2743/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6021/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4863/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8709/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1709_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1709_s2_0 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-707777049/5000000000 : ℝ)*x 0 + (2735609591/5000000000 : ℝ)*x 1 + (5137715097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (707777049/5000000000 : ℝ)^5295 ≤ (4429202950397/50000000000000 : ℝ)^4271 := by
    have hnat : (707777049 : ℕ)^5295*50000000000000^4271 ≤ 4429202950397^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707777049 5000000000 4429202950397 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735609591/5000000000 : ℝ)^5295 ≤ (473465215481/1000000000000 : ℝ)^4271 := by
    have hnat : (2735609591 : ℕ)^5295*1000000000000^4271 ≤ 473465215481^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735609591 5000000000 473465215481 1000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137715097/10000000000 : ℝ)^5295 ≤ (21897536271401/50000000000000 : ℝ)^4271 := by
    have hnat : (5137715097 : ℕ)^5295*50000000000000^4271 ≤ 21897536271401^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137715097 10000000000 21897536271401 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-707777049/5000000000 : ℝ), (2735609591/5000000000 : ℝ), (5137715097/10000000000 : ℝ)] ![(4429202950397/50000000000000 : ℝ), (473465215481/1000000000000 : ℝ), (21897536271401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-707777049/5000000000 : ℝ)|^5295 ≤ (4429202950397/50000000000000 : ℝ)^4271
        have hw : |(-707777049/5000000000 : ℝ)|=(707777049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735609591/5000000000 : ℝ)|^5295 ≤ (473465215481/1000000000000 : ℝ)^4271
        have hw : |(2735609591/5000000000 : ℝ)|=(2735609591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137715097/10000000000 : ℝ)|^5295 ≤ (21897536271401/50000000000000 : ℝ)^4271
        have hw : |(5137715097/10000000000 : ℝ)|=(5137715097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s2_1 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068801137/2000000000 : ℝ)*x 0 + (-397129791/2500000000 : ℝ)*x 1 + (1027542977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068801137/2000000000 : ℝ)^5295 ≤ (2299276707089/5000000000000 : ℝ)^4271 := by
    have hnat : (1068801137 : ℕ)^5295*5000000000000^4271 ≤ 2299276707089^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068801137 2000000000 2299276707089 5000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397129791/2500000000 : ℝ)^5295 ≤ (10219395547521/100000000000000 : ℝ)^4271 := by
    have hnat : (397129791 : ℕ)^5295*100000000000000^4271 ≤ 10219395547521^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397129791 2500000000 10219395547521 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027542977/2000000000 : ℝ)^5295 ≤ (5474383787799/12500000000000 : ℝ)^4271 := by
    have hnat : (1027542977 : ℕ)^5295*12500000000000^4271 ≤ 5474383787799^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027542977 2000000000 5474383787799 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068801137/2000000000 : ℝ), (-397129791/2500000000 : ℝ), (1027542977/2000000000 : ℝ)] ![(2299276707089/5000000000000 : ℝ), (10219395547521/100000000000000 : ℝ), (5474383787799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068801137/2000000000 : ℝ)|^5295 ≤ (2299276707089/5000000000000 : ℝ)^4271
        have hw : |(1068801137/2000000000 : ℝ)|=(1068801137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397129791/2500000000 : ℝ)|^5295 ≤ (10219395547521/100000000000000 : ℝ)^4271
        have hw : |(-397129791/2500000000 : ℝ)|=(397129791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027542977/2000000000 : ℝ)|^5295 ≤ (5474383787799/12500000000000 : ℝ)^4271
        have hw : |(1027542977/2000000000 : ℝ)|=(1027542977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s2_2 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344006063/10000000000 : ℝ)*x 0 + (5137714951/10000000000 : ℝ)*x 1 + (-158851857/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344006063/10000000000 : ℝ)^5295 ≤ (9197107634871/20000000000000 : ℝ)^4271 := by
    have hnat : (5344006063 : ℕ)^5295*20000000000000^4271 ≤ 9197107634871^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344006063 10000000000 9197107634871 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137714951/10000000000 : ℝ)^5295 ≤ (21897535499939/50000000000000 : ℝ)^4271 := by
    have hnat : (5137714951 : ℕ)^5295*50000000000000^4271 ≤ 21897535499939^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137714951 10000000000 21897535499939 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158851857/1000000000 : ℝ)^5295 ≤ (319355962811/3125000000000 : ℝ)^4271 := by
    have hnat : (158851857 : ℕ)^5295*3125000000000^4271 ≤ 319355962811^4271*1000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158851857 1000000000 319355962811 3125000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344006063/10000000000 : ℝ), (5137714951/10000000000 : ℝ), (-158851857/1000000000 : ℝ)] ![(9197107634871/20000000000000 : ℝ), (21897535499939/50000000000000 : ℝ), (319355962811/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344006063/10000000000 : ℝ)|^5295 ≤ (9197107634871/20000000000000 : ℝ)^4271
        have hw : |(5344006063/10000000000 : ℝ)|=(5344006063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137714951/10000000000 : ℝ)|^5295 ≤ (21897535499939/50000000000000 : ℝ)^4271
        have hw : |(5137714951/10000000000 : ℝ)|=(5137714951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-158851857/1000000000 : ℝ)|^5295 ≤ (319355962811/3125000000000 : ℝ)^4271
        have hw : |(-158851857/1000000000 : ℝ)|=(158851857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s2_3 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32077289/78125000 : ℝ)*x 0 + (3641512709/10000000000 : ℝ)*x 1 + (4606211821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32077289/78125000 : ℝ)^5295 ≤ (16584011779977/50000000000000 : ℝ)^4271 := by
    have hnat : (32077289 : ℕ)^5295*50000000000000^4271 ≤ 16584011779977^4271*78125000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32077289 78125000 16584011779977 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3641512709/10000000000 : ℝ)^5295 ≤ (1429112120611/5000000000000 : ℝ)^4271 := by
    have hnat : (3641512709 : ℕ)^5295*5000000000000^4271 ≤ 1429112120611^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3641512709 10000000000 1429112120611 5000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4606211821/10000000000 : ℝ)^5295 ≤ (19124867010319/50000000000000 : ℝ)^4271 := by
    have hnat : (4606211821 : ℕ)^5295*50000000000000^4271 ≤ 19124867010319^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606211821 10000000000 19124867010319 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32077289/78125000 : ℝ), (3641512709/10000000000 : ℝ), (4606211821/10000000000 : ℝ)] ![(16584011779977/50000000000000 : ℝ), (1429112120611/5000000000000 : ℝ), (19124867010319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32077289/78125000 : ℝ)|^5295 ≤ (16584011779977/50000000000000 : ℝ)^4271
        have hw : |(32077289/78125000 : ℝ)|=(32077289/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3641512709/10000000000 : ℝ)|^5295 ≤ (1429112120611/5000000000000 : ℝ)^4271
        have hw : |(3641512709/10000000000 : ℝ)|=(3641512709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4606211821/10000000000 : ℝ)|^5295 ≤ (19124867010319/50000000000000 : ℝ)^4271
        have hw : |(4606211821/10000000000 : ℝ)|=(4606211821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s2_4 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-353926753/2500000000 : ℝ)*x 0 + (1028283227/2000000000 : ℝ)*x 1 + (5467462329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353926753/2500000000 : ℝ)^5295 ≤ (2214898066479/25000000000000 : ℝ)^4271 := by
    have hnat : (353926753 : ℕ)^5295*25000000000000^4271 ≤ 2214898066479^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353926753 2500000000 2214898066479 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028283227/2000000000 : ℝ)^5295 ≤ (43834188383187/100000000000000 : ℝ)^4271 := by
    have hnat : (1028283227 : ℕ)^5295*100000000000000^4271 ≤ 43834188383187^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028283227 2000000000 43834188383187 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467462329/10000000000 : ℝ)^5295 ≤ (23653109671781/50000000000000 : ℝ)^4271 := by
    have hnat : (5467462329 : ℕ)^5295*50000000000000^4271 ≤ 23653109671781^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467462329 10000000000 23653109671781 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353926753/2500000000 : ℝ), (1028283227/2000000000 : ℝ), (5467462329/10000000000 : ℝ)] ![(2214898066479/25000000000000 : ℝ), (43834188383187/100000000000000 : ℝ), (23653109671781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353926753/2500000000 : ℝ)|^5295 ≤ (2214898066479/25000000000000 : ℝ)^4271
        have hw : |(-353926753/2500000000 : ℝ)|=(353926753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028283227/2000000000 : ℝ)|^5295 ≤ (43834188383187/100000000000000 : ℝ)^4271
        have hw : |(1028283227/2000000000 : ℝ)|=(1028283227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467462329/10000000000 : ℝ)|^5295 ≤ (23653109671781/50000000000000 : ℝ)^4271
        have hw : |(5467462329/10000000000 : ℝ)|=(5467462329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s2_5 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164210529/312500000 : ℝ)*x 0 + (-314692819/2500000000 : ℝ)*x 1 + (1366865573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164210529/312500000 : ℝ)^5295 ≤ (1801404532931/4000000000000 : ℝ)^4271 := by
    have hnat : (164210529 : ℕ)^5295*4000000000000^4271 ≤ 1801404532931^4271*312500000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164210529 312500000 1801404532931 4000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314692819/2500000000 : ℝ)^5295 ≤ (7658667715597/100000000000000 : ℝ)^4271 := by
    have hnat : (314692819 : ℕ)^5295*100000000000000^4271 ≤ 7658667715597^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314692819 2500000000 7658667715597 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366865573/2500000000 : ℝ)^5295 ≤ (47306218946671/100000000000000 : ℝ)^4271 := by
    have hnat : (1366865573 : ℕ)^5295*100000000000000^4271 ≤ 47306218946671^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366865573 2500000000 47306218946671 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164210529/312500000 : ℝ), (-314692819/2500000000 : ℝ), (1366865573/2500000000 : ℝ)] ![(1801404532931/4000000000000 : ℝ), (7658667715597/100000000000000 : ℝ), (47306218946671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164210529/312500000 : ℝ)|^5295 ≤ (1801404532931/4000000000000 : ℝ)^4271
        have hw : |(164210529/312500000 : ℝ)|=(164210529/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-314692819/2500000000 : ℝ)|^5295 ≤ (7658667715597/100000000000000 : ℝ)^4271
        have hw : |(-314692819/2500000000 : ℝ)|=(314692819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366865573/2500000000 : ℝ)|^5295 ≤ (47306218946671/100000000000000 : ℝ)^4271
        have hw : |(1366865573/2500000000 : ℝ)|=(1366865573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s2_6 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313684217/2500000000 : ℝ)*x 0 + (5467462299/10000000000 : ℝ)*x 1 + (-25175427/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313684217/2500000000 : ℝ)^5295 ≤ (45035112685763/100000000000000 : ℝ)^4271 := by
    have hnat : (1313684217 : ℕ)^5295*100000000000000^4271 ≤ 45035112685763^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313684217 2500000000 45035112685763 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467462299/10000000000 : ℝ)^5295 ≤ (47306219021759/100000000000000 : ℝ)^4271 := by
    have hnat : (5467462299 : ℕ)^5295*100000000000000^4271 ≤ 47306219021759^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467462299 10000000000 47306219021759 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25175427/200000000 : ℝ)^5295 ≤ (7658668273777/100000000000000 : ℝ)^4271 := by
    have hnat : (25175427 : ℕ)^5295*100000000000000^4271 ≤ 7658668273777^4271*200000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25175427 200000000 7658668273777 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313684217/2500000000 : ℝ), (5467462299/10000000000 : ℝ), (-25175427/200000000 : ℝ)] ![(45035112685763/100000000000000 : ℝ), (47306219021759/100000000000000 : ℝ), (7658668273777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313684217/2500000000 : ℝ)|^5295 ≤ (45035112685763/100000000000000 : ℝ)^4271
        have hw : |(1313684217/2500000000 : ℝ)|=(1313684217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467462299/10000000000 : ℝ)|^5295 ≤ (47306219021759/100000000000000 : ℝ)^4271
        have hw : |(5467462299/10000000000 : ℝ)|=(5467462299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25175427/200000000 : ℝ)|^5295 ≤ (7658668273777/100000000000000 : ℝ)^4271
        have hw : |(-25175427/200000000 : ℝ)|=(25175427/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s2_7 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (821266781/2000000000 : ℝ)*x 0 + (1148876403/2500000000 : ℝ)*x 1 + (913094659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821266781/2000000000 : ℝ)^5295 ≤ (16586219667059/50000000000000 : ℝ)^4271 := by
    have hnat : (821266781 : ℕ)^5295*50000000000000^4271 ≤ 16586219667059^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821266781 2000000000 16586219667059 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1148876403/2500000000 : ℝ)^5295 ≤ (9534886427337/25000000000000 : ℝ)^4271 := by
    have hnat : (1148876403 : ℕ)^5295*25000000000000^4271 ≤ 9534886427337^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148876403 2500000000 9534886427337 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (913094659/2500000000 : ℝ)^5295 ≤ (28688014931547/100000000000000 : ℝ)^4271 := by
    have hnat : (913094659 : ℕ)^5295*100000000000000^4271 ≤ 28688014931547^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913094659 2500000000 28688014931547 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(821266781/2000000000 : ℝ), (1148876403/2500000000 : ℝ), (913094659/2500000000 : ℝ)] ![(16586219667059/50000000000000 : ℝ), (9534886427337/25000000000000 : ℝ), (28688014931547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(821266781/2000000000 : ℝ)|^5295 ≤ (16586219667059/50000000000000 : ℝ)^4271
        have hw : |(821266781/2000000000 : ℝ)|=(821266781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1148876403/2500000000 : ℝ)|^5295 ≤ (9534886427337/25000000000000 : ℝ)^4271
        have hw : |(1148876403/2500000000 : ℝ)|=(1148876403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(913094659/2500000000 : ℝ)|^5295 ≤ (28688014931547/100000000000000 : ℝ)^4271
        have hw : |(913094659/2500000000 : ℝ)|=(913094659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1709_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8709/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4863/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1249/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2139/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8709/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4863/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8709/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4863/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8709/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4863/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8709/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4863/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8709/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4863/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8709/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4863/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4863/50000 : ℝ) ^ (5287/1024 : ℝ) ≤ (595137939459907/100000000000000000000 : ℝ) := by
    have hpowers : (4863/50000 : ℝ)^5287 ≤ (595137939459907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4863 : ℕ)^5287*100000000000000000000^1024 ≤ 595137939459907^1024*50000^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4863 50000 595137939459907 100000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4863/50000 : ℝ)) (X := (595137939459907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8709/50000 : ℝ) ^ (5287/1024 : ℝ) ≤ (482246313449649/4000000000000000000 : ℝ) := by
    have hpowers : (8709/50000 : ℝ)^5287 ≤ (482246313449649/4000000000000000000 : ℝ)^1024 := by
      have hnat : (8709 : ℕ)^5287*4000000000000000000^1024 ≤ 482246313449649^1024*50000^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8709 50000 482246313449649 4000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8709/50000 : ℝ)) (X := (482246313449649/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000595137939459907/50000000000000000000 : ℝ) ≤ (500001152673209/500000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (50000595137939459907/50000000000000000000 : ℝ)^1024 ≤ (500001152673209/500000000000000 : ℝ)^5287 := by
      have hnat : (50000595137939459907 : ℕ)^1024*500000000000000^5287 ≤ 500001152673209^5287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000595137939459907 50000000000000000000 500001152673209 500000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500001152673209/500000000000000 : ℝ)) (X := (50000595137939459907/50000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003162823943925283/25000000000000000000 : ℝ) ≤ (10000245021111429/10000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (25003162823943925283/25000000000000000000 : ℝ)^1024 ≤ (10000245021111429/10000000000000000 : ℝ)^5287 := by
      have hnat : (25003162823943925283 : ℕ)^1024*10000000000000000^5287 ≤ 10000245021111429^5287*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003162823943925283 25000000000000000000 10000245021111429 10000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000245021111429/10000000000000000 : ℝ)) (X := (25003162823943925283/25000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000482246313449649/2000000000000000000 : ℝ) ≤ (5000233494379339/5000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (2000482246313449649/2000000000000000000 : ℝ)^1024 ≤ (5000233494379339/5000000000000000 : ℝ)^5287 := by
      have hnat : (2000482246313449649 : ℕ)^1024*5000000000000000^5287 ≤ 5000233494379339^5287*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000482246313449649 2000000000000000000 5000233494379339 5000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000233494379339/5000000000000000 : ℝ)) (X := (2000482246313449649/2000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(595137939459907/100000000000000000000 : ℝ) ≤ ((6409654967714348751/6410000000000000000 : ℝ)+2*(221967647249/769200000000000 : ℝ)*(4863/50000 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (6409654967714348751/6410000000000000000 : ℝ)+2*(221967647249/769200000000000 : ℝ)*(4863/50000 : ℝ)=(500001152673209/500000000000000 : ℝ) by norm_num, show 1+2*(595137939459907/100000000000000000000 : ℝ)=(50000595137939459907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(482246313449649/4000000000000000000 : ℝ)+(595137939459907/100000000000000000000 : ℝ) ≤ ((6409654967714348751/6410000000000000000 : ℝ)+(221967647249/769200000000000 : ℝ)*((8709/50000 : ℝ)+(4863/50000 : ℝ)))^(5287/1024 : ℝ) := by
    rw [show (6409654967714348751/6410000000000000000 : ℝ)+(221967647249/769200000000000 : ℝ)*((8709/50000 : ℝ)+(4863/50000 : ℝ))=(10000245021111429/10000000000000000 : ℝ) by norm_num, show 1+(482246313449649/4000000000000000000 : ℝ)+(595137939459907/100000000000000000000 : ℝ)=(25003162823943925283/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(482246313449649/4000000000000000000 : ℝ) ≤ ((6409654967714348751/6410000000000000000 : ℝ)+2*(221967647249/769200000000000 : ℝ)*(8709/50000 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (6409654967714348751/6410000000000000000 : ℝ)+2*(221967647249/769200000000000 : ℝ)*(8709/50000 : ℝ)=(5000233494379339/5000000000000000 : ℝ) by norm_num, show 1+2*(482246313449649/4000000000000000000 : ℝ)=(2000482246313449649/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6409654967714348751/6410000000000000000 : ℝ)*(X 1 0+X 2 0)+(221967647249/769200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (4863/50000 : ℝ)) (hi := (8709/50000 : ℝ)) (c := (6409654967714348751/6410000000000000000 : ℝ)) (alpha := (221967647249/769200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6409654967714348751/6410000000000000000 : ℝ)*(X 0 1+X 2 1)+(221967647249/769200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (4863/50000 : ℝ)) (hi := (8709/50000 : ℝ)) (c := (6409654967714348751/6410000000000000000 : ℝ)) (alpha := (221967647249/769200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6409654967714348751/6410000000000000000 : ℝ)*(X 0 2+X 1 2)+(221967647249/769200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (4863/50000 : ℝ)) (hi := (8709/50000 : ℝ)) (c := (6409654967714348751/6410000000000000000 : ℝ)) (alpha := (221967647249/769200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-707777049/5000000000 : ℝ)*X 0 0+(2735609591/5000000000 : ℝ)*X 0 1+(5137715097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068801137/2000000000 : ℝ)*X 1 0+(-397129791/2500000000 : ℝ)*X 1 1+(1027542977/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344006063/10000000000 : ℝ)*X 2 0+(5137714951/10000000000 : ℝ)*X 2 1+(-158851857/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((32077289/78125000 : ℝ)*X 0 0+(3641512709/10000000000 : ℝ)*X 0 1+(4606211821/10000000000 : ℝ)*X 0 2+(32077289/78125000 : ℝ)*X 1 0+(3641512709/10000000000 : ℝ)*X 1 1+(4606211821/10000000000 : ℝ)*X 1 2+(32077289/78125000 : ℝ)*X 2 0+(3641512709/10000000000 : ℝ)*X 2 1+(4606211821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-353926753/2500000000 : ℝ)*X 0 0+(1028283227/2000000000 : ℝ)*X 0 1+(5467462329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((164210529/312500000 : ℝ)*X 1 0+(-314692819/2500000000 : ℝ)*X 1 1+(1366865573/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313684217/2500000000 : ℝ)*X 2 0+(5467462299/10000000000 : ℝ)*X 2 1+(-25175427/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((821266781/2000000000 : ℝ)*X 0 0+(1148876403/2500000000 : ℝ)*X 0 1+(913094659/2500000000 : ℝ)*X 0 2+(821266781/2000000000 : ℝ)*X 1 0+(1148876403/2500000000 : ℝ)*X 1 1+(913094659/2500000000 : ℝ)*X 1 2+(821266781/2000000000 : ℝ)*X 2 0+(1148876403/2500000000 : ℝ)*X 2 1+(913094659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2153010644149035240190880703/160250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5572267/400000000000 : ℝ)*(base19) + (1192673291/100000000000000 : ℝ)*(base23) + (220433199/100000000000000 : ℝ)*(lower2) + (111991533/100000000000000 : ℝ)*(upper3) + (221058399/100000000000000 : ℝ)*(upper5) + (1008772258090651/50000000000000 : ℝ)*(major0) + (1008772258090651/50000000000000 : ℝ)*(major1) + (1008772258090651/50000000000000 : ℝ)*(major2) + (1499236650180851/50000000000000 : ℝ)*(sp0) + (1499243562343373/50000000000000 : ℝ)*(sp1) + (1499243662540103/50000000000000 : ℝ)*(sp2) + (1036596116713487/100000000000000 : ℝ)*(sp3) + (3043478359/20000000000000 : ℝ)*(sp4) + (123439109/3125000000000 : ℝ)*(sp7) + (41464002670599/4000000000000 : ℝ)*(f.failure) + (374811064719187/12500000000000 : ℝ)*(f.sum) + (38551489663259/19230000000000000000000000000 : ℝ)*base65 + (6750445663634644297/961500000000000000000000000000000 : ℝ)*base68 + (2492355240218644297/961500000000000000000000000000000 : ℝ)*base70 + (3489435372816355703/961500000000000000000000000000000 : ℝ)*base71 + (79966734552751/19230000000000000000000000000 : ℝ)*base74 + (1688741771620144297/961500000000000000000000000000000 : ℝ)*base76 + (4545952783415644297/961500000000000000000000000000000 : ℝ)*base78 + (277946442319855703/961500000000000000000000000000000 : ℝ)*base79 + (37471679645849/19230000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (878327/200000000000000000000 : ℝ)*base89 + (878327/200000000000000000000 : ℝ)*base91 + (878327/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4012315060946840320769240217/320500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171487837/10000000000000 : ℝ)*(base19) + (907470921/50000000000000 : ℝ)*(base23) + (248745907/100000000000000 : ℝ)*(upper3) + (70377021/100000000000000 : ℝ)*(lower4) + (140166413/50000000000000 : ℝ)*(upper5) + (2063676105832989/100000000000000 : ℝ)*(major0) + (2063676105832989/100000000000000 : ℝ)*(major1) + (2063676105832989/100000000000000 : ℝ)*(major2) + (7842079811/50000000000000 : ℝ)*(sp1) + (15751965929/100000000000000 : ℝ)*(sp2) + (766762410985561/25000000000000 : ℝ)*(sp4) + (766758061226063/25000000000000 : ℝ)*(sp5) + (1533516038517237/50000000000000 : ℝ)*(sp6) + (265075537606567/25000000000000 : ℝ)*(sp7) + (265075537606567/25000000000000 : ℝ)*(f.failure) + (766762410985561/25000000000000 : ℝ)*(f.sum) + (26921628433247/12820000000000000000000000000 : ℝ)*base65 + (1527480515187921739/641000000000000000000000000000000 : ℝ)*base67 + (2108664910100078261/641000000000000000000000000000000 : ℝ)*base70 + (609720746277921739/641000000000000000000000000000000 : ℝ)*base71 + (79750888973167/12820000000000000000000000000 : ℝ)*base73 + (4354801200798078261/641000000000000000000000000000000 : ℝ)*base76 + (4618368860875078261/641000000000000000000000000000000 : ℝ)*base78 + (6853269667677078261/641000000000000000000000000000000 : ℝ)*base80 + (537368111673/12820000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6988809/1250000000000000000000 : ℝ)*base90 + (6988809/1250000000000000000000 : ℝ)*base92 + (6988809/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1709_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8709/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4863/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2139/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1709_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1709_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2139/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1709_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1709_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1709_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2139/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1709_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

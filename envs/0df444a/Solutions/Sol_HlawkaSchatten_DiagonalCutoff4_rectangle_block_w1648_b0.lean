-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1648_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:12:33.577852+00:00
-- url     : https://prove2.me/submissions/a94e448f-11dd-4fc5-a93f-c574bff41082

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
theorem support_rectangle_w1648_s0_0 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-748086191/5000000000 : ℝ)*x 0 + (361736209/625000000 : ℝ)*x 1 + (1230049881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (748086191/5000000000 : ℝ)^4911 ≤ (4535309700979/50000000000000 : ℝ)^3887 := by
    have hnat : (748086191 : ℕ)^4911*50000000000000^3887 ≤ 4535309700979^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748086191 5000000000 4535309700979 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (361736209/625000000 : ℝ)^4911 ≤ (25056337445997/50000000000000 : ℝ)^3887 := by
    have hnat : (361736209 : ℕ)^4911*50000000000000^3887 ≤ 25056337445997^3887*625000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361736209 625000000 25056337445997 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1230049881/2500000000 : ℝ)^4911 ≤ (20408352846541/50000000000000 : ℝ)^3887 := by
    have hnat : (1230049881 : ℕ)^4911*50000000000000^3887 ≤ 20408352846541^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230049881 2500000000 20408352846541 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-748086191/5000000000 : ℝ), (361736209/625000000 : ℝ), (1230049881/2500000000 : ℝ)] ![(4535309700979/50000000000000 : ℝ), (25056337445997/50000000000000 : ℝ), (20408352846541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-748086191/5000000000 : ℝ)|^4911 ≤ (4535309700979/50000000000000 : ℝ)^3887
        have hw : |(-748086191/5000000000 : ℝ)|=(748086191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(361736209/625000000 : ℝ)|^4911 ≤ (25056337445997/50000000000000 : ℝ)^3887
        have hw : |(361736209/625000000 : ℝ)|=(361736209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1230049881/2500000000 : ℝ)|^4911 ≤ (20408352846541/50000000000000 : ℝ)^3887
        have hw : |(1230049881/2500000000 : ℝ)|=(1230049881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s0_1 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5438330573/10000000000 : ℝ)*x 0 + (-986304489/5000000000 : ℝ)*x 1 + (615024979/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5438330573/10000000000 : ℝ)^4911 ≤ (46320801764427/100000000000000 : ℝ)^3887 := by
    have hnat : (5438330573 : ℕ)^4911*100000000000000^3887 ≤ 46320801764427^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438330573 10000000000 46320801764427 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986304489/5000000000 : ℝ)^4911 ≤ (6431244648479/50000000000000 : ℝ)^3887 := by
    have hnat : (986304489 : ℕ)^4911*50000000000000^3887 ≤ 6431244648479^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986304489 5000000000 6431244648479 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615024979/1250000000 : ℝ)^4911 ≤ (40816708921289/100000000000000 : ℝ)^3887 := by
    have hnat : (615024979 : ℕ)^4911*100000000000000^3887 ≤ 40816708921289^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615024979 1250000000 40816708921289 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5438330573/10000000000 : ℝ), (-986304489/5000000000 : ℝ), (615024979/1250000000 : ℝ)] ![(46320801764427/100000000000000 : ℝ), (6431244648479/50000000000000 : ℝ), (40816708921289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5438330573/10000000000 : ℝ)|^4911 ≤ (46320801764427/100000000000000 : ℝ)^3887
        have hw : |(5438330573/10000000000 : ℝ)|=(5438330573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-986304489/5000000000 : ℝ)|^4911 ≤ (6431244648479/50000000000000 : ℝ)^3887
        have hw : |(-986304489/5000000000 : ℝ)|=(986304489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(615024979/1250000000 : ℝ)|^4911 ≤ (40816708921289/100000000000000 : ℝ)^3887
        have hw : |(615024979/1250000000 : ℝ)|=(615024979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s0_2 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5438331037/10000000000 : ℝ)*x 0 + (984039881/2000000000 : ℝ)*x 1 + (-394521783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5438331037/10000000000 : ℝ)^4911 ≤ (46320806757683/100000000000000 : ℝ)^3887 := by
    have hnat : (5438331037 : ℕ)^4911*100000000000000^3887 ≤ 46320806757683^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438331037 10000000000 46320806757683 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984039881/2000000000 : ℝ)^4911 ≤ (2040835222291/5000000000000 : ℝ)^3887 := by
    have hnat : (984039881 : ℕ)^4911*5000000000000^3887 ≤ 2040835222291^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984039881 2000000000 2040835222291 5000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394521783/2000000000 : ℝ)^4911 ≤ (12862488777943/100000000000000 : ℝ)^3887 := by
    have hnat : (394521783 : ℕ)^4911*100000000000000^3887 ≤ 12862488777943^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394521783 2000000000 12862488777943 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5438331037/10000000000 : ℝ), (984039881/2000000000 : ℝ), (-394521783/2000000000 : ℝ)] ![(46320806757683/100000000000000 : ℝ), (2040835222291/5000000000000 : ℝ), (12862488777943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5438331037/10000000000 : ℝ)|^4911 ≤ (46320806757683/100000000000000 : ℝ)^3887
        have hw : |(5438331037/10000000000 : ℝ)|=(5438331037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(984039881/2000000000 : ℝ)|^4911 ≤ (2040835222291/5000000000000 : ℝ)^3887
        have hw : |(984039881/2000000000 : ℝ)|=(984039881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394521783/2000000000 : ℝ)|^4911 ≤ (12862488777943/100000000000000 : ℝ)^3887
        have hw : |(-394521783/2000000000 : ℝ)|=(394521783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s0_3 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32732427/80000000 : ℝ)*x 0 + (1541058203/5000000000 : ℝ)*x 1 + (1064221947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32732427/80000000 : ℝ)^4911 ≤ (32332790126897/100000000000000 : ℝ)^3887 := by
    have hnat : (32732427 : ℕ)^4911*100000000000000^3887 ≤ 32332790126897^3887*80000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32732427 80000000 32332790126897 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1541058203/5000000000 : ℝ)^4911 ≤ (282553241447/1250000000000 : ℝ)^3887 := by
    have hnat : (1541058203 : ℕ)^4911*1250000000000^3887 ≤ 282553241447^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541058203 5000000000 282553241447 1250000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064221947/2000000000 : ℝ)^4911 ≤ (22531475271933/50000000000000 : ℝ)^3887 := by
    have hnat : (1064221947 : ℕ)^4911*50000000000000^3887 ≤ 22531475271933^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064221947 2000000000 22531475271933 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32732427/80000000 : ℝ), (1541058203/5000000000 : ℝ), (1064221947/2000000000 : ℝ)] ![(32332790126897/100000000000000 : ℝ), (282553241447/1250000000000 : ℝ), (22531475271933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32732427/80000000 : ℝ)|^4911 ≤ (32332790126897/100000000000000 : ℝ)^3887
        have hw : |(32732427/80000000 : ℝ)|=(32732427/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1541058203/5000000000 : ℝ)|^4911 ≤ (282553241447/1250000000000 : ℝ)^3887
        have hw : |(1541058203/5000000000 : ℝ)|=(1541058203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1064221947/2000000000 : ℝ)|^4911 ≤ (22531475271933/50000000000000 : ℝ)^3887
        have hw : |(1064221947/2000000000 : ℝ)|=(1064221947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s0_4 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1498491877/10000000000 : ℝ)*x 0 + (988348791/2000000000 : ℝ)*x 1 + (1441372391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1498491877/10000000000 : ℝ)^4911 ≤ (454419481063/5000000000000 : ℝ)^3887 := by
    have hnat : (1498491877 : ℕ)^4911*5000000000000^3887 ≤ 454419481063^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498491877 10000000000 454419481063 5000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (988348791/2000000000 : ℝ)^4911 ≤ (1282582721531/3125000000000 : ℝ)^3887 := by
    have hnat : (988348791 : ℕ)^4911*3125000000000^3887 ≤ 1282582721531^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988348791 2000000000 1282582721531 3125000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1441372391/2500000000 : ℝ)^4911 ≤ (49868963280931/100000000000000 : ℝ)^3887 := by
    have hnat : (1441372391 : ℕ)^4911*100000000000000^3887 ≤ 49868963280931^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441372391 2500000000 49868963280931 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1498491877/10000000000 : ℝ), (988348791/2000000000 : ℝ), (1441372391/2500000000 : ℝ)] ![(454419481063/5000000000000 : ℝ), (1282582721531/3125000000000 : ℝ), (49868963280931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1498491877/10000000000 : ℝ)|^4911 ≤ (454419481063/5000000000000 : ℝ)^3887
        have hw : |(-1498491877/10000000000 : ℝ)|=(1498491877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(988348791/2000000000 : ℝ)|^4911 ≤ (1282582721531/3125000000000 : ℝ)^3887
        have hw : |(988348791/2000000000 : ℝ)|=(988348791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1441372391/2500000000 : ℝ)|^4911 ≤ (49868963280931/100000000000000 : ℝ)^3887
        have hw : |(1441372391/2500000000 : ℝ)|=(1441372391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s0_5 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2600785639/5000000000 : ℝ)*x 0 + (-225463901/2000000000 : ℝ)*x 1 + (5765489213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2600785639/5000000000 : ℝ)^4911 ≤ (21893863622251/50000000000000 : ℝ)^3887 := by
    have hnat : (2600785639 : ℕ)^4911*50000000000000^3887 ≤ 21893863622251^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600785639 5000000000 21893863622251 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225463901/2000000000 : ℝ)^4911 ≤ (3171656649683/50000000000000 : ℝ)^3887 := by
    have hnat : (225463901 : ℕ)^4911*50000000000000^3887 ≤ 3171656649683^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225463901 2000000000 3171656649683 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5765489213/10000000000 : ℝ)^4911 ≤ (398951675561/800000000000 : ℝ)^3887 := by
    have hnat : (5765489213 : ℕ)^4911*800000000000^3887 ≤ 398951675561^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5765489213 10000000000 398951675561 800000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2600785639/5000000000 : ℝ), (-225463901/2000000000 : ℝ), (5765489213/10000000000 : ℝ)] ![(21893863622251/50000000000000 : ℝ), (3171656649683/50000000000000 : ℝ), (398951675561/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2600785639/5000000000 : ℝ)|^4911 ≤ (21893863622251/50000000000000 : ℝ)^3887
        have hw : |(2600785639/5000000000 : ℝ)|=(2600785639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-225463901/2000000000 : ℝ)|^4911 ≤ (3171656649683/50000000000000 : ℝ)^3887
        have hw : |(-225463901/2000000000 : ℝ)|=(225463901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5765489213/10000000000 : ℝ)|^4911 ≤ (398951675561/800000000000 : ℝ)^3887
        have hw : |(5765489213/10000000000 : ℝ)|=(5765489213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s0_6 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040314123/2000000000 : ℝ)*x 0 + (5765490019/10000000000 : ℝ)*x 1 + (-1127319257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040314123/2000000000 : ℝ)^4911 ≤ (10946930048229/25000000000000 : ℝ)^3887 := by
    have hnat : (1040314123 : ℕ)^4911*25000000000000^3887 ≤ 10946930048229^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040314123 2000000000 10946930048229 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5765490019/10000000000 : ℝ)^4911 ≤ (6233621031659/12500000000000 : ℝ)^3887 := by
    have hnat : (5765490019 : ℕ)^4911*12500000000000^3887 ≤ 6233621031659^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5765490019 10000000000 6233621031659 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127319257/10000000000 : ℝ)^4911 ≤ (6343311536269/100000000000000 : ℝ)^3887 := by
    have hnat : (1127319257 : ℕ)^4911*100000000000000^3887 ≤ 6343311536269^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127319257 10000000000 6343311536269 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040314123/2000000000 : ℝ), (5765490019/10000000000 : ℝ), (-1127319257/10000000000 : ℝ)] ![(10946930048229/25000000000000 : ℝ), (6233621031659/12500000000000 : ℝ), (6343311536269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040314123/2000000000 : ℝ)|^4911 ≤ (10946930048229/25000000000000 : ℝ)^3887
        have hw : |(1040314123/2000000000 : ℝ)|=(1040314123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5765490019/10000000000 : ℝ)|^4911 ≤ (6233621031659/12500000000000 : ℝ)^3887
        have hw : |(5765490019/10000000000 : ℝ)|=(5765490019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127319257/10000000000 : ℝ)|^4911 ≤ (6343311536269/100000000000000 : ℝ)^3887
        have hw : |(-1127319257/10000000000 : ℝ)|=(1127319257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s0_7 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4097538579/10000000000 : ℝ)*x 0 + (1316377351/2500000000 : ℝ)*x 1 + (3139639533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4097538579/10000000000 : ℝ)^4911 ≤ (16196279354757/50000000000000 : ℝ)^3887 := by
    have hnat : (4097538579 : ℕ)^4911*50000000000000^3887 ≤ 16196279354757^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097538579 10000000000 16196279354757 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316377351/2500000000 : ℝ)^4911 ≤ (1778754518091/4000000000000 : ℝ)^3887 := by
    have hnat : (1316377351 : ℕ)^4911*4000000000000^3887 ≤ 1778754518091^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316377351 2500000000 1778754518091 4000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3139639533/10000000000 : ℝ)^4911 ≤ (5784644583621/25000000000000 : ℝ)^3887 := by
    have hnat : (3139639533 : ℕ)^4911*25000000000000^3887 ≤ 5784644583621^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3139639533 10000000000 5784644583621 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4097538579/10000000000 : ℝ), (1316377351/2500000000 : ℝ), (3139639533/10000000000 : ℝ)] ![(16196279354757/50000000000000 : ℝ), (1778754518091/4000000000000 : ℝ), (5784644583621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4097538579/10000000000 : ℝ)|^4911 ≤ (16196279354757/50000000000000 : ℝ)^3887
        have hw : |(4097538579/10000000000 : ℝ)|=(4097538579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316377351/2500000000 : ℝ)|^4911 ≤ (1778754518091/4000000000000 : ℝ)^3887
        have hw : |(1316377351/2500000000 : ℝ)|=(1316377351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3139639533/10000000000 : ℝ)|^4911 ≤ (5784644583621/25000000000000 : ℝ)^3887
        have hw : |(3139639533/10000000000 : ℝ)|=(3139639533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1648_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (961/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23399/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4907/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4907 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4907*1^1024 ≤ 0^1024*1^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4907/1024 : ℝ) ≤ (1239009360335268149/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4907 ≤ (1239009360335268149/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4907*100000000000000000000^1024 ≤ 1239009360335268149^1024*5^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1239009360335268149 100000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1239009360335268149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4907 := by
      have hnat : (1 : ℕ)^1024*1^4907 ≤ 1^4907*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101239009360335268149/100000000000000000000 : ℝ) ≤ (1253216250995451/1250000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (101239009360335268149/100000000000000000000 : ℝ)^1024 ≤ (1253216250995451/1250000000000000 : ℝ)^4907 := by
      have hnat : (101239009360335268149 : ℕ)^1024*1250000000000000^4907 ≤ 1253216250995451^4907*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101239009360335268149 100000000000000000000 1253216250995451 1250000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253216250995451/1250000000000000 : ℝ)) (X := (101239009360335268149/100000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51239009360335268149/50000000000000000000 : ℝ) ≤ (628216250995451/625000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (51239009360335268149/50000000000000000000 : ℝ)^1024 ≤ (628216250995451/625000000000000 : ℝ)^4907 := by
      have hnat : (51239009360335268149 : ℕ)^1024*625000000000000^4907 ≤ 628216250995451^4907*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51239009360335268149 50000000000000000000 628216250995451 625000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628216250995451/625000000000000 : ℝ)) (X := (51239009360335268149/50000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3216250995451/500000000000000 : ℝ)*(0 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3216250995451/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1239009360335268149/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3216250995451/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4907/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3216250995451/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1253216250995451/1250000000000000 : ℝ) by norm_num, show 1+(1239009360335268149/100000000000000000000 : ℝ)+(0 : ℝ)=(101239009360335268149/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1239009360335268149/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3216250995451/500000000000000 : ℝ)*(2/5 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3216250995451/500000000000000 : ℝ)*(2/5 : ℝ)=(628216250995451/625000000000000 : ℝ) by norm_num, show 1+2*(1239009360335268149/100000000000000000000 : ℝ)=(51239009360335268149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3216250995451/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3216250995451/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3216250995451/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3216250995451/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3216250995451/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3216250995451/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-748086191/5000000000 : ℝ)*X 0 0+(361736209/625000000 : ℝ)*X 0 1+(1230049881/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5438330573/10000000000 : ℝ)*X 1 0+(-986304489/5000000000 : ℝ)*X 1 1+(615024979/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5438331037/10000000000 : ℝ)*X 2 0+(984039881/2000000000 : ℝ)*X 2 1+(-394521783/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((32732427/80000000 : ℝ)*X 0 0+(1541058203/5000000000 : ℝ)*X 0 1+(1064221947/2000000000 : ℝ)*X 0 2+(32732427/80000000 : ℝ)*X 1 0+(1541058203/5000000000 : ℝ)*X 1 1+(1064221947/2000000000 : ℝ)*X 1 2+(32732427/80000000 : ℝ)*X 2 0+(1541058203/5000000000 : ℝ)*X 2 1+(1064221947/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1498491877/10000000000 : ℝ)*X 0 0+(988348791/2000000000 : ℝ)*X 0 1+(1441372391/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2600785639/5000000000 : ℝ)*X 1 0+(-225463901/2000000000 : ℝ)*X 1 1+(5765489213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1040314123/2000000000 : ℝ)*X 2 0+(5765490019/10000000000 : ℝ)*X 2 1+(-1127319257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4097538579/10000000000 : ℝ)*X 0 0+(1316377351/2500000000 : ℝ)*X 0 1+(3139639533/10000000000 : ℝ)*X 0 2+(4097538579/10000000000 : ℝ)*X 1 0+(1316377351/2500000000 : ℝ)*X 1 1+(3139639533/10000000000 : ℝ)*X 1 2+(4097538579/10000000000 : ℝ)*X 2 0+(1316377351/2500000000 : ℝ)*X 2 1+(3139639533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33345765404692303642383/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60766081/50000000000000 : ℝ)*(base1) + (262098969/20000000000000 : ℝ)*(base19) + (1408838519/100000000000000 : ℝ)*(base23) + (151175867/100000000000000 : ℝ)*(upper3) + (98421143/50000000000000 : ℝ)*(upper5) + (159927633712489/20000000000000 : ℝ)*(major0) + (159927633712489/20000000000000 : ℝ)*(major1) + (159927633712489/20000000000000 : ℝ)*(major2) + (288159171371651/25000000000000 : ℝ)*(sp0) + (576320526530099/50000000000000 : ℝ)*(sp1) + (46105638188661/4000000000000 : ℝ)*(sp2) + (223315723489117/50000000000000 : ℝ)*(sp3) + (2899800301/50000000000000 : ℝ)*(sp4) + (1091377171/50000000000000 : ℝ)*(sp7) + (223316875632369/50000000000000 : ℝ)*(f.failure) + (288160590888761/25000000000000 : ℝ)*(f.sum) + (2543385457539/5000000000000000000000000000 : ℝ)*base65 + (65616097692461/10000000000000000000000000000 : ℝ)*base68 + (24158937887539/10000000000000000000000000000 : ℝ)*base69 + (1265351332461/10000000000000000000000000000 : ℝ)*base72 + (22396426752461/5000000000000000000000000000 : ℝ)*base74 + (60387010767539/10000000000000000000000000000 : ℝ)*base75 + (4220118957539/10000000000000000000000000000 : ℝ)*base77 + (72425087082461/10000000000000000000000000000 : ℝ)*base80 + (7011531382539/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1727873/625000000000000000000 : ℝ)*base90 + (1727873/625000000000000000000 : ℝ)*base92 + (1727873/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57888451040480305623069/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5732667/1000000000000 : ℝ)*(base19) + (450057371/100000000000000 : ℝ)*(base23) + (26239821/100000000000000 : ℝ)*(base32) + (69866803/50000000000000 : ℝ)*(upper3) + (23868783/50000000000000 : ℝ)*(upper5) + (842180974371827/100000000000000 : ℝ)*(major0) + (842180974371827/100000000000000 : ℝ)*(major1) + (842180974371827/100000000000000 : ℝ)*(major2) + (178656533/25000000000000 : ℝ)*(sp1) + (1407209309/100000000000000 : ℝ)*(sp2) + (242793211356469/20000000000000 : ℝ)*(sp4) + (1213964768889513/100000000000000 : ℝ)*(sp5) + (242792839903133/20000000000000 : ℝ)*(sp6) + (470395788536881/100000000000000 : ℝ)*(sp7) + (235197907388351/50000000000000 : ℝ)*(f.failure) + (242793211356469/20000000000000 : ℝ)*(f.sum) + (3650146208977/25000000000000000000000000000 : ℝ)*base65 + (358667989608977/50000000000000000000000000000 : ℝ)*base67 + (84945048091023/50000000000000000000000000000 : ℝ)*base70 + (46210507891023/50000000000000000000000000000 : ℝ)*base72 + (201336540483977/25000000000000000000000000000 : ℝ)*base73 + (925676258977/50000000000000000000000000000 : ℝ)*base75 + (60693815791023/50000000000000000000000000000 : ℝ)*base78 + (64196274358977/50000000000000000000000000000 : ℝ)*base79 + (27893488766023/25000000000000000000000000000 : ℝ)*base82 + (4312367/625000000000000000000 : ℝ)*base90 + (4312367/625000000000000000000 : ℝ)*base92 + (4312367/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1648_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (961/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23399/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1648_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1648_s1_0 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1602879551/10000000000 : ℝ)*x 0 + (171805601/312500000 : ℝ)*x 1 + (321303853/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1602879551/10000000000 : ℝ)^4911 ≤ (1979102057693/20000000000000 : ℝ)^3887 := by
    have hnat : (1602879551 : ℕ)^4911*20000000000000^3887 ≤ 1979102057693^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602879551 10000000000 1979102057693 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171805601/312500000 : ℝ)^4911 ≤ (46961466977477/100000000000000 : ℝ)^3887 := by
    have hnat : (171805601 : ℕ)^4911*100000000000000^3887 ≤ 46961466977477^3887*312500000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171805601 312500000 46961466977477 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321303853/625000000 : ℝ)^4911 ≤ (43143022719321/100000000000000 : ℝ)^3887 := by
    have hnat : (321303853 : ℕ)^4911*100000000000000^3887 ≤ 43143022719321^3887*625000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321303853 625000000 43143022719321 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1602879551/10000000000 : ℝ), (171805601/312500000 : ℝ), (321303853/625000000 : ℝ)] ![(1979102057693/20000000000000 : ℝ), (46961466977477/100000000000000 : ℝ), (43143022719321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1602879551/10000000000 : ℝ)|^4911 ≤ (1979102057693/20000000000000 : ℝ)^3887
        have hw : |(-1602879551/10000000000 : ℝ)|=(1602879551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171805601/312500000 : ℝ)|^4911 ≤ (46961466977477/100000000000000 : ℝ)^3887
        have hw : |(171805601/312500000 : ℝ)|=(171805601/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321303853/625000000 : ℝ)|^4911 ≤ (43143022719321/100000000000000 : ℝ)^3887
        have hw : |(321303853/625000000 : ℝ)|=(321303853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s1_1 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670149413/1250000000 : ℝ)*x 0 + (-1788483619/10000000000 : ℝ)*x 1 + (1028172299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670149413/1250000000 : ℝ)^4911 ≤ (9098456021767/20000000000000 : ℝ)^3887 := by
    have hnat : (670149413 : ℕ)^4911*20000000000000^3887 ≤ 9098456021767^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670149413 1250000000 9098456021767 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788483619/10000000000 : ℝ)^4911 ≤ (5682349391597/50000000000000 : ℝ)^3887 := by
    have hnat : (1788483619 : ℕ)^4911*50000000000000^3887 ≤ 5682349391597^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788483619 10000000000 5682349391597 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028172299/2000000000 : ℝ)^4911 ≤ (43143021097057/100000000000000 : ℝ)^3887 := by
    have hnat : (1028172299 : ℕ)^4911*100000000000000^3887 ≤ 43143021097057^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028172299 2000000000 43143021097057 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670149413/1250000000 : ℝ), (-1788483619/10000000000 : ℝ), (1028172299/2000000000 : ℝ)] ![(9098456021767/20000000000000 : ℝ), (5682349391597/50000000000000 : ℝ), (43143021097057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670149413/1250000000 : ℝ)|^4911 ≤ (9098456021767/20000000000000 : ℝ)^3887
        have hw : |(670149413/1250000000 : ℝ)|=(670149413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1788483619/10000000000 : ℝ)|^4911 ≤ (5682349391597/50000000000000 : ℝ)^3887
        have hw : |(-1788483619/10000000000 : ℝ)|=(1788483619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028172299/2000000000 : ℝ)|^4911 ≤ (43143021097057/100000000000000 : ℝ)^3887
        have hw : |(1028172299/2000000000 : ℝ)|=(1028172299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s1_2 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361196423/10000000000 : ℝ)*x 0 + (5140860259/10000000000 : ℝ)*x 1 + (-447120939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361196423/10000000000 : ℝ)^4911 ≤ (45492292105529/100000000000000 : ℝ)^3887 := by
    have hnat : (5361196423 : ℕ)^4911*100000000000000^3887 ≤ 45492292105529^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361196423 10000000000 45492292105529 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140860259/10000000000 : ℝ)^4911 ≤ (43143007991711/100000000000000 : ℝ)^3887 := by
    have hnat : (5140860259 : ℕ)^4911*100000000000000^3887 ≤ 43143007991711^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140860259 10000000000 43143007991711 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447120939/2500000000 : ℝ)^4911 ≤ (11364699883083/100000000000000 : ℝ)^3887 := by
    have hnat : (447120939 : ℕ)^4911*100000000000000^3887 ≤ 11364699883083^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447120939 2500000000 11364699883083 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361196423/10000000000 : ℝ), (5140860259/10000000000 : ℝ), (-447120939/2500000000 : ℝ)] ![(45492292105529/100000000000000 : ℝ), (43143007991711/100000000000000 : ℝ), (11364699883083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361196423/10000000000 : ℝ)|^4911 ≤ (45492292105529/100000000000000 : ℝ)^3887
        have hw : |(5361196423/10000000000 : ℝ)|=(5361196423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140860259/10000000000 : ℝ)|^4911 ≤ (43143007991711/100000000000000 : ℝ)^3887
        have hw : |(5140860259/10000000000 : ℝ)|=(5140860259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447120939/2500000000 : ℝ)|^4911 ≤ (11364699883083/100000000000000 : ℝ)^3887
        have hw : |(-447120939/2500000000 : ℝ)|=(447120939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s1_3 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4174705497/10000000000 : ℝ)*x 0 + (3732585941/10000000000 : ℝ)*x 1 + (4653696709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174705497/10000000000 : ℝ)^4911 ≤ (33165203386451/100000000000000 : ℝ)^3887 := by
    have hnat : (4174705497 : ℕ)^4911*100000000000000^3887 ≤ 33165203386451^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174705497 10000000000 33165203386451 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3732585941/10000000000 : ℝ)^4911 ≤ (14395578630471/50000000000000 : ℝ)^3887 := by
    have hnat : (3732585941 : ℕ)^4911*50000000000000^3887 ≤ 14395578630471^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732585941 10000000000 14395578630471 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4653696709/10000000000 : ℝ)^4911 ≤ (38043639345111/100000000000000 : ℝ)^3887 := by
    have hnat : (4653696709 : ℕ)^4911*100000000000000^3887 ≤ 38043639345111^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4653696709 10000000000 38043639345111 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174705497/10000000000 : ℝ), (3732585941/10000000000 : ℝ), (4653696709/10000000000 : ℝ)] ![(33165203386451/100000000000000 : ℝ), (14395578630471/50000000000000 : ℝ), (38043639345111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174705497/10000000000 : ℝ)|^4911 ≤ (33165203386451/100000000000000 : ℝ)^3887
        have hw : |(4174705497/10000000000 : ℝ)|=(4174705497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3732585941/10000000000 : ℝ)|^4911 ≤ (14395578630471/50000000000000 : ℝ)^3887
        have hw : |(3732585941/10000000000 : ℝ)|=(3732585941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4653696709/10000000000 : ℝ)|^4911 ≤ (38043639345111/100000000000000 : ℝ)^3887
        have hw : |(4653696709/10000000000 : ℝ)|=(4653696709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s1_4 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-801519647/5000000000 : ℝ)*x 0 + (5144494139/10000000000 : ℝ)*x 1 + (2747047149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (801519647/5000000000 : ℝ)^4911 ≤ (4948378147381/50000000000000 : ℝ)^3887 := by
    have hnat : (801519647 : ℕ)^4911*50000000000000^3887 ≤ 4948378147381^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801519647 5000000000 4948378147381 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144494139/10000000000 : ℝ)^4911 ≤ (21590770859767/50000000000000 : ℝ)^3887 := by
    have hnat : (5144494139 : ℕ)^4911*50000000000000^3887 ≤ 21590770859767^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144494139 10000000000 21590770859767 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747047149/5000000000 : ℝ)^4911 ≤ (11730425491433/25000000000000 : ℝ)^3887 := by
    have hnat : (2747047149 : ℕ)^4911*25000000000000^3887 ≤ 11730425491433^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747047149 5000000000 11730425491433 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-801519647/5000000000 : ℝ), (5144494139/10000000000 : ℝ), (2747047149/5000000000 : ℝ)] ![(4948378147381/50000000000000 : ℝ), (21590770859767/50000000000000 : ℝ), (11730425491433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-801519647/5000000000 : ℝ)|^4911 ≤ (4948378147381/50000000000000 : ℝ)^3887
        have hw : |(-801519647/5000000000 : ℝ)|=(801519647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144494139/10000000000 : ℝ)|^4911 ≤ (21590770859767/50000000000000 : ℝ)^3887
        have hw : |(5144494139/10000000000 : ℝ)|=(5144494139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747047149/5000000000 : ℝ)|^4911 ≤ (11730425491433/25000000000000 : ℝ)^3887
        have hw : |(2747047149/5000000000 : ℝ)|=(2747047149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s1_5 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265784129/10000000000 : ℝ)*x 0 + (-717625119/5000000000 : ℝ)*x 1 + (2747047157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265784129/10000000000 : ℝ)^4911 ≤ (1111794858319/2500000000000 : ℝ)^3887 := by
    have hnat : (5265784129 : ℕ)^4911*2500000000000^3887 ≤ 1111794858319^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265784129 10000000000 1111794858319 2500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (717625119/5000000000 : ℝ)^4911 ≤ (1721300702889/20000000000000 : ℝ)^3887 := by
    have hnat : (717625119 : ℕ)^4911*20000000000000^3887 ≤ 1721300702889^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717625119 5000000000 1721300702889 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747047157/5000000000 : ℝ)^4911 ≤ (46921702138377/100000000000000 : ℝ)^3887 := by
    have hnat : (2747047157 : ℕ)^4911*100000000000000^3887 ≤ 46921702138377^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747047157 5000000000 46921702138377 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265784129/10000000000 : ℝ), (-717625119/5000000000 : ℝ), (2747047157/5000000000 : ℝ)] ![(1111794858319/2500000000000 : ℝ), (1721300702889/20000000000000 : ℝ), (46921702138377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265784129/10000000000 : ℝ)|^4911 ≤ (1111794858319/2500000000000 : ℝ)^3887
        have hw : |(5265784129/10000000000 : ℝ)|=(5265784129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-717625119/5000000000 : ℝ)|^4911 ≤ (1721300702889/20000000000000 : ℝ)^3887
        have hw : |(-717625119/5000000000 : ℝ)|=(717625119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747047157/5000000000 : ℝ)|^4911 ≤ (46921702138377/100000000000000 : ℝ)^3887
        have hw : |(2747047157/5000000000 : ℝ)|=(2747047157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s1_6 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265783941/10000000000 : ℝ)*x 0 + (5494094583/10000000000 : ℝ)*x 1 + (-1435250119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265783941/10000000000 : ℝ)^4911 ≤ (22235896163371/50000000000000 : ℝ)^3887 := by
    have hnat : (5265783941 : ℕ)^4911*50000000000000^3887 ≤ 22235896163371^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265783941 10000000000 22235896163371 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494094583/10000000000 : ℝ)^4911 ≤ (11730426260241/25000000000000 : ℝ)^3887 := by
    have hnat : (5494094583 : ℕ)^4911*25000000000000^3887 ≤ 11730426260241^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494094583 10000000000 11730426260241 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1435250119/10000000000 : ℝ)^4911 ≤ (8606502612871/100000000000000 : ℝ)^3887 := by
    have hnat : (1435250119 : ℕ)^4911*100000000000000^3887 ≤ 8606502612871^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435250119 10000000000 8606502612871 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265783941/10000000000 : ℝ), (5494094583/10000000000 : ℝ), (-1435250119/10000000000 : ℝ)] ![(22235896163371/50000000000000 : ℝ), (11730426260241/25000000000000 : ℝ), (8606502612871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265783941/10000000000 : ℝ)|^4911 ≤ (22235896163371/50000000000000 : ℝ)^3887
        have hw : |(5265783941/10000000000 : ℝ)|=(5265783941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494094583/10000000000 : ℝ)|^4911 ≤ (11730426260241/25000000000000 : ℝ)^3887
        have hw : |(5494094583/10000000000 : ℝ)|=(5494094583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1435250119/10000000000 : ℝ)|^4911 ≤ (8606502612871/100000000000000 : ℝ)^3887
        have hw : |(-1435250119/10000000000 : ℝ)|=(1435250119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s1_7 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521889239/1250000000 : ℝ)*x 0 + (4644320949/10000000000 : ℝ)*x 1 + (233881009/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521889239/1250000000 : ℝ)^4911 ≤ (6633860555777/20000000000000 : ℝ)^3887 := by
    have hnat : (521889239 : ℕ)^4911*20000000000000^3887 ≤ 6633860555777^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521889239 1250000000 6633860555777 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4644320949/10000000000 : ℝ)^4911 ≤ (37946827046677/100000000000000 : ℝ)^3887 := by
    have hnat : (4644320949 : ℕ)^4911*100000000000000^3887 ≤ 37946827046677^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4644320949 10000000000 37946827046677 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233881009/625000000 : ℝ)^4911 ≤ (7220967538049/25000000000000 : ℝ)^3887 := by
    have hnat : (233881009 : ℕ)^4911*25000000000000^3887 ≤ 7220967538049^3887*625000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233881009 625000000 7220967538049 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521889239/1250000000 : ℝ), (4644320949/10000000000 : ℝ), (233881009/625000000 : ℝ)] ![(6633860555777/20000000000000 : ℝ), (37946827046677/100000000000000 : ℝ), (7220967538049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521889239/1250000000 : ℝ)|^4911 ≤ (6633860555777/20000000000000 : ℝ)^3887
        have hw : |(521889239/1250000000 : ℝ)|=(521889239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4644320949/10000000000 : ℝ)|^4911 ≤ (37946827046677/100000000000000 : ℝ)^3887
        have hw : |(4644320949/10000000000 : ℝ)|=(4644320949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233881009/625000000 : ℝ)|^4911 ≤ (7220967538049/25000000000000 : ℝ)^3887
        have hw : |(233881009/625000000 : ℝ)|=(233881009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1648_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23399/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (961/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (973/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (541/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23399/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (961/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23399/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (961/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23399/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (961/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23399/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (961/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23399/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (961/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23399/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (961/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (961/20000 : ℝ) ^ (4907/1024 : ℝ) ≤ (12039959954193/25000000000000000000 : ℝ) := by
    have hpowers : (961/20000 : ℝ)^4907 ≤ (12039959954193/25000000000000000000 : ℝ)^1024 := by
      have hnat : (961 : ℕ)^4907*25000000000000000000^1024 ≤ 12039959954193^1024*20000^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        961 20000 12039959954193 25000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (961/20000 : ℝ)) (X := (12039959954193/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23399/100000 : ℝ) ^ (4907/1024 : ℝ) ≤ (94885178161090137/100000000000000000000 : ℝ) := by
    have hpowers : (23399/100000 : ℝ)^4907 ≤ (94885178161090137/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23399 : ℕ)^4907*100000000000000000000^1024 ≤ 94885178161090137^1024*100000^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23399 100000 94885178161090137 100000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23399/100000 : ℝ)) (X := (94885178161090137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500012039959954193/12500000000000000000 : ℝ) ≤ (10000002010012521/10000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (12500012039959954193/12500000000000000000 : ℝ)^1024 ≤ (10000002010012521/10000000000000000 : ℝ)^4907 := by
      have hnat : (12500012039959954193 : ℕ)^1024*10000000000000000^4907 ≤ 10000002010012521^4907*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500012039959954193 12500000000000000000 10000002010012521 10000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002010012521/10000000000000000 : ℝ)) (X := (12500012039959954193/12500000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100094933338000906909/100000000000000000000 : ℝ) ≤ (2000396067841243/2000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (100094933338000906909/100000000000000000000 : ℝ)^1024 ≤ (2000396067841243/2000000000000000 : ℝ)^4907 := by
      have hnat : (100094933338000906909 : ℕ)^1024*2000000000000000^4907 ≤ 2000396067841243^4907*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100094933338000906909 100000000000000000000 2000396067841243 2000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000396067841243/2000000000000000 : ℝ)) (X := (100094933338000906909/100000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50094885178161090137/50000000000000000000 : ℝ) ≤ (10003958668399909/10000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (50094885178161090137/50000000000000000000 : ℝ)^1024 ≤ (10003958668399909/10000000000000000 : ℝ)^4907 := by
      have hnat : (50094885178161090137 : ℕ)^1024*10000000000000000^4907 ≤ 10003958668399909^4907*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50094885178161090137 50000000000000000000 10003958668399909 10000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003958668399909/10000000000000000 : ℝ)) (X := (50094885178161090137/50000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12039959954193/25000000000000000000 : ℝ) ≤ ((92960512815310708067/92970000000000000000 : ℝ)+2*(989164596847/929700000000000 : ℝ)*(961/20000 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (92960512815310708067/92970000000000000000 : ℝ)+2*(989164596847/929700000000000 : ℝ)*(961/20000 : ℝ)=(10000002010012521/10000000000000000 : ℝ) by norm_num, show 1+2*(12039959954193/25000000000000000000 : ℝ)=(12500012039959954193/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(94885178161090137/100000000000000000000 : ℝ)+(12039959954193/25000000000000000000 : ℝ) ≤ ((92960512815310708067/92970000000000000000 : ℝ)+(989164596847/929700000000000 : ℝ)*((23399/100000 : ℝ)+(961/20000 : ℝ)))^(4907/1024 : ℝ) := by
    rw [show (92960512815310708067/92970000000000000000 : ℝ)+(989164596847/929700000000000 : ℝ)*((23399/100000 : ℝ)+(961/20000 : ℝ))=(2000396067841243/2000000000000000 : ℝ) by norm_num, show 1+(94885178161090137/100000000000000000000 : ℝ)+(12039959954193/25000000000000000000 : ℝ)=(100094933338000906909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(94885178161090137/100000000000000000000 : ℝ) ≤ ((92960512815310708067/92970000000000000000 : ℝ)+2*(989164596847/929700000000000 : ℝ)*(23399/100000 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (92960512815310708067/92970000000000000000 : ℝ)+2*(989164596847/929700000000000 : ℝ)*(23399/100000 : ℝ)=(10003958668399909/10000000000000000 : ℝ) by norm_num, show 1+2*(94885178161090137/100000000000000000000 : ℝ)=(50094885178161090137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92960512815310708067/92970000000000000000 : ℝ)*(X 1 0+X 2 0)+(989164596847/929700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (961/20000 : ℝ)) (hi := (23399/100000 : ℝ)) (c := (92960512815310708067/92970000000000000000 : ℝ)) (alpha := (989164596847/929700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92960512815310708067/92970000000000000000 : ℝ)*(X 0 1+X 2 1)+(989164596847/929700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (961/20000 : ℝ)) (hi := (23399/100000 : ℝ)) (c := (92960512815310708067/92970000000000000000 : ℝ)) (alpha := (989164596847/929700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92960512815310708067/92970000000000000000 : ℝ)*(X 0 2+X 1 2)+(989164596847/929700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (961/20000 : ℝ)) (hi := (23399/100000 : ℝ)) (c := (92960512815310708067/92970000000000000000 : ℝ)) (alpha := (989164596847/929700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1602879551/10000000000 : ℝ)*X 0 0+(171805601/312500000 : ℝ)*X 0 1+(321303853/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((670149413/1250000000 : ℝ)*X 1 0+(-1788483619/10000000000 : ℝ)*X 1 1+(1028172299/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361196423/10000000000 : ℝ)*X 2 0+(5140860259/10000000000 : ℝ)*X 2 1+(-447120939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4174705497/10000000000 : ℝ)*X 0 0+(3732585941/10000000000 : ℝ)*X 0 1+(4653696709/10000000000 : ℝ)*X 0 2+(4174705497/10000000000 : ℝ)*X 1 0+(3732585941/10000000000 : ℝ)*X 1 1+(4653696709/10000000000 : ℝ)*X 1 2+(4174705497/10000000000 : ℝ)*X 2 0+(3732585941/10000000000 : ℝ)*X 2 1+(4653696709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-801519647/5000000000 : ℝ)*X 0 0+(5144494139/10000000000 : ℝ)*X 0 1+(2747047149/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5265784129/10000000000 : ℝ)*X 1 0+(-717625119/5000000000 : ℝ)*X 1 1+(2747047157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265783941/10000000000 : ℝ)*X 2 0+(5494094583/10000000000 : ℝ)*X 2 1+(-1435250119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((521889239/1250000000 : ℝ)*X 0 0+(4644320949/10000000000 : ℝ)*X 0 1+(233881009/625000000 : ℝ)*X 0 2+(521889239/1250000000 : ℝ)*X 1 0+(4644320949/10000000000 : ℝ)*X 1 1+(233881009/625000000 : ℝ)*X 1 2+(521889239/1250000000 : ℝ)*X 2 0+(4644320949/10000000000 : ℝ)*X 2 1+(233881009/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4879303687678127004972403607/516500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (628399237/100000000000000 : ℝ)*(base1) + (817149857/100000000000000 : ℝ)*(base19) + (148474733/10000000000000 : ℝ)*(base23) + (7786523/25000000000000 : ℝ)*(upper3) + (44394827/100000000000000 : ℝ)*(lower4) + (105529479/100000000000000 : ℝ)*(upper5) + (1943705409682621/100000000000000 : ℝ)*(major0) + (1943705409682621/100000000000000 : ℝ)*(major1) + (1943705409682621/100000000000000 : ℝ)*(major2) + (2801764558443089/100000000000000 : ℝ)*(sp0) + (560352622578799/20000000000000 : ℝ)*(sp1) + (1400881222648261/50000000000000 : ℝ)*(sp2) + (271411453951987/25000000000000 : ℝ)*(sp3) + (26043767/20000000000000 : ℝ)*(sp7) + (1085646574426019/100000000000000 : ℝ)*(f.failure) + (700440982510963/25000000000000 : ℝ)*(f.sum) + (83805160460021/23242500000000000000000000000 : ℝ)*base65 + (12008224186684632131/3099000000000000000000000000000000 : ℝ)*base68 + (29091167012071632131/3099000000000000000000000000000000 : ℝ)*base70 + (4494887803159632131/3099000000000000000000000000000000 : ℝ)*base72 + (167828059402657/46485000000000000000000000000 : ℝ)*base73 + (16947648284518632131/3099000000000000000000000000000000 : ℝ)*base76 + (32624328972433632131/3099000000000000000000000000000000 : ℝ)*base78 + (1045795400134632131/3099000000000000000000000000000000 : ℝ)*base80 + (72615011167087/46485000000000000000000000000 : ℝ)*base81 + (7070077/1250000000000000000000 : ℝ)*base89 + (7070077/1250000000000000000000 : ℝ)*base91 + (7070077/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (792132029837407880871110749/258250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69939913/10000000000000 : ℝ)*(base19) + (708962349/100000000000000 : ℝ)*(base23) + (44671299/100000000000000 : ℝ)*(upper2) + (42045819/50000000000000 : ℝ)*(upper3) + (17214999/20000000000000 : ℝ)*(upper5) + (992195233034847/50000000000000 : ℝ)*(major0) + (992195233034847/50000000000000 : ℝ)*(major1) + (992195233034847/50000000000000 : ℝ)*(major2) + (6670605231/100000000000000 : ℝ)*(sp1) + (163050377/2000000000000 : ℝ)*(sp2) + (2860409828261373/100000000000000 : ℝ)*(sp4) + (2860402458257013/100000000000000 : ℝ)*(sp5) + (1430200483390087/50000000000000 : ℝ)*(sp6) + (277092750408611/25000000000000 : ℝ)*(sp7) + (277092750408611/25000000000000 : ℝ)*(f.failure) + (2860409828261373/100000000000000 : ℝ)*(f.sum) + (87281513281/60527343750000000000000000 : ℝ)*base65 + (3495900538227732139/516500000000000000000000000000000 : ℝ)*base68 + (15194067363232139/516500000000000000000000000000000 : ℝ)*base70 + (3513826510556732139/516500000000000000000000000000000 : ℝ)*base72 + (52266573493529/15495000000000000000000000000 : ℝ)*base74 + (4774459182867732139/516500000000000000000000000000000 : ℝ)*base76 + (2714840978876232139/516500000000000000000000000000000 : ℝ)*base78 + (231613692020232139/516500000000000000000000000000000 : ℝ)*base80 + (13955453749939/3873750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (39213/312500000000000000000 : ℝ)*base89 + (39213/312500000000000000000 : ℝ)*base91 + (39213/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1648_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23399/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (961/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (973/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (541/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1648_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1648_s2_0 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-322474629/2000000000 : ℝ)*x 0 + (5451804187/10000000000 : ℝ)*x 1 + (647571957/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322474629/2000000000 : ℝ)^4911 ≤ (9969617684243/100000000000000 : ℝ)^3887 := by
    have hnat : (322474629 : ℕ)^4911*100000000000000^3887 ≤ 9969617684243^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322474629 2000000000 9969617684243 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451804187/10000000000 : ℝ)^4911 ≤ (46465843029603/100000000000000 : ℝ)^3887 := by
    have hnat : (5451804187 : ℕ)^4911*100000000000000^3887 ≤ 46465843029603^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451804187 10000000000 46465843029603 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647571957/1250000000 : ℝ)^4911 ≤ (21782269634507/50000000000000 : ℝ)^3887 := by
    have hnat : (647571957 : ℕ)^4911*50000000000000^3887 ≤ 21782269634507^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647571957 1250000000 21782269634507 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-322474629/2000000000 : ℝ), (5451804187/10000000000 : ℝ), (647571957/1250000000 : ℝ)] ![(9969617684243/100000000000000 : ℝ), (46465843029603/100000000000000 : ℝ), (21782269634507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-322474629/2000000000 : ℝ)|^4911 ≤ (9969617684243/100000000000000 : ℝ)^3887
        have hw : |(-322474629/2000000000 : ℝ)|=(322474629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451804187/10000000000 : ℝ)|^4911 ≤ (46465843029603/100000000000000 : ℝ)^3887
        have hw : |(5451804187/10000000000 : ℝ)|=(5451804187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647571957/1250000000 : ℝ)|^4911 ≤ (21782269634507/50000000000000 : ℝ)^3887
        have hw : |(647571957/1250000000 : ℝ)|=(647571957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s2_1 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337258813/2500000000 : ℝ)*x 0 + (-1752114553/10000000000 : ℝ)*x 1 + (2590288231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337258813/2500000000 : ℝ)^4911 ≤ (45361952310673/100000000000000 : ℝ)^3887 := by
    have hnat : (1337258813 : ℕ)^4911*100000000000000^3887 ≤ 45361952310673^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337258813 2500000000 45361952310673 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1752114553/10000000000 : ℝ)^4911 ≤ (11073499849207/100000000000000 : ℝ)^3887 := by
    have hnat : (1752114553 : ℕ)^4911*100000000000000^3887 ≤ 11073499849207^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752114553 10000000000 11073499849207 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590288231/5000000000 : ℝ)^4911 ≤ (43564547832401/100000000000000 : ℝ)^3887 := by
    have hnat : (2590288231 : ℕ)^4911*100000000000000^3887 ≤ 43564547832401^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590288231 5000000000 43564547832401 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337258813/2500000000 : ℝ), (-1752114553/10000000000 : ℝ), (2590288231/5000000000 : ℝ)] ![(45361952310673/100000000000000 : ℝ), (11073499849207/100000000000000 : ℝ), (43564547832401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337258813/2500000000 : ℝ)|^4911 ≤ (45361952310673/100000000000000 : ℝ)^3887
        have hw : |(1337258813/2500000000 : ℝ)|=(1337258813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1752114553/10000000000 : ℝ)|^4911 ≤ (11073499849207/100000000000000 : ℝ)^3887
        have hw : |(-1752114553/10000000000 : ℝ)|=(1752114553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590288231/5000000000 : ℝ)|^4911 ≤ (43564547832401/100000000000000 : ℝ)^3887
        have hw : |(2590288231/5000000000 : ℝ)|=(2590288231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s2_2 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337259213/2500000000 : ℝ)*x 0 + (5180575289/10000000000 : ℝ)*x 1 + (-876056983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337259213/2500000000 : ℝ)^4911 ≤ (9072393890773/20000000000000 : ℝ)^3887 := by
    have hnat : (1337259213 : ℕ)^4911*20000000000000^3887 ≤ 9072393890773^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337259213 2500000000 9072393890773 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180575289/10000000000 : ℝ)^4911 ≤ (8712907073961/20000000000000 : ℝ)^3887 := by
    have hnat : (5180575289 : ℕ)^4911*20000000000000^3887 ≤ 8712907073961^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180575289 10000000000 8712907073961 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876056983/5000000000 : ℝ)^4911 ≤ (11073495161981/100000000000000 : ℝ)^3887 := by
    have hnat : (876056983 : ℕ)^4911*100000000000000^3887 ≤ 11073495161981^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876056983 5000000000 11073495161981 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337259213/2500000000 : ℝ), (5180575289/10000000000 : ℝ), (-876056983/5000000000 : ℝ)] ![(9072393890773/20000000000000 : ℝ), (8712907073961/20000000000000 : ℝ), (11073495161981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337259213/2500000000 : ℝ)|^4911 ≤ (9072393890773/20000000000000 : ℝ)^3887
        have hw : |(1337259213/2500000000 : ℝ)|=(1337259213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180575289/10000000000 : ℝ)|^4911 ≤ (8712907073961/20000000000000 : ℝ)^3887
        have hw : |(5180575289/10000000000 : ℝ)|=(5180575289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-876056983/5000000000 : ℝ)|^4911 ≤ (11073495161981/100000000000000 : ℝ)^3887
        have hw : |(-876056983/5000000000 : ℝ)|=(876056983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s2_3 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4181777747/10000000000 : ℝ)*x 0 + (3842445337/10000000000 : ℝ)*x 1 + (567801611/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181777747/10000000000 : ℝ)^4911 ≤ (4154525593533/12500000000000 : ℝ)^3887 := by
    have hnat : (4181777747 : ℕ)^4911*12500000000000^3887 ≤ 4154525593533^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181777747 10000000000 4154525593533 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3842445337/10000000000 : ℝ)^4911 ≤ (29865914533541/100000000000000 : ℝ)^3887 := by
    have hnat : (3842445337 : ℕ)^4911*100000000000000^3887 ≤ 29865914533541^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3842445337 10000000000 29865914533541 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567801611/1250000000 : ℝ)^4911 ≤ (36897880705083/100000000000000 : ℝ)^3887 := by
    have hnat : (567801611 : ℕ)^4911*100000000000000^3887 ≤ 36897880705083^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567801611 1250000000 36897880705083 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181777747/10000000000 : ℝ), (3842445337/10000000000 : ℝ), (567801611/1250000000 : ℝ)] ![(4154525593533/12500000000000 : ℝ), (29865914533541/100000000000000 : ℝ), (36897880705083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181777747/10000000000 : ℝ)|^4911 ≤ (4154525593533/12500000000000 : ℝ)^3887
        have hw : |(4181777747/10000000000 : ℝ)|=(4181777747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3842445337/10000000000 : ℝ)|^4911 ≤ (29865914533541/100000000000000 : ℝ)^3887
        have hw : |(3842445337/10000000000 : ℝ)|=(3842445337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567801611/1250000000 : ℝ)|^4911 ≤ (36897880705083/100000000000000 : ℝ)^3887
        have hw : |(567801611/1250000000 : ℝ)|=(567801611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s2_4 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-403110443/2500000000 : ℝ)*x 0 + (323917469/625000000 : ℝ)*x 1 + (2724839213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403110443/2500000000 : ℝ)^4911 ≤ (9970153808911/100000000000000 : ℝ)^3887 := by
    have hnat : (403110443 : ℕ)^4911*100000000000000^3887 ≤ 9970153808911^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403110443 2500000000 9970153808911 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323917469/625000000 : ℝ)^4911 ≤ (10896723225117/25000000000000 : ℝ)^3887 := by
    have hnat : (323917469 : ℕ)^4911*25000000000000^3887 ≤ 10896723225117^3887*625000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323917469 625000000 10896723225117 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724839213/5000000000 : ℝ)^4911 ≤ (5805369159667/12500000000000 : ℝ)^3887 := by
    have hnat : (2724839213 : ℕ)^4911*12500000000000^3887 ≤ 5805369159667^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724839213 5000000000 5805369159667 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403110443/2500000000 : ℝ), (323917469/625000000 : ℝ), (2724839213/5000000000 : ℝ)] ![(9970153808911/100000000000000 : ℝ), (10896723225117/25000000000000 : ℝ), (5805369159667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403110443/2500000000 : ℝ)|^4911 ≤ (9970153808911/100000000000000 : ℝ)^3887
        have hw : |(-403110443/2500000000 : ℝ)|=(403110443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323917469/625000000 : ℝ)|^4911 ≤ (10896723225117/25000000000000 : ℝ)^3887
        have hw : |(323917469/625000000 : ℝ)|=(323917469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724839213/5000000000 : ℝ)|^4911 ≤ (5805369159667/12500000000000 : ℝ)^3887
        have hw : |(2724839213/5000000000 : ℝ)|=(2724839213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s2_5 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638294667/5000000000 : ℝ)*x 0 + (-148301231/1000000000 : ℝ)*x 1 + (544967767/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638294667/5000000000 : ℝ)^4911 ≤ (1783484814223/4000000000000 : ℝ)^3887 := by
    have hnat : (2638294667 : ℕ)^4911*4000000000000^3887 ≤ 1783484814223^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638294667 5000000000 1783484814223 4000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148301231/1000000000 : ℝ)^4911 ≤ (8969934485517/100000000000000 : ℝ)^3887 := by
    have hnat : (148301231 : ℕ)^4911*100000000000000^3887 ≤ 8969934485517^3887*1000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148301231 1000000000 8969934485517 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544967767/1000000000 : ℝ)^4911 ≤ (5805368142163/12500000000000 : ℝ)^3887 := by
    have hnat : (544967767 : ℕ)^4911*12500000000000^3887 ≤ 5805368142163^3887*1000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544967767 1000000000 5805368142163 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638294667/5000000000 : ℝ), (-148301231/1000000000 : ℝ), (544967767/1000000000 : ℝ)] ![(1783484814223/4000000000000 : ℝ), (8969934485517/100000000000000 : ℝ), (5805368142163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638294667/5000000000 : ℝ)|^4911 ≤ (1783484814223/4000000000000 : ℝ)^3887
        have hw : |(2638294667/5000000000 : ℝ)|=(2638294667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-148301231/1000000000 : ℝ)|^4911 ≤ (8969934485517/100000000000000 : ℝ)^3887
        have hw : |(-148301231/1000000000 : ℝ)|=(148301231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544967767/1000000000 : ℝ)|^4911 ≤ (5805368142163/12500000000000 : ℝ)^3887
        have hw : |(544967767/1000000000 : ℝ)|=(544967767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s2_6 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276590039/10000000000 : ℝ)*x 0 + (2724838621/5000000000 : ℝ)*x 1 + (-148301193/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276590039/10000000000 : ℝ)^4911 ≤ (44587127882207/100000000000000 : ℝ)^3887 := by
    have hnat : (5276590039 : ℕ)^4911*100000000000000^3887 ≤ 44587127882207^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276590039 10000000000 44587127882207 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724838621/5000000000 : ℝ)^4911 ≤ (23221470264463/50000000000000 : ℝ)^3887 := by
    have hnat : (2724838621 : ℕ)^4911*50000000000000^3887 ≤ 23221470264463^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724838621 5000000000 23221470264463 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148301193/1000000000 : ℝ)^4911 ≤ (1793986316321/20000000000000 : ℝ)^3887 := by
    have hnat : (148301193 : ℕ)^4911*20000000000000^3887 ≤ 1793986316321^3887*1000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148301193 1000000000 1793986316321 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276590039/10000000000 : ℝ), (2724838621/5000000000 : ℝ), (-148301193/1000000000 : ℝ)] ![(44587127882207/100000000000000 : ℝ), (23221470264463/50000000000000 : ℝ), (1793986316321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276590039/10000000000 : ℝ)|^4911 ≤ (44587127882207/100000000000000 : ℝ)^3887
        have hw : |(5276590039/10000000000 : ℝ)|=(5276590039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724838621/5000000000 : ℝ)|^4911 ≤ (23221470264463/50000000000000 : ℝ)^3887
        have hw : |(2724838621/5000000000 : ℝ)|=(2724838621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-148301193/1000000000 : ℝ)|^4911 ≤ (1793986316321/20000000000000 : ℝ)^3887
        have hw : |(-148301193/1000000000 : ℝ)|=(148301193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s2_7 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836391657/2000000000 : ℝ)*x 0 + (283561471/625000000 : ℝ)*x 1 + (480991609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836391657/2000000000 : ℝ)^4911 ≤ (33238017661287/100000000000000 : ℝ)^3887 := by
    have hnat : (836391657 : ℕ)^4911*100000000000000^3887 ≤ 33238017661287^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836391657 2000000000 33238017661287 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283561471/625000000 : ℝ)^4911 ≤ (9210542142369/25000000000000 : ℝ)^3887 := by
    have hnat : (283561471 : ℕ)^4911*25000000000000^3887 ≤ 9210542142369^3887*625000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283561471 625000000 9210542142369 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480991609/1250000000 : ℝ)^4911 ≤ (29919813753259/100000000000000 : ℝ)^3887 := by
    have hnat : (480991609 : ℕ)^4911*100000000000000^3887 ≤ 29919813753259^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480991609 1250000000 29919813753259 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836391657/2000000000 : ℝ), (283561471/625000000 : ℝ), (480991609/1250000000 : ℝ)] ![(33238017661287/100000000000000 : ℝ), (9210542142369/25000000000000 : ℝ), (29919813753259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836391657/2000000000 : ℝ)|^4911 ≤ (33238017661287/100000000000000 : ℝ)^3887
        have hw : |(836391657/2000000000 : ℝ)|=(836391657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283561471/625000000 : ℝ)|^4911 ≤ (9210542142369/25000000000000 : ℝ)^3887
        have hw : |(283561471/625000000 : ℝ)|=(283561471/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(480991609/1250000000 : ℝ)|^4911 ≤ (29919813753259/100000000000000 : ℝ)^3887
        have hw : |(480991609/1250000000 : ℝ)|=(480991609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1648_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (541/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (973/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2647/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (511/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (541/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (973/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (541/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (973/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (541/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (973/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (541/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (973/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (541/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (973/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (541/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (973/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (973/10000 : ℝ) ^ (4907/1024 : ℝ) ≤ (70796964997037/5000000000000000000 : ℝ) := by
    have hpowers : (973/10000 : ℝ)^4907 ≤ (70796964997037/5000000000000000000 : ℝ)^1024 := by
      have hnat : (973 : ℕ)^4907*5000000000000000000^1024 ≤ 70796964997037^1024*10000^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        973 10000 70796964997037 5000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (973/10000 : ℝ)) (X := (70796964997037/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (541/3125 : ℝ) ^ (4907/1024 : ℝ) ≤ (11197883509214073/50000000000000000000 : ℝ) := by
    have hpowers : (541/3125 : ℝ)^4907 ≤ (11197883509214073/50000000000000000000 : ℝ)^1024 := by
      have hnat : (541 : ℕ)^4907*50000000000000000000^1024 ≤ 11197883509214073^1024*3125^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        541 3125 11197883509214073 50000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (541/3125 : ℝ)) (X := (11197883509214073/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500070796964997037/2500000000000000000 : ℝ) ≤ (2000011819079663/2000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (2500070796964997037/2500000000000000000 : ℝ)^1024 ≤ (2000011819079663/2000000000000000 : ℝ)^4907 := by
      have hnat : (2500070796964997037 : ℕ)^1024*2000000000000000^4907 ≤ 2000011819079663^4907*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500070796964997037 2500000000000000000 2000011819079663 2000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000011819079663/2000000000000000 : ℝ)) (X := (2500070796964997037/2500000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011905853159184443/50000000000000000000 : ℝ) ≤ (2000099371878451/2000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (50011905853159184443/50000000000000000000 : ℝ)^1024 ≤ (2000099371878451/2000000000000000 : ℝ)^4907 := by
      have hnat : (50011905853159184443 : ℕ)^1024*2000000000000000^4907 ≤ 2000099371878451^4907*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011905853159184443 50000000000000000000 2000099371878451 2000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000099371878451/2000000000000000 : ℝ)) (X := (50011905853159184443/50000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011197883509214073/25000000000000000000 : ℝ) ≤ (2000186924677239/2000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (25011197883509214073/25000000000000000000 : ℝ)^1024 ≤ (2000186924677239/2000000000000000 : ℝ)^4907 := by
      have hnat : (25011197883509214073 : ℕ)^1024*2000000000000000^4907 ≤ 2000186924677239^4907*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011197883509214073 25000000000000000000 2000186924677239 2000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000186924677239/2000000000000000 : ℝ)) (X := (25011197883509214073/25000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(70796964997037/5000000000000000000 : ℝ) ≤ ((7581192917398795193/7582000000000000000 : ℝ)+2*(21888199697/37910000000000 : ℝ)*(973/10000 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (7581192917398795193/7582000000000000000 : ℝ)+2*(21888199697/37910000000000 : ℝ)*(973/10000 : ℝ)=(2000011819079663/2000000000000000 : ℝ) by norm_num, show 1+2*(70796964997037/5000000000000000000 : ℝ)=(2500070796964997037/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11197883509214073/50000000000000000000 : ℝ)+(70796964997037/5000000000000000000 : ℝ) ≤ ((7581192917398795193/7582000000000000000 : ℝ)+(21888199697/37910000000000 : ℝ)*((541/3125 : ℝ)+(973/10000 : ℝ)))^(4907/1024 : ℝ) := by
    rw [show (7581192917398795193/7582000000000000000 : ℝ)+(21888199697/37910000000000 : ℝ)*((541/3125 : ℝ)+(973/10000 : ℝ))=(2000099371878451/2000000000000000 : ℝ) by norm_num, show 1+(11197883509214073/50000000000000000000 : ℝ)+(70796964997037/5000000000000000000 : ℝ)=(50011905853159184443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11197883509214073/50000000000000000000 : ℝ) ≤ ((7581192917398795193/7582000000000000000 : ℝ)+2*(21888199697/37910000000000 : ℝ)*(541/3125 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (7581192917398795193/7582000000000000000 : ℝ)+2*(21888199697/37910000000000 : ℝ)*(541/3125 : ℝ)=(2000186924677239/2000000000000000 : ℝ) by norm_num, show 1+2*(11197883509214073/50000000000000000000 : ℝ)=(25011197883509214073/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7581192917398795193/7582000000000000000 : ℝ)*(X 1 0+X 2 0)+(21888199697/37910000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (973/10000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (7581192917398795193/7582000000000000000 : ℝ)) (alpha := (21888199697/37910000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7581192917398795193/7582000000000000000 : ℝ)*(X 0 1+X 2 1)+(21888199697/37910000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (973/10000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (7581192917398795193/7582000000000000000 : ℝ)) (alpha := (21888199697/37910000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7581192917398795193/7582000000000000000 : ℝ)*(X 0 2+X 1 2)+(21888199697/37910000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (973/10000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (7581192917398795193/7582000000000000000 : ℝ)) (alpha := (21888199697/37910000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-322474629/2000000000 : ℝ)*X 0 0+(5451804187/10000000000 : ℝ)*X 0 1+(647571957/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337258813/2500000000 : ℝ)*X 1 0+(-1752114553/10000000000 : ℝ)*X 1 1+(2590288231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337259213/2500000000 : ℝ)*X 2 0+(5180575289/10000000000 : ℝ)*X 2 1+(-876056983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4181777747/10000000000 : ℝ)*X 0 0+(3842445337/10000000000 : ℝ)*X 0 1+(567801611/1250000000 : ℝ)*X 0 2+(4181777747/10000000000 : ℝ)*X 1 0+(3842445337/10000000000 : ℝ)*X 1 1+(567801611/1250000000 : ℝ)*X 1 2+(4181777747/10000000000 : ℝ)*X 2 0+(3842445337/10000000000 : ℝ)*X 2 1+(567801611/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-403110443/2500000000 : ℝ)*X 0 0+(323917469/625000000 : ℝ)*X 0 1+(2724839213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638294667/5000000000 : ℝ)*X 1 0+(-148301231/1000000000 : ℝ)*X 1 1+(544967767/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276590039/10000000000 : ℝ)*X 2 0+(2724838621/5000000000 : ℝ)*X 2 1+(-148301193/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((836391657/2000000000 : ℝ)*X 0 0+(283561471/625000000 : ℝ)*X 0 1+(480991609/1250000000 : ℝ)*X 0 2+(836391657/2000000000 : ℝ)*X 1 0+(283561471/625000000 : ℝ)*X 1 1+(480991609/1250000000 : ℝ)*X 1 2+(836391657/2000000000 : ℝ)*X 2 0+(283561471/625000000 : ℝ)*X 2 1+(480991609/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243580047654583205942147517/47387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235329801/50000000000000 : ℝ)*(base19) + (1236567759/100000000000000 : ℝ)*(base23) + (11359997/6250000000000 : ℝ)*(upper4) + (371670267/100000000000000 : ℝ)*(upper5) + (639449421517323/25000000000000 : ℝ)*(major0) + (639449421517323/25000000000000 : ℝ)*(major1) + (639449421517323/25000000000000 : ℝ)*(major2) + (737386177355817/20000000000000 : ℝ)*(sp0) + (3686949888196249/100000000000000 : ℝ)*(sp1) + (368694933417459/10000000000000 : ℝ)*(sp2) + (1428641307259287/100000000000000 : ℝ)*(sp3) + (153780963/781250000000 : ℝ)*(sp4) + (211886497/100000000000000 : ℝ)*(sp5) + (415349721/12500000000000 : ℝ)*(sp7) + (714322315028527/50000000000000 : ℝ)*(f.failure) + (921737642685587/25000000000000 : ℝ)*(f.sum) + (628396474033/236937500000000000000000000 : ℝ)*base66 + (379274204472071661/189550000000000000000000000000000 : ℝ)*base68 + (713262339035971661/189550000000000000000000000000000 : ℝ)*base70 + (959557778288421661/189550000000000000000000000000000 : ℝ)*base72 + (788541218597/236937500000000000000000000 : ℝ)*base74 + (711544105315828339/189550000000000000000000000000000 : ℝ)*base75 + (1002774786678121661/189550000000000000000000000000000 : ℝ)*base78 + (340783529230521661/189550000000000000000000000000000 : ℝ)*base80 + (510552736761/947750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (7635759/625000000000000000000 : ℝ)*base90 + (7635759/625000000000000000000 : ℝ)*base92 + (7635759/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (583813958090222456889789579/94775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2364097/800000000000 : ℝ)*(base19) + (1507578919/100000000000000 : ℝ)*(base23) + (14434589/100000000000000 : ℝ)*(lower2) + (7596863/2500000000000 : ℝ)*(lower4) + (13823251/25000000000000 : ℝ)*(upper5) + (649576941841333/25000000000000 : ℝ)*(major0) + (649576941841333/25000000000000 : ℝ)*(major1) + (649576941841333/25000000000000 : ℝ)*(major2) + (2762521993/50000000000000 : ℝ)*(sp0) + (2376123703/20000000000000 : ℝ)*(sp2) + (3745338478517361/100000000000000 : ℝ)*(sp4) + (1872671854024611/50000000000000 : ℝ)*(sp5) + (468166326920489/12500000000000 : ℝ)*(sp6) + (1451271325835993/100000000000000 : ℝ)*(sp7) + (1451271325835993/100000000000000 : ℝ)*(f.failure) + (3745344003561347/100000000000000 : ℝ)*(f.sum) + (14302327072701/758200000000000000000000000 : ℝ)*base66 + (1219524413637612269/189550000000000000000000000000000 : ℝ)*base67 + (363029294993412269/189550000000000000000000000000000 : ℝ)*base69 + (71097718888162269/189550000000000000000000000000000 : ℝ)*base71 + (336446648913/189550000000000000000000000 : ℝ)*base73 + (1218788000135512269/189550000000000000000000000000000 : ℝ)*base75 + (1027265786028162269/189550000000000000000000000000000 : ℝ)*base77 + (40044190863462269/189550000000000000000000000000000 : ℝ)*base79 + (2972233262389/1895500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (269081/1250000000000000000000 : ℝ)*base90 + (269081/1250000000000000000000 : ℝ)*base92 + (269081/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1648_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (541/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (973/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1648_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1648_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1648_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1648_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1648_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1648_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1533_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:33.985155+00:00
-- url     : https://prove2.me/submissions/72b4a357-72ad-40cf-a7df-9f8d1a00db62

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
theorem support_rectangle_w1533_s3_0 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-367408749/2000000000 : ℝ)*x 0 + (543308897/1000000000 : ℝ)*x 1 + (208652509/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367408749/2000000000 : ℝ)^4563 ≤ (11251086963809/100000000000000 : ℝ)^3539 := by
    have hnat : (367408749 : ℕ)^4563*100000000000000^3539 ≤ 11251086963809^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367408749 2000000000 11251086963809 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543308897/1000000000 : ℝ)^4563 ≤ (9107796775243/20000000000000 : ℝ)^3539 := by
    have hnat : (543308897 : ℕ)^4563*20000000000000^3539 ≤ 9107796775243^3539*1000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543308897 1000000000 9107796775243 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208652509/400000000 : ℝ)^4563 ≤ (4320992914749/10000000000000 : ℝ)^3539 := by
    have hnat : (208652509 : ℕ)^4563*10000000000000^3539 ≤ 4320992914749^3539*400000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208652509 400000000 4320992914749 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-367408749/2000000000 : ℝ), (543308897/1000000000 : ℝ), (208652509/400000000 : ℝ)] ![(11251086963809/100000000000000 : ℝ), (9107796775243/20000000000000 : ℝ), (4320992914749/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-367408749/2000000000 : ℝ)|^4563 ≤ (11251086963809/100000000000000 : ℝ)^3539
        have hw : |(-367408749/2000000000 : ℝ)|=(367408749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543308897/1000000000 : ℝ)|^4563 ≤ (9107796775243/20000000000000 : ℝ)^3539
        have hw : |(543308897/1000000000 : ℝ)|=(543308897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208652509/400000000 : ℝ)|^4563 ≤ (4320992914749/10000000000000 : ℝ)^3539
        have hw : |(208652509/400000000 : ℝ)|=(208652509/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s3_1 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351075641/10000000000 : ℝ)*x 0 + (-1948080169/10000000000 : ℝ)*x 1 + (5216312531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351075641/10000000000 : ℝ)^4563 ≤ (2790912862941/6250000000000 : ℝ)^3539 := by
    have hnat : (5351075641 : ℕ)^4563*6250000000000^3539 ≤ 2790912862941^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351075641 10000000000 2790912862941 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1948080169/10000000000 : ℝ)^4563 ≤ (97083736833/800000000000 : ℝ)^3539 := by
    have hnat : (1948080169 : ℕ)^4563*800000000000^3539 ≤ 97083736833^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948080169 10000000000 97083736833 800000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216312531/10000000000 : ℝ)^4563 ≤ (43209927075481/100000000000000 : ℝ)^3539 := by
    have hnat : (5216312531 : ℕ)^4563*100000000000000^3539 ≤ 43209927075481^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216312531 10000000000 43209927075481 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351075641/10000000000 : ℝ), (-1948080169/10000000000 : ℝ), (5216312531/10000000000 : ℝ)] ![(2790912862941/6250000000000 : ℝ), (97083736833/800000000000 : ℝ), (43209927075481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351075641/10000000000 : ℝ)|^4563 ≤ (2790912862941/6250000000000 : ℝ)^3539
        have hw : |(5351075641/10000000000 : ℝ)|=(5351075641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1948080169/10000000000 : ℝ)|^4563 ≤ (97083736833/800000000000 : ℝ)^3539
        have hw : |(-1948080169/10000000000 : ℝ)|=(1948080169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216312531/10000000000 : ℝ)|^4563 ≤ (43209927075481/100000000000000 : ℝ)^3539
        have hw : |(5216312531/10000000000 : ℝ)|=(5216312531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s3_2 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66888449/125000000 : ℝ)*x 0 + (5216312059/10000000000 : ℝ)*x 1 + (-974040211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66888449/125000000 : ℝ)^4563 ≤ (44654608808977/100000000000000 : ℝ)^3539 := by
    have hnat : (66888449 : ℕ)^4563*100000000000000^3539 ≤ 44654608808977^3539*125000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66888449 125000000 44654608808977 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216312059/10000000000 : ℝ)^4563 ≤ (8641984406861/20000000000000 : ℝ)^3539 := by
    have hnat : (5216312059 : ℕ)^4563*20000000000000^3539 ≤ 8641984406861^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216312059 10000000000 8641984406861 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974040211/5000000000 : ℝ)^4563 ≤ (6067734568101/50000000000000 : ℝ)^3539 := by
    have hnat : (974040211 : ℕ)^4563*50000000000000^3539 ≤ 6067734568101^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974040211 5000000000 6067734568101 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66888449/125000000 : ℝ), (5216312059/10000000000 : ℝ), (-974040211/5000000000 : ℝ)] ![(44654608808977/100000000000000 : ℝ), (8641984406861/20000000000000 : ℝ), (6067734568101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66888449/125000000 : ℝ)|^4563 ≤ (44654608808977/100000000000000 : ℝ)^3539
        have hw : |(66888449/125000000 : ℝ)|=(66888449/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216312059/10000000000 : ℝ)|^4563 ≤ (8641984406861/20000000000000 : ℝ)^3539
        have hw : |(5216312059/10000000000 : ℝ)|=(5216312059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974040211/5000000000 : ℝ)|^4563 ≤ (6067734568101/50000000000000 : ℝ)^3539
        have hw : |(-974040211/5000000000 : ℝ)|=(974040211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s3_3 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425984763/1000000000 : ℝ)*x 0 + (4016519537/10000000000 : ℝ)*x 1 + (4515361779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425984763/1000000000 : ℝ)^4563 ≤ (6655646451251/20000000000000 : ℝ)^3539 := by
    have hnat : (425984763 : ℕ)^4563*20000000000000^3539 ≤ 6655646451251^3539*1000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425984763 1000000000 6655646451251 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016519537/10000000000 : ℝ)^4563 ≤ (30847851947883/100000000000000 : ℝ)^3539 := by
    have hnat : (4016519537 : ℕ)^4563*100000000000000^3539 ≤ 30847851947883^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016519537 10000000000 30847851947883 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515361779/10000000000 : ℝ)^4563 ≤ (35873915773351/100000000000000 : ℝ)^3539 := by
    have hnat : (4515361779 : ℕ)^4563*100000000000000^3539 ≤ 35873915773351^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515361779 10000000000 35873915773351 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425984763/1000000000 : ℝ), (4016519537/10000000000 : ℝ), (4515361779/10000000000 : ℝ)] ![(6655646451251/20000000000000 : ℝ), (30847851947883/100000000000000 : ℝ), (35873915773351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425984763/1000000000 : ℝ)|^4563 ≤ (6655646451251/20000000000000 : ℝ)^3539
        have hw : |(425984763/1000000000 : ℝ)|=(425984763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016519537/10000000000 : ℝ)|^4563 ≤ (30847851947883/100000000000000 : ℝ)^3539
        have hw : |(4016519537/10000000000 : ℝ)|=(4016519537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515361779/10000000000 : ℝ)|^4563 ≤ (35873915773351/100000000000000 : ℝ)^3539
        have hw : |(4515361779/10000000000 : ℝ)|=(4515361779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s3_4 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-459268627/2500000000 : ℝ)*x 0 + (2608729267/5000000000 : ℝ)*x 1 + (5431934031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (459268627/2500000000 : ℝ)^4563 ≤ (140641623627/1250000000000 : ℝ)^3539 := by
    have hnat : (459268627 : ℕ)^4563*1250000000000^3539 ≤ 140641623627^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459268627 2500000000 140641623627 1250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608729267/5000000000 : ℝ)^4563 ≤ (172888669201/400000000000 : ℝ)^3539 := by
    have hnat : (2608729267 : ℕ)^4563*400000000000^3539 ≤ 172888669201^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608729267 5000000000 172888669201 400000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431934031/10000000000 : ℝ)^4563 ≤ (45526502797713/100000000000000 : ℝ)^3539 := by
    have hnat : (5431934031 : ℕ)^4563*100000000000000^3539 ≤ 45526502797713^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431934031 10000000000 45526502797713 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-459268627/2500000000 : ℝ), (2608729267/5000000000 : ℝ), (5431934031/10000000000 : ℝ)] ![(140641623627/1250000000000 : ℝ), (172888669201/400000000000 : ℝ), (45526502797713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-459268627/2500000000 : ℝ)|^4563 ≤ (140641623627/1250000000000 : ℝ)^3539
        have hw : |(-459268627/2500000000 : ℝ)|=(459268627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608729267/5000000000 : ℝ)|^4563 ≤ (172888669201/400000000000 : ℝ)^3539
        have hw : |(2608729267/5000000000 : ℝ)|=(2608729267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431934031/10000000000 : ℝ)|^4563 ≤ (45526502797713/100000000000000 : ℝ)^3539
        have hw : |(5431934031/10000000000 : ℝ)|=(5431934031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s3_5 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293994287/10000000000 : ℝ)*x 0 + (-1732459041/10000000000 : ℝ)*x 1 + (169747943/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293994287/10000000000 : ℝ)^4563 ≤ (44041384995059/100000000000000 : ℝ)^3539 := by
    have hnat : (5293994287 : ℕ)^4563*100000000000000^3539 ≤ 44041384995059^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293994287 10000000000 44041384995059 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1732459041/10000000000 : ℝ)^4563 ≤ (10432110624817/100000000000000 : ℝ)^3539 := by
    have hnat : (1732459041 : ℕ)^4563*100000000000000^3539 ≤ 10432110624817^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732459041 10000000000 10432110624817 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169747943/312500000 : ℝ)^4563 ≤ (11381626091159/25000000000000 : ℝ)^3539 := by
    have hnat : (169747943 : ℕ)^4563*25000000000000^3539 ≤ 11381626091159^3539*312500000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169747943 312500000 11381626091159 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293994287/10000000000 : ℝ), (-1732459041/10000000000 : ℝ), (169747943/312500000 : ℝ)] ![(44041384995059/100000000000000 : ℝ), (10432110624817/100000000000000 : ℝ), (11381626091159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293994287/10000000000 : ℝ)|^4563 ≤ (44041384995059/100000000000000 : ℝ)^3539
        have hw : |(5293994287/10000000000 : ℝ)|=(5293994287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1732459041/10000000000 : ℝ)|^4563 ≤ (10432110624817/100000000000000 : ℝ)^3539
        have hw : |(-1732459041/10000000000 : ℝ)|=(1732459041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169747943/312500000 : ℝ)|^4563 ≤ (11381626091159/25000000000000 : ℝ)^3539
        have hw : |(169747943/312500000 : ℝ)|=(169747943/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s3_6 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293995159/10000000000 : ℝ)*x 0 + (5431933739/10000000000 : ℝ)*x 1 + (-433114611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293995159/10000000000 : ℝ)^4563 ≤ (22020697174169/50000000000000 : ℝ)^3539 := by
    have hnat : (5293995159 : ℕ)^4563*50000000000000^3539 ≤ 22020697174169^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293995159 10000000000 22020697174169 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431933739/10000000000 : ℝ)^4563 ≤ (22763249821127/50000000000000 : ℝ)^3539 := by
    have hnat : (5431933739 : ℕ)^4563*50000000000000^3539 ≤ 22763249821127^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431933739 10000000000 22763249821127 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433114611/2500000000 : ℝ)^4563 ≤ (5216052994889/50000000000000 : ℝ)^3539 := by
    have hnat : (433114611 : ℕ)^4563*50000000000000^3539 ≤ 5216052994889^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433114611 2500000000 5216052994889 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293995159/10000000000 : ℝ), (5431933739/10000000000 : ℝ), (-433114611/2500000000 : ℝ)] ![(22020697174169/50000000000000 : ℝ), (22763249821127/50000000000000 : ℝ), (5216052994889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293995159/10000000000 : ℝ)|^4563 ≤ (22020697174169/50000000000000 : ℝ)^3539
        have hw : |(5293995159/10000000000 : ℝ)|=(5293995159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431933739/10000000000 : ℝ)|^4563 ≤ (22763249821127/50000000000000 : ℝ)^3539
        have hw : |(5431933739/10000000000 : ℝ)|=(5431933739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433114611/2500000000 : ℝ)|^4563 ≤ (5216052994889/50000000000000 : ℝ)^3539
        have hw : |(-433114611/2500000000 : ℝ)|=(433114611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s3_7 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170396677/400000000 : ℝ)*x 0 + (4512724449/10000000000 : ℝ)*x 1 + (1004794191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170396677/400000000 : ℝ)^4563 ≤ (16639465114939/50000000000000 : ℝ)^3539 := by
    have hnat : (170396677 : ℕ)^4563*50000000000000^3539 ≤ 16639465114939^3539*400000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170396677 400000000 16639465114939 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512724449/10000000000 : ℝ)^4563 ≤ (17923451041797/50000000000000 : ℝ)^3539 := by
    have hnat : (4512724449 : ℕ)^4563*50000000000000^3539 ≤ 17923451041797^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512724449 10000000000 17923451041797 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004794191/2500000000 : ℝ)^4563 ≤ (15437083831181/50000000000000 : ℝ)^3539 := by
    have hnat : (1004794191 : ℕ)^4563*50000000000000^3539 ≤ 15437083831181^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004794191 2500000000 15437083831181 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170396677/400000000 : ℝ), (4512724449/10000000000 : ℝ), (1004794191/2500000000 : ℝ)] ![(16639465114939/50000000000000 : ℝ), (17923451041797/50000000000000 : ℝ), (15437083831181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170396677/400000000 : ℝ)|^4563 ≤ (16639465114939/50000000000000 : ℝ)^3539
        have hw : |(170396677/400000000 : ℝ)|=(170396677/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512724449/10000000000 : ℝ)|^4563 ≤ (17923451041797/50000000000000 : ℝ)^3539
        have hw : |(4512724449/10000000000 : ℝ)|=(4512724449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004794191/2500000000 : ℝ)|^4563 ≤ (15437083831181/50000000000000 : ℝ)^3539
        have hw : |(1004794191/2500000000 : ℝ)|=(1004794191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1533_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7961/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2189/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7769/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7961/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (331/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7961/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (331/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7961/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (331/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7961/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (331/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7961/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (331/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7961/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (331/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (331/3125 : ℝ) ^ (4561/1024 : ℝ) ≤ (2270507110840297/50000000000000000000 : ℝ) := by
    have hpowers : (331/3125 : ℝ)^4561 ≤ (2270507110840297/50000000000000000000 : ℝ)^1024 := by
      have hnat : (331 : ℕ)^4561*50000000000000000000^1024 ≤ 2270507110840297^1024*3125^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        331 3125 2270507110840297 50000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (331/3125 : ℝ)) (X := (2270507110840297/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7961/50000 : ℝ) ^ (4561/1024 : ℝ) ≤ (3487597546868751/12500000000000000000 : ℝ) := by
    have hpowers : (7961/50000 : ℝ)^4561 ≤ (3487597546868751/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7961 : ℕ)^4561*12500000000000000000^1024 ≤ 3487597546868751^1024*50000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7961 50000 3487597546868751 12500000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7961/50000 : ℝ)) (X := (3487597546868751/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002270507110840297/25000000000000000000 : ℝ) ≤ (10000203895409869/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (25002270507110840297/25000000000000000000 : ℝ)^1024 ≤ (10000203895409869/10000000000000000 : ℝ)^4561 := by
      have hnat : (25002270507110840297 : ℕ)^1024*10000000000000000^4561 ≤ 10000203895409869^4561*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002270507110840297 25000000000000000000 10000203895409869 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000203895409869/10000000000000000 : ℝ)) (X := (25002270507110840297/25000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016220897298315301/50000000000000000000 : ℝ) ≤ (10000728266161791/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50016220897298315301/50000000000000000000 : ℝ)^1024 ≤ (10000728266161791/10000000000000000 : ℝ)^4561 := by
      have hnat : (50016220897298315301 : ℕ)^1024*10000000000000000^4561 ≤ 10000728266161791^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016220897298315301 50000000000000000000 10000728266161791 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000728266161791/10000000000000000 : ℝ)) (X := (50016220897298315301/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253487597546868751/6250000000000000000 : ℝ) ≤ (10001252636913713/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (6253487597546868751/6250000000000000000 : ℝ)^1024 ≤ (10001252636913713/10000000000000000 : ℝ)^4561 := by
      have hnat : (6253487597546868751 : ℕ)^1024*10000000000000000^4561 ≤ 10001252636913713^4561*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253487597546868751 6250000000000000000 10001252636913713 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001252636913713/10000000000000000 : ℝ)) (X := (6253487597546868751/6250000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2270507110840297/50000000000000000000 : ℝ) ≤ ((26644989246262943061/26650000000000000000 : ℝ)+2*(262185375961/266500000000000 : ℝ)*(331/3125 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (26644989246262943061/26650000000000000000 : ℝ)+2*(262185375961/266500000000000 : ℝ)*(331/3125 : ℝ)=(10000203895409869/10000000000000000 : ℝ) by norm_num, show 1+2*(2270507110840297/50000000000000000000 : ℝ)=(25002270507110840297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3487597546868751/12500000000000000000 : ℝ)+(2270507110840297/50000000000000000000 : ℝ) ≤ ((26644989246262943061/26650000000000000000 : ℝ)+(262185375961/266500000000000 : ℝ)*((7961/50000 : ℝ)+(331/3125 : ℝ)))^(4561/1024 : ℝ) := by
    rw [show (26644989246262943061/26650000000000000000 : ℝ)+(262185375961/266500000000000 : ℝ)*((7961/50000 : ℝ)+(331/3125 : ℝ))=(10000728266161791/10000000000000000 : ℝ) by norm_num, show 1+(3487597546868751/12500000000000000000 : ℝ)+(2270507110840297/50000000000000000000 : ℝ)=(50016220897298315301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3487597546868751/12500000000000000000 : ℝ) ≤ ((26644989246262943061/26650000000000000000 : ℝ)+2*(262185375961/266500000000000 : ℝ)*(7961/50000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (26644989246262943061/26650000000000000000 : ℝ)+2*(262185375961/266500000000000 : ℝ)*(7961/50000 : ℝ)=(10001252636913713/10000000000000000 : ℝ) by norm_num, show 1+2*(3487597546868751/12500000000000000000 : ℝ)=(6253487597546868751/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26644989246262943061/26650000000000000000 : ℝ)*(X 1 0+X 2 0)+(262185375961/266500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (331/3125 : ℝ)) (hi := (7961/50000 : ℝ)) (c := (26644989246262943061/26650000000000000000 : ℝ)) (alpha := (262185375961/266500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26644989246262943061/26650000000000000000 : ℝ)*(X 0 1+X 2 1)+(262185375961/266500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (331/3125 : ℝ)) (hi := (7961/50000 : ℝ)) (c := (26644989246262943061/26650000000000000000 : ℝ)) (alpha := (262185375961/266500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26644989246262943061/26650000000000000000 : ℝ)*(X 0 2+X 1 2)+(262185375961/266500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (331/3125 : ℝ)) (hi := (7961/50000 : ℝ)) (c := (26644989246262943061/26650000000000000000 : ℝ)) (alpha := (262185375961/266500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-367408749/2000000000 : ℝ)*X 0 0+(543308897/1000000000 : ℝ)*X 0 1+(208652509/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351075641/10000000000 : ℝ)*X 1 0+(-1948080169/10000000000 : ℝ)*X 1 1+(5216312531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66888449/125000000 : ℝ)*X 2 0+(5216312059/10000000000 : ℝ)*X 2 1+(-974040211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((425984763/1000000000 : ℝ)*X 0 0+(4016519537/10000000000 : ℝ)*X 0 1+(4515361779/10000000000 : ℝ)*X 0 2+(425984763/1000000000 : ℝ)*X 1 0+(4016519537/10000000000 : ℝ)*X 1 1+(4515361779/10000000000 : ℝ)*X 1 2+(425984763/1000000000 : ℝ)*X 2 0+(4016519537/10000000000 : ℝ)*X 2 1+(4515361779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-459268627/2500000000 : ℝ)*X 0 0+(2608729267/5000000000 : ℝ)*X 0 1+(5431934031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293994287/10000000000 : ℝ)*X 1 0+(-1732459041/10000000000 : ℝ)*X 1 1+(169747943/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293995159/10000000000 : ℝ)*X 2 0+(5431933739/10000000000 : ℝ)*X 2 1+(-433114611/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170396677/400000000 : ℝ)*X 0 0+(4512724449/10000000000 : ℝ)*X 0 1+(1004794191/2500000000 : ℝ)*X 0 2+(170396677/400000000 : ℝ)*X 1 0+(4512724449/10000000000 : ℝ)*X 1 1+(1004794191/2500000000 : ℝ)*X 1 2+(170396677/400000000 : ℝ)*X 2 0+(4512724449/10000000000 : ℝ)*X 2 1+(1004794191/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5356596258346595147921986323/666250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72289783/20000000000000 : ℝ)*(base19) + (214751957/25000000000000 : ℝ)*(base23) + (37508289/50000000000000 : ℝ)*(lower2) + (212559741/100000000000000 : ℝ)*(lower4) + (7868607/50000000000000 : ℝ)*(lower5) + (1654427788742419/50000000000000 : ℝ)*(major0) + (1654427788742419/50000000000000 : ℝ)*(major1) + (1654427788742419/50000000000000 : ℝ)*(major2) + (4613057071204491/100000000000000 : ℝ)*(sp0) + (461306057822681/10000000000000 : ℝ)*(sp1) + (576632510083487/12500000000000 : ℝ)*(sp2) + (25058073533467/1250000000000 : ℝ)*(sp3) + (1934235617/50000000000000 : ℝ)*(sp4) + (508077409/12500000000000 : ℝ)*(sp7) + (2004649947296633/100000000000000 : ℝ)*(f.failure) + (1153265234918931/25000000000000 : ℝ)*(f.sum) + (52723194687093/13325000000000000000000000000 : ℝ)*base65 + (10847831542853304559/1332500000000000000000000000000000 : ℝ)*base67 + (2207594117144195441/1332500000000000000000000000000000 : ℝ)*base70 + (10715604988133304559/1332500000000000000000000000000000 : ℝ)*base71 + (2734853698249/416406250000000000000000000 : ℝ)*base73 + (6702841338576695441/1332500000000000000000000000000000 : ℝ)*base76 + (270764949058304559/1332500000000000000000000000000000 : ℝ)*base77 + (9987592677718304559/1332500000000000000000000000000000 : ℝ)*base79 + (17196573046059/6662500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (39576293/10000000000000000000000 : ℝ)*base89 + (39576293/10000000000000000000000 : ℝ)*base91 + (39576293/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129398371960773185076309/13325000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111615937/12500000000000 : ℝ)*(base19) + (374437707/20000000000000 : ℝ)*(base23) + (701407/25000000000000 : ℝ)*(upper2) + (6413841/2500000000000 : ℝ)*(upper3) + (49379109/50000000000000 : ℝ)*(upper5) + (3344344347237473/100000000000000 : ℝ)*(major0) + (3344344347237473/100000000000000 : ℝ)*(major1) + (3344344347237473/100000000000000 : ℝ)*(major2) + (2538570689/25000000000000 : ℝ)*(sp1) + (914293921/3125000000000 : ℝ)*(sp2) + (2331268884512347/50000000000000 : ℝ)*(sp4) + (2331263360907221/50000000000000 : ℝ)*(sp5) + (4662506639430687/100000000000000 : ℝ)*(sp6) + (253268825219001/12500000000000 : ℝ)*(sp7) + (253268825219001/12500000000000 : ℝ)*(f.failure) + (2331268884512347/50000000000000 : ℝ)*(f.sum) + (12368861763047/13325000000000000000000000000 : ℝ)*base66 + (7363754746320175147/2665000000000000000000000000000000 : ℝ)*base68 + (9243402121409824853/2665000000000000000000000000000000 : ℝ)*base69 + (13807971690550175147/2665000000000000000000000000000000 : ℝ)*base72 + (55340292595897/13325000000000000000000000000 : ℝ)*base74 + (2175225923599824853/2665000000000000000000000000000000 : ℝ)*base75 + (5038626686845175147/2665000000000000000000000000000000 : ℝ)*base78 + (7170097395254824853/2665000000000000000000000000000000 : ℝ)*base79 + (34039887269053/13325000000000000000000000000 : ℝ)*base81 + (3158021/1250000000000000000000 : ℝ)*base89 + (3158021/1250000000000000000000 : ℝ)*base91 + (3158021/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1533_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7961/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2189/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7769/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1533_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1533_s4_0 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1837389881/10000000000 : ℝ)*x 0 + (5430805719/10000000000 : ℝ)*x 1 + (5218366851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1837389881/10000000000 : ℝ)^4563 ≤ (11253820365747/100000000000000 : ℝ)^3539 := by
    have hnat : (1837389881 : ℕ)^4563*100000000000000^3539 ≤ 11253820365747^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837389881 10000000000 11253820365747 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430805719/10000000000 : ℝ)^4563 ≤ (4551431021067/10000000000000 : ℝ)^3539 := by
    have hnat : (5430805719 : ℕ)^4563*10000000000000^3539 ≤ 4551431021067^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430805719 10000000000 4551431021067 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218366851/10000000000 : ℝ)^4563 ≤ (5403983675237/12500000000000 : ℝ)^3539 := by
    have hnat : (5218366851 : ℕ)^4563*12500000000000^3539 ≤ 5403983675237^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218366851 10000000000 5403983675237 12500000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1837389881/10000000000 : ℝ), (5430805719/10000000000 : ℝ), (5218366851/10000000000 : ℝ)] ![(11253820365747/100000000000000 : ℝ), (4551431021067/10000000000000 : ℝ), (5403983675237/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1837389881/10000000000 : ℝ)|^4563 ≤ (11253820365747/100000000000000 : ℝ)^3539
        have hw : |(-1837389881/10000000000 : ℝ)|=(1837389881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430805719/10000000000 : ℝ)|^4563 ≤ (4551431021067/10000000000000 : ℝ)^3539
        have hw : |(5430805719/10000000000 : ℝ)|=(5430805719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218366851/10000000000 : ℝ)|^4563 ≤ (5403983675237/12500000000000 : ℝ)^3539
        have hw : |(5218366851/10000000000 : ℝ)|=(5218366851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s4_1 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350475377/10000000000 : ℝ)*x 0 + (-121634509/625000000 : ℝ)*x 1 + (5218366821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350475377/10000000000 : ℝ)^4563 ≤ (44648147326959/100000000000000 : ℝ)^3539 := by
    have hnat : (5350475377 : ℕ)^4563*100000000000000^3539 ≤ 44648147326959^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350475377 10000000000 44648147326959 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121634509/625000000 : ℝ)^4563 ≤ (12119983572129/100000000000000 : ℝ)^3539 := by
    have hnat : (121634509 : ℕ)^4563*100000000000000^3539 ≤ 12119983572129^3539*625000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121634509 625000000 12119983572129 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218366821/10000000000 : ℝ)^4563 ≤ (8646373816289/20000000000000 : ℝ)^3539 := by
    have hnat : (5218366821 : ℕ)^4563*20000000000000^3539 ≤ 8646373816289^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218366821 10000000000 8646373816289 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350475377/10000000000 : ℝ), (-121634509/625000000 : ℝ), (5218366821/10000000000 : ℝ)] ![(44648147326959/100000000000000 : ℝ), (12119983572129/100000000000000 : ℝ), (8646373816289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350475377/10000000000 : ℝ)|^4563 ≤ (44648147326959/100000000000000 : ℝ)^3539
        have hw : |(5350475377/10000000000 : ℝ)|=(5350475377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121634509/625000000 : ℝ)|^4563 ≤ (12119983572129/100000000000000 : ℝ)^3539
        have hw : |(-121634509/625000000 : ℝ)|=(121634509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218366821/10000000000 : ℝ)|^4563 ≤ (8646373816289/20000000000000 : ℝ)^3539
        have hw : |(5218366821/10000000000 : ℝ)|=(5218366821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s4_2 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675237689/5000000000 : ℝ)*x 0 + (5218366857/10000000000 : ℝ)*x 1 + (-389230419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675237689/5000000000 : ℝ)^4563 ≤ (22324073668859/50000000000000 : ℝ)^3539 := by
    have hnat : (2675237689 : ℕ)^4563*50000000000000^3539 ≤ 22324073668859^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675237689 5000000000 22324073668859 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218366857/10000000000 : ℝ)^4563 ≤ (21615934732993/50000000000000 : ℝ)^3539 := by
    have hnat : (5218366857 : ℕ)^4563*50000000000000^3539 ≤ 21615934732993^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218366857 10000000000 21615934732993 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389230419/2000000000 : ℝ)^4563 ≤ (12119983178677/100000000000000 : ℝ)^3539 := by
    have hnat : (389230419 : ℕ)^4563*100000000000000^3539 ≤ 12119983178677^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389230419 2000000000 12119983178677 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675237689/5000000000 : ℝ), (5218366857/10000000000 : ℝ), (-389230419/2000000000 : ℝ)] ![(22324073668859/50000000000000 : ℝ), (21615934732993/50000000000000 : ℝ), (12119983178677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675237689/5000000000 : ℝ)|^4563 ≤ (22324073668859/50000000000000 : ℝ)^3539
        have hw : |(2675237689/5000000000 : ℝ)|=(2675237689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218366857/10000000000 : ℝ)|^4563 ≤ (21615934732993/50000000000000 : ℝ)^3539
        have hw : |(5218366857/10000000000 : ℝ)|=(5218366857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389230419/2000000000 : ℝ)|^4563 ≤ (12119983178677/100000000000000 : ℝ)^3539
        have hw : |(-389230419/2000000000 : ℝ)|=(389230419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s4_3 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852012899/2000000000 : ℝ)*x 0 + (201074291/500000000 : ℝ)*x 1 + (4510345999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852012899/2000000000 : ℝ)^4563 ≤ (2080026039943/6250000000000 : ℝ)^3539 := by
    have hnat : (852012899 : ℕ)^4563*6250000000000^3539 ≤ 2080026039943^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852012899 2000000000 2080026039943 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201074291/500000000 : ℝ)^4563 ≤ (30897039371201/100000000000000 : ℝ)^3539 := by
    have hnat : (201074291 : ℕ)^4563*100000000000000^3539 ≤ 30897039371201^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201074291 500000000 30897039371201 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510345999/10000000000 : ℝ)^4563 ≤ (8955635992869/25000000000000 : ℝ)^3539 := by
    have hnat : (4510345999 : ℕ)^4563*25000000000000^3539 ≤ 8955635992869^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510345999 10000000000 8955635992869 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852012899/2000000000 : ℝ), (201074291/500000000 : ℝ), (4510345999/10000000000 : ℝ)] ![(2080026039943/6250000000000 : ℝ), (30897039371201/100000000000000 : ℝ), (8955635992869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852012899/2000000000 : ℝ)|^4563 ≤ (2080026039943/6250000000000 : ℝ)^3539
        have hw : |(852012899/2000000000 : ℝ)|=(852012899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201074291/500000000 : ℝ)|^4563 ≤ (30897039371201/100000000000000 : ℝ)^3539
        have hw : |(201074291/500000000 : ℝ)|=(201074291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510345999/10000000000 : ℝ)|^4563 ≤ (8955635992869/25000000000000 : ℝ)^3539
        have hw : |(4510345999/10000000000 : ℝ)|=(4510345999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s4_4 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-114838641/625000000 : ℝ)*x 0 + (2609733917/5000000000 : ℝ)*x 1 + (5429696573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114838641/625000000 : ℝ)^4563 ≤ (5627022223469/50000000000000 : ℝ)^3539 := by
    have hnat : (114838641 : ℕ)^4563*50000000000000^3539 ≤ 5627022223469^3539*625000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114838641 625000000 5627022223469 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609733917/5000000000 : ℝ)^4563 ≤ (675681720347/1562500000000 : ℝ)^3539 := by
    have hnat : (2609733917 : ℕ)^4563*1562500000000^3539 ≤ 675681720347^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609733917 5000000000 675681720347 1562500000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429696573/10000000000 : ℝ)^4563 ≤ (45502325446599/100000000000000 : ℝ)^3539 := by
    have hnat : (5429696573 : ℕ)^4563*100000000000000^3539 ≤ 45502325446599^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429696573 10000000000 45502325446599 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114838641/625000000 : ℝ), (2609733917/5000000000 : ℝ), (5429696573/10000000000 : ℝ)] ![(5627022223469/50000000000000 : ℝ), (675681720347/1562500000000 : ℝ), (45502325446599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114838641/625000000 : ℝ)|^4563 ≤ (5627022223469/50000000000000 : ℝ)^3539
        have hw : |(-114838641/625000000 : ℝ)|=(114838641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609733917/5000000000 : ℝ)|^4563 ≤ (675681720347/1562500000000 : ℝ)^3539
        have hw : |(2609733917/5000000000 : ℝ)|=(2609733917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429696573/10000000000 : ℝ)|^4563 ≤ (45502325446599/100000000000000 : ℝ)^3539
        have hw : |(5429696573/10000000000 : ℝ)|=(5429696573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s4_5 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323634353/2500000000 : ℝ)*x 0 + (-27106601/156250000 : ℝ)*x 1 + (542969659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323634353/2500000000 : ℝ)^4563 ≤ (22023605384613/50000000000000 : ℝ)^3539 := by
    have hnat : (1323634353 : ℕ)^4563*50000000000000^3539 ≤ 22023605384613^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323634353 2500000000 22023605384613 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27106601/156250000 : ℝ)^4563 ≤ (10450463590381/100000000000000 : ℝ)^3539 := by
    have hnat : (27106601 : ℕ)^4563*100000000000000^3539 ≤ 10450463590381^3539*156250000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27106601 156250000 10450463590381 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542969659/1000000000 : ℝ)^4563 ≤ (9100465126057/20000000000000 : ℝ)^3539 := by
    have hnat : (542969659 : ℕ)^4563*20000000000000^3539 ≤ 9100465126057^3539*1000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542969659 1000000000 9100465126057 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323634353/2500000000 : ℝ), (-27106601/156250000 : ℝ), (542969659/1000000000 : ℝ)] ![(22023605384613/50000000000000 : ℝ), (10450463590381/100000000000000 : ℝ), (9100465126057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323634353/2500000000 : ℝ)|^4563 ≤ (22023605384613/50000000000000 : ℝ)^3539
        have hw : |(1323634353/2500000000 : ℝ)|=(1323634353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27106601/156250000 : ℝ)|^4563 ≤ (10450463590381/100000000000000 : ℝ)^3539
        have hw : |(-27106601/156250000 : ℝ)|=(27106601/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542969659/1000000000 : ℝ)|^4563 ≤ (9100465126057/20000000000000 : ℝ)^3539
        have hw : |(542969659/1000000000 : ℝ)|=(542969659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s4_6 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330908589/625000000 : ℝ)*x 0 + (5429696621/10000000000 : ℝ)*x 1 + (-433705601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330908589/625000000 : ℝ)^4563 ≤ (8809442179589/20000000000000 : ℝ)^3539 := by
    have hnat : (330908589 : ℕ)^4563*20000000000000^3539 ≤ 8809442179589^3539*625000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330908589 625000000 8809442179589 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429696621/10000000000 : ℝ)^4563 ≤ (22751162982621/50000000000000 : ℝ)^3539 := by
    have hnat : (5429696621 : ℕ)^4563*50000000000000^3539 ≤ 22751162982621^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429696621 10000000000 22751162982621 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433705601/2500000000 : ℝ)^4563 ≤ (2612615781091/25000000000000 : ℝ)^3539 := by
    have hnat : (433705601 : ℕ)^4563*25000000000000^3539 ≤ 2612615781091^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433705601 2500000000 2612615781091 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330908589/625000000 : ℝ), (5429696621/10000000000 : ℝ), (-433705601/2500000000 : ℝ)] ![(8809442179589/20000000000000 : ℝ), (22751162982621/50000000000000 : ℝ), (2612615781091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330908589/625000000 : ℝ)|^4563 ≤ (8809442179589/20000000000000 : ℝ)^3539
        have hw : |(330908589/625000000 : ℝ)|=(330908589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429696621/10000000000 : ℝ)|^4563 ≤ (22751162982621/50000000000000 : ℝ)^3539
        have hw : |(5429696621/10000000000 : ℝ)|=(5429696621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433705601/2500000000 : ℝ)|^4563 ≤ (2612615781091/25000000000000 : ℝ)^3539
        have hw : |(-433705601/2500000000 : ℝ)|=(433705601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s4_7 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260129699/10000000000 : ℝ)*x 0 + (450781253/1000000000 : ℝ)*x 1 + (80480761/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260129699/10000000000 : ℝ)^4563 ≤ (1040033544241/3125000000000 : ℝ)^3539 := by
    have hnat : (4260129699 : ℕ)^4563*3125000000000^3539 ≤ 1040033544241^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260129699 10000000000 1040033544241 3125000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450781253/1000000000 : ℝ)^4563 ≤ (35796602370921/100000000000000 : ℝ)^3539 := by
    have hnat : (450781253 : ℕ)^4563*100000000000000^3539 ≤ 35796602370921^3539*1000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450781253 1000000000 35796602370921 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80480761/200000000 : ℝ)^4563 ≤ (30922324193613/100000000000000 : ℝ)^3539 := by
    have hnat : (80480761 : ℕ)^4563*100000000000000^3539 ≤ 30922324193613^3539*200000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80480761 200000000 30922324193613 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260129699/10000000000 : ℝ), (450781253/1000000000 : ℝ), (80480761/200000000 : ℝ)] ![(1040033544241/3125000000000 : ℝ), (35796602370921/100000000000000 : ℝ), (30922324193613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260129699/10000000000 : ℝ)|^4563 ≤ (1040033544241/3125000000000 : ℝ)^3539
        have hw : |(4260129699/10000000000 : ℝ)|=(4260129699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450781253/1000000000 : ℝ)|^4563 ≤ (35796602370921/100000000000000 : ℝ)^3539
        have hw : |(450781253/1000000000 : ℝ)|=(450781253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80480761/200000000 : ℝ)|^4563 ≤ (30922324193613/100000000000000 : ℝ)^3539
        have hw : |(80480761/200000000 : ℝ)|=(80480761/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1533_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7769/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2189/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10989/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7769/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2189/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7769/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2189/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7769/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2189/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7769/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2189/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7769/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2189/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7769/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2189/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2189/20000 : ℝ) ^ (4561/1024 : ℝ) ≤ (656870040985299/12500000000000000000 : ℝ) := by
    have hpowers : (2189/20000 : ℝ)^4561 ≤ (656870040985299/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2189 : ℕ)^4561*12500000000000000000^1024 ≤ 656870040985299^1024*20000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2189 20000 656870040985299 12500000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2189/20000 : ℝ)) (X := (656870040985299/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7769/50000 : ℝ) ^ (4561/1024 : ℝ) ≤ (12513008282210681/50000000000000000000 : ℝ) := by
    have hpowers : (7769/50000 : ℝ)^4561 ≤ (12513008282210681/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7769 : ℕ)^4561*50000000000000000000^1024 ≤ 12513008282210681^1024*50000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7769 50000 12513008282210681 50000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7769/50000 : ℝ)) (X := (12513008282210681/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250656870040985299/6250000000000000000 : ℝ) ≤ (10000235950892433/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (6250656870040985299/6250000000000000000 : ℝ)^1024 ≤ (10000235950892433/10000000000000000 : ℝ)^4561 := by
      have hnat : (6250656870040985299 : ℕ)^1024*10000000000000000^4561 ≤ 10000235950892433^4561*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250656870040985299 6250000000000000000 10000235950892433 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000235950892433/10000000000000000 : ℝ)) (X := (6250656870040985299/6250000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015140488446151877/50000000000000000000 : ℝ) ≤ (10000679764970217/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50015140488446151877/50000000000000000000 : ℝ)^1024 ≤ (10000679764970217/10000000000000000 : ℝ)^4561 := by
      have hnat : (50015140488446151877 : ℕ)^1024*10000000000000000^4561 ≤ 10000679764970217^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015140488446151877 50000000000000000000 10000679764970217 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000679764970217/10000000000000000 : ℝ)) (X := (50015140488446151877/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012513008282210681/25000000000000000000 : ℝ) ≤ (10001123579048001/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (25012513008282210681/25000000000000000000 : ℝ)^1024 ≤ (10001123579048001/10000000000000000 : ℝ)^4561 := by
      have hnat : (25012513008282210681 : ℕ)^1024*10000000000000000^4561 ≤ 10001123579048001^4561*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012513008282210681 25000000000000000000 10001123579048001 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001123579048001/10000000000000000 : ℝ)) (X := (25012513008282210681/25000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(656870040985299/12500000000000000000 : ℝ) ≤ ((15307122877428751003/15310000000000000000 : ℝ)+2*(18492253241/19137500000000 : ℝ)*(2189/20000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (15307122877428751003/15310000000000000000 : ℝ)+2*(18492253241/19137500000000 : ℝ)*(2189/20000 : ℝ)=(10000235950892433/10000000000000000 : ℝ) by norm_num, show 1+2*(656870040985299/12500000000000000000 : ℝ)=(6250656870040985299/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12513008282210681/50000000000000000000 : ℝ)+(656870040985299/12500000000000000000 : ℝ) ≤ ((15307122877428751003/15310000000000000000 : ℝ)+(18492253241/19137500000000 : ℝ)*((7769/50000 : ℝ)+(2189/20000 : ℝ)))^(4561/1024 : ℝ) := by
    rw [show (15307122877428751003/15310000000000000000 : ℝ)+(18492253241/19137500000000 : ℝ)*((7769/50000 : ℝ)+(2189/20000 : ℝ))=(10000679764970217/10000000000000000 : ℝ) by norm_num, show 1+(12513008282210681/50000000000000000000 : ℝ)+(656870040985299/12500000000000000000 : ℝ)=(50015140488446151877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12513008282210681/50000000000000000000 : ℝ) ≤ ((15307122877428751003/15310000000000000000 : ℝ)+2*(18492253241/19137500000000 : ℝ)*(7769/50000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (15307122877428751003/15310000000000000000 : ℝ)+2*(18492253241/19137500000000 : ℝ)*(7769/50000 : ℝ)=(10001123579048001/10000000000000000 : ℝ) by norm_num, show 1+2*(12513008282210681/50000000000000000000 : ℝ)=(25012513008282210681/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15307122877428751003/15310000000000000000 : ℝ)*(X 1 0+X 2 0)+(18492253241/19137500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (2189/20000 : ℝ)) (hi := (7769/50000 : ℝ)) (c := (15307122877428751003/15310000000000000000 : ℝ)) (alpha := (18492253241/19137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15307122877428751003/15310000000000000000 : ℝ)*(X 0 1+X 2 1)+(18492253241/19137500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (2189/20000 : ℝ)) (hi := (7769/50000 : ℝ)) (c := (15307122877428751003/15310000000000000000 : ℝ)) (alpha := (18492253241/19137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15307122877428751003/15310000000000000000 : ℝ)*(X 0 2+X 1 2)+(18492253241/19137500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (2189/20000 : ℝ)) (hi := (7769/50000 : ℝ)) (c := (15307122877428751003/15310000000000000000 : ℝ)) (alpha := (18492253241/19137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1837389881/10000000000 : ℝ)*X 0 0+(5430805719/10000000000 : ℝ)*X 0 1+(5218366851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350475377/10000000000 : ℝ)*X 1 0+(-121634509/625000000 : ℝ)*X 1 1+(5218366821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675237689/5000000000 : ℝ)*X 2 0+(5218366857/10000000000 : ℝ)*X 2 1+(-389230419/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((852012899/2000000000 : ℝ)*X 0 0+(201074291/500000000 : ℝ)*X 0 1+(4510345999/10000000000 : ℝ)*X 0 2+(852012899/2000000000 : ℝ)*X 1 0+(201074291/500000000 : ℝ)*X 1 1+(4510345999/10000000000 : ℝ)*X 1 2+(852012899/2000000000 : ℝ)*X 2 0+(201074291/500000000 : ℝ)*X 2 1+(4510345999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-114838641/625000000 : ℝ)*X 0 0+(2609733917/5000000000 : ℝ)*X 0 1+(5429696573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323634353/2500000000 : ℝ)*X 1 0+(-27106601/156250000 : ℝ)*X 1 1+(542969659/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330908589/625000000 : ℝ)*X 2 0+(5429696621/10000000000 : ℝ)*X 2 1+(-433705601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4260129699/10000000000 : ℝ)*X 0 0+(450781253/1000000000 : ℝ)*X 0 1+(80480761/200000000 : ℝ)*X 0 2+(4260129699/10000000000 : ℝ)*X 1 0+(450781253/1000000000 : ℝ)*X 1 1+(80480761/200000000 : ℝ)*X 1 2+(4260129699/10000000000 : ℝ)*X 2 0+(450781253/1000000000 : ℝ)*X 2 1+(80480761/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12021561452088412949943/1913750000000000000000000000 : ℝ) := by norm_num
    linear_combination (591257661/50000000000000 : ℝ)*(base19) + (1069248583/100000000000000 : ℝ)*(base23) + (61073817/100000000000000 : ℝ)*(lower2) + (29505963/20000000000000 : ℝ)*(upper3) + (22518897/20000000000000 : ℝ)*(upper5) + (3376432974052223/100000000000000 : ℝ)*(major0) + (3376432974052223/100000000000000 : ℝ)*(major1) + (3376432974052223/100000000000000 : ℝ)*(major2) + (2353627665764481/50000000000000 : ℝ)*(sp0) + (4707273255829649/100000000000000 : ℝ)*(sp1) + (1176818342274097/25000000000000 : ℝ)*(sp2) + (63924455396853/3125000000000 : ℝ)*(sp3) + (19106816009/100000000000000 : ℝ)*(sp4) + (1745534181/20000000000000 : ℝ)*(sp7) + (2045591300370201/100000000000000 : ℝ)*(f.failure) + (4707274438344971/100000000000000 : ℝ)*(f.sum) + (14600270569351/7655000000000000000000000000 : ℝ)*base66 + (3952033819793970331/1531000000000000000000000000000000 : ℝ)*base68 + (17166094517917029669/1531000000000000000000000000000000 : ℝ)*base69 + (683152526952029669/1531000000000000000000000000000000 : ℝ)*base71 + (9904349539363/3827500000000000000000000000 : ℝ)*base74 + (17604572902607029669/1531000000000000000000000000000000 : ℝ)*base75 + (1493442601268970331/1531000000000000000000000000000000 : ℝ)*base78 + (7323486172085970331/1531000000000000000000000000000000 : ℝ)*base80 + (17595418186687/3827500000000000000000000000 : ℝ)*base81 + (14633221/10000000000000000000000 : ℝ)*base89 + (14633221/10000000000000000000000 : ℝ)*base91 + (14633221/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4408367659133700764720271759/765500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (862922871/100000000000000 : ℝ)*(base19) + (492423987/50000000000000 : ℝ)*(base23) + (7158131/5000000000000 : ℝ)*(upper3) + (39090691/100000000000000 : ℝ)*(lower4) + (103638623/100000000000000 : ℝ)*(upper5) + (3411900625081249/100000000000000 : ℝ)*(major0) + (3411900625081249/100000000000000 : ℝ)*(major1) + (3411900625081249/100000000000000 : ℝ)*(major2) + (1533774341/12500000000000 : ℝ)*(sp1) + (3160355791/20000000000000 : ℝ)*(sp2) + (4756721898026387/100000000000000 : ℝ)*(sp4) + (4756708764908789/100000000000000 : ℝ)*(sp5) + (2378352555699729/50000000000000 : ℝ)*(sp6) + (2067079160175831/100000000000000 : ℝ)*(sp7) + (2067079160175831/100000000000000 : ℝ)*(f.failure) + (4756721898026387/100000000000000 : ℝ)*(f.sum) + (2121244658037/7655000000000000000000000000 : ℝ)*base65 + (4414926777955557253/1531000000000000000000000000000000 : ℝ)*base68 + (7197336016041442747/1531000000000000000000000000000000 : ℝ)*base69 + (9465527685189442747/1531000000000000000000000000000000 : ℝ)*base71 + (25197733606869/3827500000000000000000000000 : ℝ)*base74 + (6981193344684442747/1531000000000000000000000000000000 : ℝ)*base75 + (13395513348791442747/1531000000000000000000000000000000 : ℝ)*base77 + (6047263813400557253/1531000000000000000000000000000000 : ℝ)*base80 + (22686834351343/7655000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (47278549/10000000000000000000000 : ℝ)*base90 + (47278549/10000000000000000000000 : ℝ)*base92 + (47278549/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1533_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7769/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2189/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1533_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1533_s5_0 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-459357527/2500000000 : ℝ)*x 0 + (2715271221/5000000000 : ℝ)*x 1 + (2609301721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (459357527/2500000000 : ℝ)^4563 ≤ (11254138044073/100000000000000 : ℝ)^3539 := by
    have hnat : (459357527 : ℕ)^4563*100000000000000^3539 ≤ 11254138044073^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459357527 2500000000 11254138044073 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715271221/5000000000 : ℝ)^4563 ≤ (45511465333767/100000000000000 : ℝ)^3539 := by
    have hnat : (2715271221 : ℕ)^4563*100000000000000^3539 ≤ 45511465333767^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715271221 5000000000 45511465333767 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609301721/5000000000 : ℝ)^4563 ≤ (43234396606379/100000000000000 : ℝ)^3539 := by
    have hnat : (2609301721 : ℕ)^4563*100000000000000^3539 ≤ 43234396606379^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609301721 5000000000 43234396606379 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-459357527/2500000000 : ℝ), (2715271221/5000000000 : ℝ), (2609301721/5000000000 : ℝ)] ![(11254138044073/100000000000000 : ℝ), (45511465333767/100000000000000 : ℝ), (43234396606379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-459357527/2500000000 : ℝ)|^4563 ≤ (11254138044073/100000000000000 : ℝ)^3539
        have hw : |(-459357527/2500000000 : ℝ)|=(459357527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715271221/5000000000 : ℝ)|^4563 ≤ (45511465333767/100000000000000 : ℝ)^3539
        have hw : |(2715271221/5000000000 : ℝ)|=(2715271221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609301721/5000000000 : ℝ)|^4563 ≤ (43234396606379/100000000000000 : ℝ)^3539
        have hw : |(2609301721/5000000000 : ℝ)|=(2609301721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s5_1 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350405667/10000000000 : ℝ)*x 0 + (-486482667/2500000000 : ℝ)*x 1 + (5218603521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350405667/10000000000 : ℝ)^4563 ≤ (1395231165713/3125000000000 : ℝ)^3539 := by
    have hnat : (5350405667 : ℕ)^4563*3125000000000^3539 ≤ 1395231165713^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350405667 10000000000 1395231165713 3125000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486482667/2500000000 : ℝ)^4563 ≤ (12118205232653/100000000000000 : ℝ)^3539 := by
    have hnat : (486482667 : ℕ)^4563*100000000000000^3539 ≤ 12118205232653^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486482667 2500000000 12118205232653 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218603521/10000000000 : ℝ)^4563 ≤ (21617198725121/50000000000000 : ℝ)^3539 := by
    have hnat : (5218603521 : ℕ)^4563*50000000000000^3539 ≤ 21617198725121^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218603521 10000000000 21617198725121 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350405667/10000000000 : ℝ), (-486482667/2500000000 : ℝ), (5218603521/10000000000 : ℝ)] ![(1395231165713/3125000000000 : ℝ), (12118205232653/100000000000000 : ℝ), (21617198725121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350405667/10000000000 : ℝ)|^4563 ≤ (1395231165713/3125000000000 : ℝ)^3539
        have hw : |(5350405667/10000000000 : ℝ)|=(5350405667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486482667/2500000000 : ℝ)|^4563 ≤ (12118205232653/100000000000000 : ℝ)^3539
        have hw : |(-486482667/2500000000 : ℝ)|=(486482667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218603521/10000000000 : ℝ)|^4563 ≤ (21617198725121/50000000000000 : ℝ)^3539
        have hw : |(5218603521/10000000000 : ℝ)|=(5218603521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s5_2 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070081179/2000000000 : ℝ)*x 0 + (5218603087/10000000000 : ℝ)*x 1 + (-1945930939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070081179/2000000000 : ℝ)^4563 ≤ (4464739975591/10000000000000 : ℝ)^3539 := by
    have hnat : (1070081179 : ℕ)^4563*10000000000000^3539 ≤ 4464739975591^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070081179 2000000000 4464739975591 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218603087/10000000000 : ℝ)^4563 ≤ (8646878562867/20000000000000 : ℝ)^3539 := by
    have hnat : (5218603087 : ℕ)^4563*20000000000000^3539 ≤ 8646878562867^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218603087 10000000000 8646878562867 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945930939/10000000000 : ℝ)^4563 ≤ (1211820740861/10000000000000 : ℝ)^3539 := by
    have hnat : (1945930939 : ℕ)^4563*10000000000000^3539 ≤ 1211820740861^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945930939 10000000000 1211820740861 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070081179/2000000000 : ℝ), (5218603087/10000000000 : ℝ), (-1945930939/10000000000 : ℝ)] ![(4464739975591/10000000000000 : ℝ), (8646878562867/20000000000000 : ℝ), (1211820740861/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070081179/2000000000 : ℝ)|^4563 ≤ (4464739975591/10000000000000 : ℝ)^3539
        have hw : |(1070081179/2000000000 : ℝ)|=(1070081179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218603087/10000000000 : ℝ)|^4563 ≤ (8646878562867/20000000000000 : ℝ)^3539
        have hw : |(5218603087/10000000000 : ℝ)|=(5218603087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945930939/10000000000 : ℝ)|^4563 ≤ (1211820740861/10000000000000 : ℝ)^3539
        have hw : |(-1945930939/10000000000 : ℝ)|=(1945930939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s5_3 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260088987/10000000000 : ℝ)*x 0 + (4022057757/10000000000 : ℝ)*x 1 + (4509768623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260088987/10000000000 : ℝ)^4563 ≤ (33280663337923/100000000000000 : ℝ)^3539 := by
    have hnat : (4260088987 : ℕ)^4563*100000000000000^3539 ≤ 33280663337923^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260088987 10000000000 33280663337923 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022057757/10000000000 : ℝ)^4563 ≤ (30902705120571/100000000000000 : ℝ)^3539 := by
    have hnat : (4022057757 : ℕ)^4563*100000000000000^3539 ≤ 30902705120571^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022057757 10000000000 30902705120571 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509768623/10000000000 : ℝ)^4563 ≤ (7163326305181/20000000000000 : ℝ)^3539 := by
    have hnat : (4509768623 : ℕ)^4563*20000000000000^3539 ≤ 7163326305181^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509768623 10000000000 7163326305181 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260088987/10000000000 : ℝ), (4022057757/10000000000 : ℝ), (4509768623/10000000000 : ℝ)] ![(33280663337923/100000000000000 : ℝ), (30902705120571/100000000000000 : ℝ), (7163326305181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260088987/10000000000 : ℝ)|^4563 ≤ (33280663337923/100000000000000 : ℝ)^3539
        have hw : |(4260088987/10000000000 : ℝ)|=(4260088987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022057757/10000000000 : ℝ)|^4563 ≤ (30902705120571/100000000000000 : ℝ)^3539
        have hw : |(4022057757/10000000000 : ℝ)|=(4022057757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509768623/10000000000 : ℝ)|^4563 ≤ (7163326305181/20000000000000 : ℝ)^3539
        have hw : |(4509768623/10000000000 : ℝ)|=(4509768623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s5_4 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73498331/400000000 : ℝ)*x 0 + (1304924763/2500000000 : ℝ)*x 1 + (5429438729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73498331/400000000 : ℝ)^4563 ≤ (5627180242033/50000000000000 : ℝ)^3539 := by
    have hnat : (73498331 : ℕ)^4563*50000000000000^3539 ≤ 5627180242033^3539*400000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73498331 400000000 5627180242033 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304924763/2500000000 : ℝ)^4563 ≤ (43246100064073/100000000000000 : ℝ)^3539 := by
    have hnat : (1304924763 : ℕ)^4563*100000000000000^3539 ≤ 43246100064073^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304924763 2500000000 43246100064073 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429438729/10000000000 : ℝ)^4563 ≤ (22749769720503/50000000000000 : ℝ)^3539 := by
    have hnat : (5429438729 : ℕ)^4563*50000000000000^3539 ≤ 22749769720503^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429438729 10000000000 22749769720503 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73498331/400000000 : ℝ), (1304924763/2500000000 : ℝ), (5429438729/10000000000 : ℝ)] ![(5627180242033/50000000000000 : ℝ), (43246100064073/100000000000000 : ℝ), (22749769720503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73498331/400000000 : ℝ)|^4563 ≤ (5627180242033/50000000000000 : ℝ)^3539
        have hw : |(-73498331/400000000 : ℝ)|=(73498331/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304924763/2500000000 : ℝ)|^4563 ≤ (43246100064073/100000000000000 : ℝ)^3539
        have hw : |(1304924763/2500000000 : ℝ)|=(1304924763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429438729/10000000000 : ℝ)|^4563 ≤ (22749769720503/50000000000000 : ℝ)^3539
        have hw : |(5429438729/10000000000 : ℝ)|=(5429438729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s5_5 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647299829/5000000000 : ℝ)*x 0 + (-1735095213/10000000000 : ℝ)*x 1 + (5429438731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647299829/5000000000 : ℝ)^4563 ≤ (8809575691111/20000000000000 : ℝ)^3539 := by
    have hnat : (2647299829 : ℕ)^4563*20000000000000^3539 ≤ 8809575691111^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647299829 5000000000 8809575691111 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1735095213/10000000000 : ℝ)^4563 ≤ (5226291033/50000000000 : ℝ)^3539 := by
    have hnat : (1735095213 : ℕ)^4563*50000000000^3539 ≤ 5226291033^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735095213 10000000000 5226291033 50000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429438731/10000000000 : ℝ)^4563 ≤ (5687442432827/12500000000000 : ℝ)^3539 := by
    have hnat : (5429438731 : ℕ)^4563*12500000000000^3539 ≤ 5687442432827^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429438731 10000000000 5687442432827 12500000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647299829/5000000000 : ℝ), (-1735095213/10000000000 : ℝ), (5429438731/10000000000 : ℝ)] ![(8809575691111/20000000000000 : ℝ), (5226291033/50000000000 : ℝ), (5687442432827/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647299829/5000000000 : ℝ)|^4563 ≤ (8809575691111/20000000000000 : ℝ)^3539
        have hw : |(2647299829/5000000000 : ℝ)|=(2647299829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1735095213/10000000000 : ℝ)|^4563 ≤ (5226291033/50000000000 : ℝ)^3539
        have hw : |(-1735095213/10000000000 : ℝ)|=(1735095213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429438731/10000000000 : ℝ)|^4563 ≤ (5687442432827/12500000000000 : ℝ)^3539
        have hw : |(5429438731/10000000000 : ℝ)|=(5429438731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s5_6 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264729983/500000000 : ℝ)*x 0 + (2714719363/5000000000 : ℝ)*x 1 + (-1735095217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264729983/500000000 : ℝ)^4563 ≤ (2752992404813/6250000000000 : ℝ)^3539 := by
    have hnat : (264729983 : ℕ)^4563*6250000000000^3539 ≤ 2752992404813^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264729983 500000000 2752992404813 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714719363/5000000000 : ℝ)^4563 ≤ (45499539408591/100000000000000 : ℝ)^3539 := by
    have hnat : (2714719363 : ℕ)^4563*100000000000000^3539 ≤ 45499539408591^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714719363 5000000000 45499539408591 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1735095217/10000000000 : ℝ)^4563 ≤ (10452582097069/100000000000000 : ℝ)^3539 := by
    have hnat : (1735095217 : ℕ)^4563*100000000000000^3539 ≤ 10452582097069^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735095217 10000000000 10452582097069 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264729983/500000000 : ℝ), (2714719363/5000000000 : ℝ), (-1735095217/10000000000 : ℝ)] ![(2752992404813/6250000000000 : ℝ), (45499539408591/100000000000000 : ℝ), (10452582097069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264729983/500000000 : ℝ)|^4563 ≤ (2752992404813/6250000000000 : ℝ)^3539
        have hw : |(264729983/500000000 : ℝ)|=(264729983/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714719363/5000000000 : ℝ)|^4563 ≤ (45499539408591/100000000000000 : ℝ)^3539
        have hw : |(2714719363/5000000000 : ℝ)|=(2714719363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1735095217/10000000000 : ℝ)|^4563 ≤ (10452582097069/100000000000000 : ℝ)^3539
        have hw : |(-1735095217/10000000000 : ℝ)|=(1735095217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s5_7 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532519233/1250000000 : ℝ)*x 0 + (4507246863/10000000000 : ℝ)*x 1 + (2012299009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532519233/1250000000 : ℝ)^4563 ≤ (2080082301367/6250000000000 : ℝ)^3539 := by
    have hnat : (532519233 : ℕ)^4563*6250000000000^3539 ≤ 2080082301367^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532519233 1250000000 2080082301367 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507246863/10000000000 : ℝ)^4563 ≤ (8947702691841/25000000000000 : ℝ)^3539 := by
    have hnat : (4507246863 : ℕ)^4563*25000000000000^3539 ≤ 8947702691841^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507246863 10000000000 8947702691841 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012299009/5000000000 : ℝ)^4563 ≤ (3092787239107/10000000000000 : ℝ)^3539 := by
    have hnat : (2012299009 : ℕ)^4563*10000000000000^3539 ≤ 3092787239107^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012299009 5000000000 3092787239107 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532519233/1250000000 : ℝ), (4507246863/10000000000 : ℝ), (2012299009/5000000000 : ℝ)] ![(2080082301367/6250000000000 : ℝ), (8947702691841/25000000000000 : ℝ), (3092787239107/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532519233/1250000000 : ℝ)|^4563 ≤ (2080082301367/6250000000000 : ℝ)^3539
        have hw : |(532519233/1250000000 : ℝ)|=(532519233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507246863/10000000000 : ℝ)|^4563 ≤ (8947702691841/25000000000000 : ℝ)^3539
        have hw : |(4507246863/10000000000 : ℝ)|=(4507246863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012299009/5000000000 : ℝ)|^4563 ≤ (3092787239107/10000000000000 : ℝ)^3539
        have hw : |(2012299009/5000000000 : ℝ)|=(2012299009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1533_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5497/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10989/100000 : ℝ) ^ (4561/1024 : ℝ) ≤ (5349710756098553/100000000000000000000 : ℝ) := by
    have hpowers : (10989/100000 : ℝ)^4561 ≤ (5349710756098553/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10989 : ℕ)^4561*100000000000000000000^1024 ≤ 5349710756098553^1024*100000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10989 100000 5349710756098553 100000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10989/100000 : ℝ)) (X := (5349710756098553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4561/1024 : ℝ) ≤ (24683500780251719/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4561 ≤ (24683500780251719/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4561*100000000000000000000^1024 ≤ 24683500780251719^1024*10000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 24683500780251719 100000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (24683500780251719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005349710756098553/50000000000000000000 : ℝ) ≤ (10000240205067401/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50005349710756098553/50000000000000000000 : ℝ)^1024 ≤ (10000240205067401/10000000000000000 : ℝ)^4561 := by
      have hnat : (50005349710756098553 : ℕ)^1024*10000000000000000^4561 ≤ 10000240205067401^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005349710756098553 50000000000000000000 10000240205067401 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000240205067401/10000000000000000 : ℝ)) (X := (50005349710756098553/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1562969268930255473/1562500000000000000 : ℝ) ≤ (125008427545463/125000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (1562969268930255473/1562500000000000000 : ℝ)^1024 ≤ (125008427545463/125000000000000 : ℝ)^4561 := by
      have hnat : (1562969268930255473 : ℕ)^1024*125000000000000^4561 ≤ 125008427545463^4561*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562969268930255473 1562500000000000000 125008427545463 125000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125008427545463/125000000000000 : ℝ)) (X := (1562969268930255473/1562500000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024683500780251719/50000000000000000000 : ℝ) ≤ (10001108202206679/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50024683500780251719/50000000000000000000 : ℝ)^1024 ≤ (10001108202206679/10000000000000000 : ℝ)^4561 := by
      have hnat : (50024683500780251719 : ℕ)^1024*10000000000000000^4561 ≤ 10001108202206679^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024683500780251719 50000000000000000000 10001108202206679 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001108202206679/10000000000000000 : ℝ)) (X := (50024683500780251719/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5349710756098553/100000000000000000000 : ℝ) ≤ ((45001542742444845959/45010000000000000000 : ℝ)+2*(433998569639/450100000000000 : ℝ)*(10989/100000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (45001542742444845959/45010000000000000000 : ℝ)+2*(433998569639/450100000000000 : ℝ)*(10989/100000 : ℝ)=(10000240205067401/10000000000000000 : ℝ) by norm_num, show 1+2*(5349710756098553/100000000000000000000 : ℝ)=(50005349710756098553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24683500780251719/100000000000000000000 : ℝ)+(5349710756098553/100000000000000000000 : ℝ) ≤ ((45001542742444845959/45010000000000000000 : ℝ)+(433998569639/450100000000000 : ℝ)*((1549/10000 : ℝ)+(10989/100000 : ℝ)))^(4561/1024 : ℝ) := by
    rw [show (45001542742444845959/45010000000000000000 : ℝ)+(433998569639/450100000000000 : ℝ)*((1549/10000 : ℝ)+(10989/100000 : ℝ))=(125008427545463/125000000000000 : ℝ) by norm_num, show 1+(24683500780251719/100000000000000000000 : ℝ)+(5349710756098553/100000000000000000000 : ℝ)=(1562969268930255473/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24683500780251719/100000000000000000000 : ℝ) ≤ ((45001542742444845959/45010000000000000000 : ℝ)+2*(433998569639/450100000000000 : ℝ)*(1549/10000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (45001542742444845959/45010000000000000000 : ℝ)+2*(433998569639/450100000000000 : ℝ)*(1549/10000 : ℝ)=(10001108202206679/10000000000000000 : ℝ) by norm_num, show 1+2*(24683500780251719/100000000000000000000 : ℝ)=(50024683500780251719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45001542742444845959/45010000000000000000 : ℝ)*(X 1 0+X 2 0)+(433998569639/450100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (45001542742444845959/45010000000000000000 : ℝ)) (alpha := (433998569639/450100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45001542742444845959/45010000000000000000 : ℝ)*(X 0 1+X 2 1)+(433998569639/450100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (45001542742444845959/45010000000000000000 : ℝ)) (alpha := (433998569639/450100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45001542742444845959/45010000000000000000 : ℝ)*(X 0 2+X 1 2)+(433998569639/450100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (45001542742444845959/45010000000000000000 : ℝ)) (alpha := (433998569639/450100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-459357527/2500000000 : ℝ)*X 0 0+(2715271221/5000000000 : ℝ)*X 0 1+(2609301721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350405667/10000000000 : ℝ)*X 1 0+(-486482667/2500000000 : ℝ)*X 1 1+(5218603521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070081179/2000000000 : ℝ)*X 2 0+(5218603087/10000000000 : ℝ)*X 2 1+(-1945930939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4260088987/10000000000 : ℝ)*X 0 0+(4022057757/10000000000 : ℝ)*X 0 1+(4509768623/10000000000 : ℝ)*X 0 2+(4260088987/10000000000 : ℝ)*X 1 0+(4022057757/10000000000 : ℝ)*X 1 1+(4509768623/10000000000 : ℝ)*X 1 2+(4260088987/10000000000 : ℝ)*X 2 0+(4022057757/10000000000 : ℝ)*X 2 1+(4509768623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-73498331/400000000 : ℝ)*X 0 0+(1304924763/2500000000 : ℝ)*X 0 1+(5429438729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647299829/5000000000 : ℝ)*X 1 0+(-1735095213/10000000000 : ℝ)*X 1 1+(5429438731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264729983/500000000 : ℝ)*X 2 0+(2714719363/5000000000 : ℝ)*X 2 1+(-1735095217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((532519233/1250000000 : ℝ)*X 0 0+(4507246863/10000000000 : ℝ)*X 0 1+(2012299009/5000000000 : ℝ)*X 0 2+(532519233/1250000000 : ℝ)*X 1 0+(4507246863/10000000000 : ℝ)*X 1 1+(2012299009/5000000000 : ℝ)*X 1 2+(532519233/1250000000 : ℝ)*X 2 0+(4507246863/10000000000 : ℝ)*X 2 1+(2012299009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4410820595830913388177150207/562625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7370349/800000000000 : ℝ)*(base19) + (530330479/50000000000000 : ℝ)*(base23) + (1031609/3125000000000 : ℝ)*(lower2) + (57080791/20000000000000 : ℝ)*(upper3) + (3511373/50000000000000 : ℝ)*(upper5) + (846096749739291/25000000000000 : ℝ)*(major0) + (846096749739291/25000000000000 : ℝ)*(major1) + (846096749739291/25000000000000 : ℝ)*(major2) + (2359177207115119/50000000000000 : ℝ)*(sp0) + (4718362617506307/100000000000000 : ℝ)*(sp1) + (2359181239069487/50000000000000 : ℝ)*(sp2) + (256300101247297/12500000000000 : ℝ)*(sp3) + (9124569693/100000000000000 : ℝ)*(sp4) + (75102497/800000000000 : ℝ)*(sp7) + (2050410197790501/100000000000000 : ℝ)*(f.failure) + (1179590884699983/25000000000000 : ℝ)*(f.sum) + (52560528202869/22505000000000000000000000000 : ℝ)*base66 + (639669424294282133/160750000000000000000000000000000 : ℝ)*base68 + (592943065021717867/160750000000000000000000000000000 : ℝ)*base69 + (1432475426370782133/160750000000000000000000000000000 : ℝ)*base72 + (1683889979141/22505000000000000000000000000 : ℝ)*base73 + (671905465716217867/160750000000000000000000000000000 : ℝ)*base75 + (908078377601532133/160750000000000000000000000000000 : ℝ)*base78 + (1773378170633782133/160750000000000000000000000000000 : ℝ)*base80 + (9809769453941/5626250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (58159521/10000000000000000000000 : ℝ)*base89 + (58159521/10000000000000000000000 : ℝ)*base91 + (58159521/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3051843734532153703313537637/281312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (880920041/50000000000000 : ℝ)*(base19) + (475922383/25000000000000 : ℝ)*(base23) + (580246479/100000000000000 : ℝ)*(lower1) + (22596689/10000000000000 : ℝ)*(upper3) + (63607451/100000000000000 : ℝ)*(lower4) + (224197803/100000000000000 : ℝ)*(upper5) + (854959250472381/25000000000000 : ℝ)*(major0) + (854959250472381/25000000000000 : ℝ)*(major1) + (854959250472381/25000000000000 : ℝ)*(major2) + (944569803/50000000000000 : ℝ)*(sp2) + (119194656913871/2500000000000 : ℝ)*(sp4) + (4767784514714759/100000000000000 : ℝ)*(sp5) + (4767782483725703/100000000000000 : ℝ)*(sp6) + (129492960350283/6250000000000 : ℝ)*(sp7) + (129492960350283/6250000000000 : ℝ)*(f.failure) + (119194656913871/2500000000000 : ℝ)*(f.sum) + (4142219441469/5626250000000000000000000000 : ℝ)*base65 + (10289351062894448803/160750000000000000000000000000000 : ℝ)*base68 + (695038193484448803/160750000000000000000000000000000 : ℝ)*base70 + (33904577572046948803/160750000000000000000000000000000 : ℝ)*base72 + (126405614894351/22505000000000000000000000000 : ℝ)*base73 + (10727288962123801197/160750000000000000000000000000000 : ℝ)*base75 + (1447301684972948803/160750000000000000000000000000000 : ℝ)*base78 + (3554139284909448803/160750000000000000000000000000000 : ℝ)*base80 + (170985490580259/22505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4052943/625000000000000000000 : ℝ)*base89 + (4052943/625000000000000000000 : ℝ)*base91 + (4052943/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1533_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1533_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1533_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7961/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1533_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1533_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1533_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7961/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1533_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

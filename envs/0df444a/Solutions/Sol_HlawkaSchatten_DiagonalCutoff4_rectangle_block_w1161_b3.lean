-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1161_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:40:20.350635+00:00
-- url     : https://prove2.me/submissions/19f7569c-a127-404e-b813-3375fdefe1aa

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
theorem support_rectangle_w1161_s9_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157835897/10000000000 : ℝ)*x 0 + (2696321081/5000000000 : ℝ)*x 1 + (1053217387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157835897/10000000000 : ℝ)^4177 ≤ (3278442283013/25000000000000 : ℝ)^3153 := by
    have hnat : (2157835897 : ℕ)^4177*25000000000000^3153 ≤ 3278442283013^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157835897 10000000000 3278442283013 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696321081/5000000000 : ℝ)^4177 ≤ (11031607513867/25000000000000 : ℝ)^3153 := by
    have hnat : (2696321081 : ℕ)^4177*25000000000000^3153 ≤ 11031607513867^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696321081 5000000000 11031607513867 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053217387/2000000000 : ℝ)^4177 ≤ (21379900395447/50000000000000 : ℝ)^3153 := by
    have hnat : (1053217387 : ℕ)^4177*50000000000000^3153 ≤ 21379900395447^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053217387 2000000000 21379900395447 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157835897/10000000000 : ℝ), (2696321081/5000000000 : ℝ), (1053217387/2000000000 : ℝ)] ![(3278442283013/25000000000000 : ℝ), (11031607513867/25000000000000 : ℝ), (21379900395447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157835897/10000000000 : ℝ)|^4177 ≤ (3278442283013/25000000000000 : ℝ)^3153
        have hw : |(-2157835897/10000000000 : ℝ)|=(2157835897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696321081/5000000000 : ℝ)|^4177 ≤ (11031607513867/25000000000000 : ℝ)^3153
        have hw : |(2696321081/5000000000 : ℝ)|=(2696321081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053217387/2000000000 : ℝ)|^4177 ≤ (21379900395447/50000000000000 : ℝ)^3153
        have hw : |(1053217387/2000000000 : ℝ)|=(1053217387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s9_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336168381/2500000000 : ℝ)*x 0 + (-222202149/1000000000 : ℝ)*x 1 + (1053217387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336168381/2500000000 : ℝ)^4177 ≤ (174428770219/400000000000 : ℝ)^3153 := by
    have hnat : (1336168381 : ℕ)^4177*400000000000^3153 ≤ 174428770219^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336168381 2500000000 174428770219 400000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222202149/1000000000 : ℝ)^4177 ≤ (13633006639257/100000000000000 : ℝ)^3153 := by
    have hnat : (222202149 : ℕ)^4177*100000000000000^3153 ≤ 13633006639257^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222202149 1000000000 13633006639257 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053217387/2000000000 : ℝ)^4177 ≤ (21379900395447/50000000000000 : ℝ)^3153 := by
    have hnat : (1053217387 : ℕ)^4177*50000000000000^3153 ≤ 21379900395447^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053217387 2000000000 21379900395447 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336168381/2500000000 : ℝ), (-222202149/1000000000 : ℝ), (1053217387/2000000000 : ℝ)] ![(174428770219/400000000000 : ℝ), (13633006639257/100000000000000 : ℝ), (21379900395447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336168381/2500000000 : ℝ)|^4177 ≤ (174428770219/400000000000 : ℝ)^3153
        have hw : |(1336168381/2500000000 : ℝ)|=(1336168381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222202149/1000000000 : ℝ)|^4177 ≤ (13633006639257/100000000000000 : ℝ)^3153
        have hw : |(-222202149/1000000000 : ℝ)|=(222202149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053217387/2000000000 : ℝ)|^4177 ≤ (21379900395447/50000000000000 : ℝ)^3153
        have hw : |(1053217387/2000000000 : ℝ)|=(1053217387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s9_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336168381/2500000000 : ℝ)*x 0 + (1053217387/2000000000 : ℝ)*x 1 + (-222202149/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336168381/2500000000 : ℝ)^4177 ≤ (174428770219/400000000000 : ℝ)^3153 := by
    have hnat : (1336168381 : ℕ)^4177*400000000000^3153 ≤ 174428770219^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336168381 2500000000 174428770219 400000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053217387/2000000000 : ℝ)^4177 ≤ (21379900395447/50000000000000 : ℝ)^3153 := by
    have hnat : (1053217387 : ℕ)^4177*50000000000000^3153 ≤ 21379900395447^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053217387 2000000000 21379900395447 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222202149/1000000000 : ℝ)^4177 ≤ (13633006639257/100000000000000 : ℝ)^3153 := by
    have hnat : (222202149 : ℕ)^4177*100000000000000^3153 ≤ 13633006639257^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222202149 1000000000 13633006639257 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336168381/2500000000 : ℝ), (1053217387/2000000000 : ℝ), (-222202149/1000000000 : ℝ)] ![(174428770219/400000000000 : ℝ), (21379900395447/50000000000000 : ℝ), (13633006639257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336168381/2500000000 : ℝ)|^4177 ≤ (174428770219/400000000000 : ℝ)^3153
        have hw : |(1336168381/2500000000 : ℝ)|=(1336168381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053217387/2000000000 : ℝ)|^4177 ≤ (21379900395447/50000000000000 : ℝ)^3153
        have hw : |(1053217387/2000000000 : ℝ)|=(1053217387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222202149/1000000000 : ℝ)|^4177 ≤ (13633006639257/100000000000000 : ℝ)^3153
        have hw : |(-222202149/1000000000 : ℝ)|=(222202149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s9_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362005659/10000000000 : ℝ)*x 0 + (423746029/1000000000 : ℝ)*x 1 + (4490177299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362005659/10000000000 : ℝ)^4177 ≤ (16658546386453/50000000000000 : ℝ)^3153 := by
    have hnat : (4362005659 : ℕ)^4177*50000000000000^3153 ≤ 16658546386453^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362005659 10000000000 16658546386453 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423746029/1000000000 : ℝ)^4177 ≤ (8015686564319/25000000000000 : ℝ)^3153 := by
    have hnat : (423746029 : ℕ)^4177*25000000000000^3153 ≤ 8015686564319^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423746029 1000000000 8015686564319 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490177299/10000000000 : ℝ)^4177 ≤ (4327520118191/12500000000000 : ℝ)^3153 := by
    have hnat : (4490177299 : ℕ)^4177*12500000000000^3153 ≤ 4327520118191^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490177299 10000000000 4327520118191 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362005659/10000000000 : ℝ), (423746029/1000000000 : ℝ), (4490177299/10000000000 : ℝ)] ![(16658546386453/50000000000000 : ℝ), (8015686564319/25000000000000 : ℝ), (4327520118191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362005659/10000000000 : ℝ)|^4177 ≤ (16658546386453/50000000000000 : ℝ)^3153
        have hw : |(4362005659/10000000000 : ℝ)|=(4362005659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423746029/1000000000 : ℝ)|^4177 ≤ (8015686564319/25000000000000 : ℝ)^3153
        have hw : |(423746029/1000000000 : ℝ)|=(423746029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490177299/10000000000 : ℝ)|^4177 ≤ (4327520118191/12500000000000 : ℝ)^3153
        have hw : |(4490177299/10000000000 : ℝ)|=(4490177299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s9_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157840801/10000000000 : ℝ)*x 0 + (65830061/125000000 : ℝ)*x 1 + (1348080753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157840801/10000000000 : ℝ)^4177 ≤ (13113808614153/100000000000000 : ℝ)^3153 := by
    have hnat : (2157840801 : ℕ)^4177*100000000000000^3153 ≤ 13113808614153^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157840801 10000000000 13113808614153 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65830061/125000000 : ℝ)^4177 ≤ (10690805233761/25000000000000 : ℝ)^3153 := by
    have hnat : (65830061 : ℕ)^4177*25000000000000^3153 ≤ 10690805233761^3153*125000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65830061 125000000 10690805233761 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348080753/2500000000 : ℝ)^4177 ≤ (44122970435701/100000000000000 : ℝ)^3153 := by
    have hnat : (1348080753 : ℕ)^4177*100000000000000^3153 ≤ 44122970435701^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348080753 2500000000 44122970435701 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157840801/10000000000 : ℝ), (65830061/125000000 : ℝ), (1348080753/2500000000 : ℝ)] ![(13113808614153/100000000000000 : ℝ), (10690805233761/25000000000000 : ℝ), (44122970435701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157840801/10000000000 : ℝ)|^4177 ≤ (13113808614153/100000000000000 : ℝ)^3153
        have hw : |(-2157840801/10000000000 : ℝ)|=(2157840801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65830061/125000000 : ℝ)|^4177 ≤ (10690805233761/25000000000000 : ℝ)^3153
        have hw : |(65830061/125000000 : ℝ)|=(65830061/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348080753/2500000000 : ℝ)|^4177 ≤ (44122970435701/100000000000000 : ℝ)^3153
        have hw : |(1348080753/2500000000 : ℝ)|=(1348080753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s9_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656282663/5000000000 : ℝ)*x 0 + (-2095785427/10000000000 : ℝ)*x 1 + (539232301/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656282663/5000000000 : ℝ)^4177 ≤ (5407560063307/12500000000000 : ℝ)^3153 := by
    have hnat : (2656282663 : ℕ)^4177*12500000000000^3153 ≤ 5407560063307^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656282663 5000000000 5407560063307 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095785427/10000000000 : ℝ)^4177 ≤ (12616549058837/100000000000000 : ℝ)^3153 := by
    have hnat : (2095785427 : ℕ)^4177*100000000000000^3153 ≤ 12616549058837^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095785427 10000000000 12616549058837 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539232301/1000000000 : ℝ)^4177 ≤ (44122970414021/100000000000000 : ℝ)^3153 := by
    have hnat : (539232301 : ℕ)^4177*100000000000000^3153 ≤ 44122970414021^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539232301 1000000000 44122970414021 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656282663/5000000000 : ℝ), (-2095785427/10000000000 : ℝ), (539232301/1000000000 : ℝ)] ![(5407560063307/12500000000000 : ℝ), (12616549058837/100000000000000 : ℝ), (44122970414021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656282663/5000000000 : ℝ)|^4177 ≤ (5407560063307/12500000000000 : ℝ)^3153
        have hw : |(2656282663/5000000000 : ℝ)|=(2656282663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095785427/10000000000 : ℝ)|^4177 ≤ (12616549058837/100000000000000 : ℝ)^3153
        have hw : |(-2095785427/10000000000 : ℝ)|=(2095785427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539232301/1000000000 : ℝ)|^4177 ≤ (44122970414021/100000000000000 : ℝ)^3153
        have hw : |(539232301/1000000000 : ℝ)|=(539232301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s9_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328141351/2500000000 : ℝ)*x 0 + (5392323047/10000000000 : ℝ)*x 1 + (-261973159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328141351/2500000000 : ℝ)^4177 ≤ (21630240673947/50000000000000 : ℝ)^3153 := by
    have hnat : (1328141351 : ℕ)^4177*50000000000000^3153 ≤ 21630240673947^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328141351 2500000000 21630240673947 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392323047/10000000000 : ℝ)^4177 ≤ (44122970815101/100000000000000 : ℝ)^3153 := by
    have hnat : (5392323047 : ℕ)^4177*100000000000000^3153 ≤ 44122970815101^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392323047 10000000000 44122970815101 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261973159/1250000000 : ℝ)^4177 ≤ (6308273911351/50000000000000 : ℝ)^3153 := by
    have hnat : (261973159 : ℕ)^4177*50000000000000^3153 ≤ 6308273911351^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261973159 1250000000 6308273911351 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328141351/2500000000 : ℝ), (5392323047/10000000000 : ℝ), (-261973159/1250000000 : ℝ)] ![(21630240673947/50000000000000 : ℝ), (44122970815101/100000000000000 : ℝ), (6308273911351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328141351/2500000000 : ℝ)|^4177 ≤ (21630240673947/50000000000000 : ℝ)^3153
        have hw : |(1328141351/2500000000 : ℝ)|=(1328141351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392323047/10000000000 : ℝ)|^4177 ≤ (44122970815101/100000000000000 : ℝ)^3153
        have hw : |(5392323047/10000000000 : ℝ)|=(5392323047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261973159/1250000000 : ℝ)|^4177 ≤ (6308273911351/50000000000000 : ℝ)^3153
        have hw : |(-261973159/1250000000 : ℝ)|=(261973159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s9_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1090503849/2500000000 : ℝ)*x 0 + (4489542381/10000000000 : ℝ)*x 1 + (4138767/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090503849/2500000000 : ℝ)^4177 ≤ (6663438259593/20000000000000 : ℝ)^3153 := by
    have hnat : (1090503849 : ℕ)^4177*20000000000000^3153 ≤ 6663438259593^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090503849 2500000000 6663438259593 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489542381/10000000000 : ℝ)^4177 ≤ (34613675889027/100000000000000 : ℝ)^3153 := by
    have hnat : (4489542381 : ℕ)^4177*100000000000000^3153 ≤ 34613675889027^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489542381 10000000000 34613675889027 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4138767/9765625 : ℝ)^4177 ≤ (3206913280349/10000000000000 : ℝ)^3153 := by
    have hnat : (4138767 : ℕ)^4177*10000000000000^3153 ≤ 3206913280349^3153*9765625^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138767 9765625 3206913280349 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090503849/2500000000 : ℝ), (4489542381/10000000000 : ℝ), (4138767/9765625 : ℝ)] ![(6663438259593/20000000000000 : ℝ), (34613675889027/100000000000000 : ℝ), (3206913280349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090503849/2500000000 : ℝ)|^4177 ≤ (6663438259593/20000000000000 : ℝ)^3153
        have hw : |(1090503849/2500000000 : ℝ)|=(1090503849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489542381/10000000000 : ℝ)|^4177 ≤ (34613675889027/100000000000000 : ℝ)^3153
        have hw : |(4489542381/10000000000 : ℝ)|=(4489542381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4138767/9765625 : ℝ)|^4177 ≤ (3206913280349/10000000000000 : ℝ)^3153
        have hw : |(4138767/9765625 : ℝ)|=(4138767/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5689/50000 : ℝ) ^ (8353/2048 : ℝ) ≤ (882953801041939/6250000000000000000 : ℝ) := by
    have hpowers : (5689/50000 : ℝ)^8353 ≤ (882953801041939/6250000000000000000 : ℝ)^2048 := by
      have hnat : (5689 : ℕ)^8353*6250000000000000000^2048 ≤ 882953801041939^2048*50000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5689 50000 882953801041939 6250000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5689/50000 : ℝ)) (X := (882953801041939/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (703/5000 : ℝ) ^ (8353/2048 : ℝ) ≤ (33493583318753229/100000000000000000000 : ℝ) := by
    have hpowers : (703/5000 : ℝ)^8353 ≤ (33493583318753229/100000000000000000000 : ℝ)^2048 := by
      have hnat : (703 : ℕ)^8353*100000000000000000000^2048 ≤ 33493583318753229^2048*5000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 5000 33493583318753229 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/5000 : ℝ)) (X := (33493583318753229/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125882953801041939/3125000000000000000 : ℝ) ≤ (5000346337189341/5000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (3125882953801041939/3125000000000000000 : ℝ)^2048 ≤ (5000346337189341/5000000000000000 : ℝ)^8353 := by
      have hnat : (3125882953801041939 : ℕ)^2048*5000000000000000^8353 ≤ 5000346337189341^8353*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125882953801041939 3125000000000000000 5000346337189341 5000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000346337189341/5000000000000000 : ℝ)) (X := (3125882953801041939/3125000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047620844135424253/100000000000000000000 : ℝ) ≤ (10001167364605453/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (100047620844135424253/100000000000000000000 : ℝ)^2048 ≤ (10001167364605453/10000000000000000 : ℝ)^8353 := by
      have hnat : (100047620844135424253 : ℕ)^2048*10000000000000000^8353 ≤ 10001167364605453^8353*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047620844135424253 100000000000000000000 10001167364605453 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001167364605453/10000000000000000 : ℝ)) (X := (100047620844135424253/100000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033493583318753229/50000000000000000000 : ℝ) ≤ (312551314213507/312500000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50033493583318753229/50000000000000000000 : ℝ)^2048 ≤ (312551314213507/312500000000000 : ℝ)^8353 := by
      have hnat : (50033493583318753229 : ℕ)^2048*312500000000000^8353 ≤ 312551314213507^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033493583318753229 50000000000000000000 312551314213507 312500000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312551314213507/312500000000000 : ℝ)) (X := (50033493583318753229/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(882953801041939/6250000000000000000 : ℝ) ≤ ((3351381962735403031/3352500000000000000 : ℝ)+2*(474690226771/268200000000000 : ℝ)*(5689/50000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (3351381962735403031/3352500000000000000 : ℝ)+2*(474690226771/268200000000000 : ℝ)*(5689/50000 : ℝ)=(5000346337189341/5000000000000000 : ℝ) by norm_num, show 1+2*(882953801041939/6250000000000000000 : ℝ)=(3125882953801041939/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33493583318753229/100000000000000000000 : ℝ)+(882953801041939/6250000000000000000 : ℝ) ≤ ((3351381962735403031/3352500000000000000 : ℝ)+(474690226771/268200000000000 : ℝ)*((703/5000 : ℝ)+(5689/50000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (3351381962735403031/3352500000000000000 : ℝ)+(474690226771/268200000000000 : ℝ)*((703/5000 : ℝ)+(5689/50000 : ℝ))=(10001167364605453/10000000000000000 : ℝ) by norm_num, show 1+(33493583318753229/100000000000000000000 : ℝ)+(882953801041939/6250000000000000000 : ℝ)=(100047620844135424253/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33493583318753229/100000000000000000000 : ℝ) ≤ ((3351381962735403031/3352500000000000000 : ℝ)+2*(474690226771/268200000000000 : ℝ)*(703/5000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (3351381962735403031/3352500000000000000 : ℝ)+2*(474690226771/268200000000000 : ℝ)*(703/5000 : ℝ)=(312551314213507/312500000000000 : ℝ) by norm_num, show 1+2*(33493583318753229/100000000000000000000 : ℝ)=(50033493583318753229/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3351381962735403031/3352500000000000000 : ℝ)*(X 1 0+X 2 0)+(474690226771/268200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (3351381962735403031/3352500000000000000 : ℝ)) (alpha := (474690226771/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3351381962735403031/3352500000000000000 : ℝ)*(X 0 1+X 2 1)+(474690226771/268200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (3351381962735403031/3352500000000000000 : ℝ)) (alpha := (474690226771/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3351381962735403031/3352500000000000000 : ℝ)*(X 0 2+X 1 2)+(474690226771/268200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (3351381962735403031/3352500000000000000 : ℝ)) (alpha := (474690226771/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2157835897/10000000000 : ℝ)*X 0 0+(2696321081/5000000000 : ℝ)*X 0 1+(1053217387/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336168381/2500000000 : ℝ)*X 1 0+(-222202149/1000000000 : ℝ)*X 1 1+(1053217387/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336168381/2500000000 : ℝ)*X 2 0+(1053217387/2000000000 : ℝ)*X 2 1+(-222202149/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362005659/10000000000 : ℝ)*X 0 0+(423746029/1000000000 : ℝ)*X 0 1+(4490177299/10000000000 : ℝ)*X 0 2+(4362005659/10000000000 : ℝ)*X 1 0+(423746029/1000000000 : ℝ)*X 1 1+(4490177299/10000000000 : ℝ)*X 1 2+(4362005659/10000000000 : ℝ)*X 2 0+(423746029/1000000000 : ℝ)*X 2 1+(4490177299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157840801/10000000000 : ℝ)*X 0 0+(65830061/125000000 : ℝ)*X 0 1+(1348080753/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656282663/5000000000 : ℝ)*X 1 0+(-2095785427/10000000000 : ℝ)*X 1 1+(539232301/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328141351/2500000000 : ℝ)*X 2 0+(5392323047/10000000000 : ℝ)*X 2 1+(-261973159/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090503849/2500000000 : ℝ)*X 0 0+(4489542381/10000000000 : ℝ)*X 0 1+(4138767/9765625 : ℝ)*X 0 2+(1090503849/2500000000 : ℝ)*X 1 0+(4489542381/10000000000 : ℝ)*X 1 1+(4138767/9765625 : ℝ)*X 1 2+(1090503849/2500000000 : ℝ)*X 2 0+(4489542381/10000000000 : ℝ)*X 2 1+(4138767/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112419273274694151616216501/55875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40216179/10000000000000 : ℝ)*(base19) + (373987153/100000000000000 : ℝ)*(base23) + (1882303/12500000000000 : ℝ)*(lower2) + (6469/12500000000 : ℝ)*(upper3) + (7735317/25000000000000 : ℝ)*(upper5) + (5929358871642629/100000000000000 : ℝ)*(major0) + (5929358871642629/100000000000000 : ℝ)*(major1) + (5929358871642629/100000000000000 : ℝ)*(major2) + (7901700160661483/100000000000000 : ℝ)*(sp0) + (7901710740138043/100000000000000 : ℝ)*(sp1) + (197542769207817/2500000000000 : ℝ)*(sp2) + (1978500290388347/50000000000000 : ℝ)*(sp3) + (10981638349/100000000000000 : ℝ)*(sp4) + (5953142783/100000000000000 : ℝ)*(sp7) + (989251633479869/25000000000000 : ℝ)*(f.failure) + (7901711142299833/100000000000000 : ℝ)*(f.sum) + (145437503262781/13410000000000000000000000000 : ℝ)*base66 + (1115581547641715333/111750000000000000000000000000000 : ℝ)*base67 + (1809858504177215333/111750000000000000000000000000000 : ℝ)*base69 + (936865328273034667/111750000000000000000000000000000 : ℝ)*base72 + (40816141688371/13410000000000000000000000000 : ℝ)*base74 + (359303675136215333/111750000000000000000000000000000 : ℝ)*base75 + (537047383832034667/111750000000000000000000000000000 : ℝ)*base78 + (2508115458642215333/111750000000000000000000000000000 : ℝ)*base79 + (42579853675259/13410000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4939209/625000000000000000000 : ℝ)*base90 + (4939209/625000000000000000000 : ℝ)*base92 + (4939209/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145649859069441230365578257/55875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (776328413/100000000000000 : ℝ)*(base19) + (979898957/100000000000000 : ℝ)*(base23) + (111496911/50000000000000 : ℝ)*(lower1) + (2834633/100000000000000 : ℝ)*(upper2) + (66562451/50000000000000 : ℝ)*(upper3) + (72067719/100000000000000 : ℝ)*(upper5) + (5959327977143153/100000000000000 : ℝ)*(major0) + (5959327977143153/100000000000000 : ℝ)*(major1) + (5959327977143153/100000000000000 : ℝ)*(major2) + (13507079667/100000000000000 : ℝ)*(sp2) + (3970824601904233/50000000000000 : ℝ)*(sp4) + (1985412106870013/25000000000000 : ℝ)*(sp5) + (3970817358414921/50000000000000 : ℝ)*(sp6) + (3977006663587533/100000000000000 : ℝ)*(sp7) + (3977006663587533/100000000000000 : ℝ)*(f.failure) + (3970824601904233/50000000000000 : ℝ)*(f.sum) + (56502610434143/13410000000000000000000000000 : ℝ)*base65 + (416100731668628081/111750000000000000000000000000000 : ℝ)*base67 + (2058581680508378081/111750000000000000000000000000000 : ℝ)*base69 + (1600797697781378081/111750000000000000000000000000000 : ℝ)*base71 + (48774466765673/13410000000000000000000000000 : ℝ)*base73 + (339950691195621919/111750000000000000000000000000000 : ℝ)*base76 + (424754386875621919/111750000000000000000000000000000 : ℝ)*base78 + (387145732385378081/111750000000000000000000000000000 : ℝ)*base79 + (238021847261137/13410000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (12619913/2500000000000000000000 : ℝ)*base90 + (12619913/2500000000000000000000 : ℝ)*base92 + (12619913/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1161_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1161_box_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031571653/10000000000 : ℝ)*x 0 + (537603549/1000000000 : ℝ)*x 1 + (2688017449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031571653/10000000000 : ℝ)^4177 ≤ (12107005737033/100000000000000 : ℝ)^3153 := by
    have hnat : (2031571653 : ℕ)^4177*100000000000000^3153 ≤ 12107005737033^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031571653 10000000000 12107005737033 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537603549/1000000000 : ℝ)^4177 ≤ (43946500328051/100000000000000 : ℝ)^3153 := by
    have hnat : (537603549 : ℕ)^4177*100000000000000^3153 ≤ 43946500328051^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537603549 1000000000 43946500328051 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688017449/5000000000 : ℝ)^4177 ≤ (2746655869817/6250000000000 : ℝ)^3153 := by
    have hnat : (2688017449 : ℕ)^4177*6250000000000^3153 ≤ 2746655869817^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688017449 5000000000 2746655869817 6250000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031571653/10000000000 : ℝ), (537603549/1000000000 : ℝ), (2688017449/5000000000 : ℝ)] ![(12107005737033/100000000000000 : ℝ), (43946500328051/100000000000000 : ℝ), (2746655869817/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031571653/10000000000 : ℝ)|^4177 ≤ (12107005737033/100000000000000 : ℝ)^3153
        have hw : |(-2031571653/10000000000 : ℝ)|=(2031571653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537603549/1000000000 : ℝ)|^4177 ≤ (43946500328051/100000000000000 : ℝ)^3153
        have hw : |(537603549/1000000000 : ℝ)|=(537603549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688017449/5000000000 : ℝ)|^4177 ≤ (2746655869817/6250000000000 : ℝ)^3153
        have hw : |(2688017449/5000000000 : ℝ)|=(2688017449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2648079553/5000000000 : ℝ)*x 0 + (-267493/1250000 : ℝ)*x 1 + (1344008857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648079553/5000000000 : ℝ)^4177 ≤ (21541792236169/50000000000000 : ℝ)^3153 := by
    have hnat : (2648079553 : ℕ)^4177*50000000000000^3153 ≤ 21541792236169^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648079553 5000000000 21541792236169 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267493/1250000 : ℝ)^4177 ≤ (6484957924819/50000000000000 : ℝ)^3153 := by
    have hnat : (267493 : ℕ)^4177*50000000000000^3153 ≤ 6484957924819^3153*1250000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267493 1250000 6484957924819 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344008857/2500000000 : ℝ)^4177 ≤ (43946499656631/100000000000000 : ℝ)^3153 := by
    have hnat : (1344008857 : ℕ)^4177*100000000000000^3153 ≤ 43946499656631^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344008857 2500000000 43946499656631 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648079553/5000000000 : ℝ), (-267493/1250000 : ℝ), (1344008857/2500000000 : ℝ)] ![(21541792236169/50000000000000 : ℝ), (6484957924819/50000000000000 : ℝ), (43946499656631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648079553/5000000000 : ℝ)|^4177 ≤ (21541792236169/50000000000000 : ℝ)^3153
        have hw : |(2648079553/5000000000 : ℝ)|=(2648079553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267493/1250000 : ℝ)|^4177 ≤ (6484957924819/50000000000000 : ℝ)^3153
        have hw : |(-267493/1250000 : ℝ)|=(267493/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344008857/2500000000 : ℝ)|^4177 ≤ (43946499656631/100000000000000 : ℝ)^3153
        have hw : |(1344008857/2500000000 : ℝ)|=(1344008857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296158701/10000000000 : ℝ)*x 0 + (21504141/40000000 : ℝ)*x 1 + (-2139944783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296158701/10000000000 : ℝ)^4177 ≤ (43083580107719/100000000000000 : ℝ)^3153 := by
    have hnat : (5296158701 : ℕ)^4177*100000000000000^3153 ≤ 43083580107719^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296158701 10000000000 43083580107719 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21504141/40000000 : ℝ)^4177 ≤ (8789299545801/20000000000000 : ℝ)^3153 := by
    have hnat : (21504141 : ℕ)^4177*20000000000000^3153 ≤ 8789299545801^3153*40000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21504141 40000000 8789299545801 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139944783/10000000000 : ℝ)^4177 ≤ (2593984427309/20000000000000 : ℝ)^3153 := by
    have hnat : (2139944783 : ℕ)^4177*20000000000000^3153 ≤ 2593984427309^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139944783 10000000000 2593984427309 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296158701/10000000000 : ℝ), (21504141/40000000 : ℝ), (-2139944783/10000000000 : ℝ)] ![(43083580107719/100000000000000 : ℝ), (8789299545801/20000000000000 : ℝ), (2593984427309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296158701/10000000000 : ℝ)|^4177 ≤ (43083580107719/100000000000000 : ℝ)^3153
        have hw : |(5296158701/10000000000 : ℝ)|=(5296158701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21504141/40000000 : ℝ)|^4177 ≤ (8789299545801/20000000000000 : ℝ)^3153
        have hw : |(21504141/40000000 : ℝ)|=(21504141/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139944783/10000000000 : ℝ)|^4177 ≤ (2593984427309/20000000000000 : ℝ)^3153
        have hw : |(-2139944783/10000000000 : ℝ)|=(2139944783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1117336093/2500000000 : ℝ)*x 0 + (4310430741/10000000000 : ℝ)*x 1 + (4310431777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117336093/2500000000 : ℝ)^4177 ≤ (34407528898389/100000000000000 : ℝ)^3153 := by
    have hnat : (1117336093 : ℕ)^4177*100000000000000^3153 ≤ 34407528898389^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117336093 2500000000 34407528898389 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310430741/10000000000 : ℝ)^4177 ≤ (16398115162041/50000000000000 : ℝ)^3153 := by
    have hnat : (4310430741 : ℕ)^4177*50000000000000^3153 ≤ 16398115162041^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310430741 10000000000 16398115162041 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4310431777/10000000000 : ℝ)^4177 ≤ (32796240766559/100000000000000 : ℝ)^3153 := by
    have hnat : (4310431777 : ℕ)^4177*100000000000000^3153 ≤ 32796240766559^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310431777 10000000000 32796240766559 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1117336093/2500000000 : ℝ), (4310430741/10000000000 : ℝ), (4310431777/10000000000 : ℝ)] ![(34407528898389/100000000000000 : ℝ), (16398115162041/50000000000000 : ℝ), (32796240766559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1117336093/2500000000 : ℝ)|^4177 ≤ (34407528898389/100000000000000 : ℝ)^3153
        have hw : |(1117336093/2500000000 : ℝ)|=(1117336093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4310430741/10000000000 : ℝ)|^4177 ≤ (16398115162041/50000000000000 : ℝ)^3153
        have hw : |(4310430741/10000000000 : ℝ)|=(4310430741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4310431777/10000000000 : ℝ)|^4177 ≤ (32796240766559/100000000000000 : ℝ)^3153
        have hw : |(4310431777/10000000000 : ℝ)|=(4310431777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2285484059/10000000000 : ℝ)*x 0 + (2640690549/5000000000 : ℝ)*x 1 + (1320345257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2285484059/10000000000 : ℝ)^4177 ≤ (3537801937109/25000000000000 : ℝ)^3153 := by
    have hnat : (2285484059 : ℕ)^4177*25000000000000^3153 ≤ 3537801937109^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285484059 10000000000 3537801937109 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640690549/5000000000 : ℝ)^4177 ≤ (21462198248971/50000000000000 : ℝ)^3153 := by
    have hnat : (2640690549 : ℕ)^4177*50000000000000^3153 ≤ 21462198248971^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640690549 5000000000 21462198248971 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320345257/2500000000 : ℝ)^4177 ≤ (42924395744247/100000000000000 : ℝ)^3153 := by
    have hnat : (1320345257 : ℕ)^4177*100000000000000^3153 ≤ 42924395744247^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320345257 2500000000 42924395744247 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2285484059/10000000000 : ℝ), (2640690549/5000000000 : ℝ), (1320345257/2500000000 : ℝ)] ![(3537801937109/25000000000000 : ℝ), (21462198248971/50000000000000 : ℝ), (42924395744247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2285484059/10000000000 : ℝ)|^4177 ≤ (3537801937109/25000000000000 : ℝ)^3153
        have hw : |(-2285484059/10000000000 : ℝ)|=(2285484059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640690549/5000000000 : ℝ)|^4177 ≤ (21462198248971/50000000000000 : ℝ)^3153
        have hw : |(2640690549/5000000000 : ℝ)|=(2640690549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320345257/2500000000 : ℝ)|^4177 ≤ (42924395744247/100000000000000 : ℝ)^3153
        have hw : |(1320345257/2500000000 : ℝ)|=(1320345257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167593859/312500000 : ℝ)*x 0 + (-2177234921/10000000000 : ℝ)*x 1 + (2640690439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167593859/312500000 : ℝ)^4177 ≤ (21902713854347/50000000000000 : ℝ)^3153 := by
    have hnat : (167593859 : ℕ)^4177*50000000000000^3153 ≤ 21902713854347^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167593859 312500000 21902713854347 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177234921/10000000000 : ℝ)^4177 ≤ (13270178143097/100000000000000 : ℝ)^3153 := by
    have hnat : (2177234921 : ℕ)^4177*100000000000000^3153 ≤ 13270178143097^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177234921 10000000000 13270178143097 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640690439/5000000000 : ℝ)^4177 ≤ (10731098532297/25000000000000 : ℝ)^3153 := by
    have hnat : (2640690439 : ℕ)^4177*25000000000000^3153 ≤ 10731098532297^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640690439 5000000000 10731098532297 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167593859/312500000 : ℝ), (-2177234921/10000000000 : ℝ), (2640690439/5000000000 : ℝ)] ![(21902713854347/50000000000000 : ℝ), (13270178143097/100000000000000 : ℝ), (10731098532297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167593859/312500000 : ℝ)|^4177 ≤ (21902713854347/50000000000000 : ℝ)^3153
        have hw : |(167593859/312500000 : ℝ)|=(167593859/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177234921/10000000000 : ℝ)|^4177 ≤ (13270178143097/100000000000000 : ℝ)^3153
        have hw : |(-2177234921/10000000000 : ℝ)|=(2177234921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640690439/5000000000 : ℝ)|^4177 ≤ (10731098532297/25000000000000 : ℝ)^3153
        have hw : |(2640690439/5000000000 : ℝ)|=(2640690439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363003579/10000000000 : ℝ)*x 0 + (5281381001/10000000000 : ℝ)*x 1 + (-435446927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363003579/10000000000 : ℝ)^4177 ≤ (43805428693389/100000000000000 : ℝ)^3153 := by
    have hnat : (5363003579 : ℕ)^4177*100000000000000^3153 ≤ 43805428693389^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363003579 10000000000 43805428693389 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281381001/10000000000 : ℝ)^4177 ≤ (42924395453537/100000000000000 : ℝ)^3153 := by
    have hnat : (5281381001 : ℕ)^4177*100000000000000^3153 ≤ 42924395453537^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281381001 10000000000 42924395453537 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435446927/2000000000 : ℝ)^4177 ≤ (13270175833809/100000000000000 : ℝ)^3153 := by
    have hnat : (435446927 : ℕ)^4177*100000000000000^3153 ≤ 13270175833809^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435446927 2000000000 13270175833809 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363003579/10000000000 : ℝ), (5281381001/10000000000 : ℝ), (-435446927/2000000000 : ℝ)] ![(43805428693389/100000000000000 : ℝ), (42924395453537/100000000000000 : ℝ), (13270175833809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363003579/10000000000 : ℝ)|^4177 ≤ (43805428693389/100000000000000 : ℝ)^3153
        have hw : |(5363003579/10000000000 : ℝ)|=(5363003579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281381001/10000000000 : ℝ)|^4177 ≤ (42924395453537/100000000000000 : ℝ)^3153
        have hw : |(5281381001/10000000000 : ℝ)|=(5281381001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435446927/2000000000 : ℝ)|^4177 ≤ (13270175833809/100000000000000 : ℝ)^3153
        have hw : |(-435446927/2000000000 : ℝ)|=(435446927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254297959/10000000000 : ℝ)*x 0 + (441793381/1000000000 : ℝ)*x 1 + (4417933741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254297959/10000000000 : ℝ)^4177 ≤ (32231633728659/100000000000000 : ℝ)^3153 := by
    have hnat : (4254297959 : ℕ)^4177*100000000000000^3153 ≤ 32231633728659^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254297959 10000000000 32231633728659 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441793381/1000000000 : ℝ)^4177 ≤ (33884183479777/100000000000000 : ℝ)^3153 := by
    have hnat : (441793381 : ℕ)^4177*100000000000000^3153 ≤ 33884183479777^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441793381 1000000000 33884183479777 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417933741/10000000000 : ℝ)^4177 ≤ (33884182778697/100000000000000 : ℝ)^3153 := by
    have hnat : (4417933741 : ℕ)^4177*100000000000000^3153 ≤ 33884182778697^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417933741 10000000000 33884182778697 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254297959/10000000000 : ℝ), (441793381/1000000000 : ℝ), (4417933741/10000000000 : ℝ)] ![(32231633728659/100000000000000 : ℝ), (33884183479777/100000000000000 : ℝ), (33884182778697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254297959/10000000000 : ℝ)|^4177 ≤ (32231633728659/100000000000000 : ℝ)^3153
        have hw : |(4254297959/10000000000 : ℝ)|=(4254297959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441793381/1000000000 : ℝ)|^4177 ≤ (33884183479777/100000000000000 : ℝ)^3153
        have hw : |(441793381/1000000000 : ℝ)|=(441793381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417933741/10000000000 : ℝ)|^4177 ≤ (33884182778697/100000000000000 : ℝ)^3153
        have hw : |(4417933741/10000000000 : ℝ)|=(4417933741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_8 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1116182797/5000000000 : ℝ)*x 0 + (2608485069/5000000000 : ℝ)*x 1 + (2692822529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1116182797/5000000000 : ℝ)^4177 ≤ (13717147046589/100000000000000 : ℝ)^3153 := by
    have hnat : (1116182797 : ℕ)^4177*100000000000000^3153 ≤ 13717147046589^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116182797 5000000000 13717147046589 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608485069/5000000000 : ℝ)^4177 ≤ (42232256974343/100000000000000 : ℝ)^3153 := by
    have hnat : (2608485069 : ℕ)^4177*100000000000000^3153 ≤ 42232256974343^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608485069 5000000000 42232256974343 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692822529/5000000000 : ℝ)^4177 ≤ (44050595965043/100000000000000 : ℝ)^3153 := by
    have hnat : (2692822529 : ℕ)^4177*100000000000000^3153 ≤ 44050595965043^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692822529 5000000000 44050595965043 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1116182797/5000000000 : ℝ), (2608485069/5000000000 : ℝ), (2692822529/5000000000 : ℝ)] ![(13717147046589/100000000000000 : ℝ), (42232256974343/100000000000000 : ℝ), (44050595965043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1116182797/5000000000 : ℝ)|^4177 ≤ (13717147046589/100000000000000 : ℝ)^3153
        have hw : |(-1116182797/5000000000 : ℝ)|=(1116182797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608485069/5000000000 : ℝ)|^4177 ≤ (42232256974343/100000000000000 : ℝ)^3153
        have hw : |(2608485069/5000000000 : ℝ)|=(2608485069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692822529/5000000000 : ℝ)|^4177 ≤ (44050595965043/100000000000000 : ℝ)^3153
        have hw : |(2692822529/5000000000 : ℝ)|=(2692822529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_9 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644684843/5000000000 : ℝ)*x 0 + (-2136090297/10000000000 : ℝ)*x 1 + (2692822079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644684843/5000000000 : ℝ)^4177 ≤ (43010431236321/100000000000000 : ℝ)^3153 := by
    have hnat : (2644684843 : ℕ)^4177*100000000000000^3153 ≤ 43010431236321^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644684843 5000000000 43010431236321 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136090297/10000000000 : ℝ)^4177 ≤ (12938982537449/100000000000000 : ℝ)^3153 := by
    have hnat : (2136090297 : ℕ)^4177*100000000000000^3153 ≤ 12938982537449^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136090297 10000000000 12938982537449 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692822079/5000000000 : ℝ)^4177 ≤ (5506323276621/12500000000000 : ℝ)^3153 := by
    have hnat : (2692822079 : ℕ)^4177*12500000000000^3153 ≤ 5506323276621^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692822079 5000000000 5506323276621 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644684843/5000000000 : ℝ), (-2136090297/10000000000 : ℝ), (2692822079/5000000000 : ℝ)] ![(43010431236321/100000000000000 : ℝ), (12938982537449/100000000000000 : ℝ), (5506323276621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644684843/5000000000 : ℝ)|^4177 ≤ (43010431236321/100000000000000 : ℝ)^3153
        have hw : |(2644684843/5000000000 : ℝ)|=(2644684843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136090297/10000000000 : ℝ)|^4177 ≤ (12938982537449/100000000000000 : ℝ)^3153
        have hw : |(-2136090297/10000000000 : ℝ)|=(2136090297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692822079/5000000000 : ℝ)|^4177 ≤ (5506323276621/12500000000000 : ℝ)^3153
        have hw : |(2692822079/5000000000 : ℝ)|=(2692822079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_10 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057873811/2000000000 : ℝ)*x 0 + (2692822307/5000000000 : ℝ)*x 1 + (-66752829/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057873811/2000000000 : ℝ)^4177 ≤ (43010424438969/100000000000000 : ℝ)^3153 := by
    have hnat : (1057873811 : ℕ)^4177*100000000000000^3153 ≤ 43010424438969^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057873811 2000000000 43010424438969 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692822307/5000000000 : ℝ)^4177 ≤ (44050591154019/100000000000000 : ℝ)^3153 := by
    have hnat : (2692822307 : ℕ)^4177*100000000000000^3153 ≤ 44050591154019^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692822307 5000000000 44050591154019 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66752829/312500000 : ℝ)^4177 ≤ (12938984391121/100000000000000 : ℝ)^3153 := by
    have hnat : (66752829 : ℕ)^4177*100000000000000^3153 ≤ 12938984391121^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66752829 312500000 12938984391121 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057873811/2000000000 : ℝ), (2692822307/5000000000 : ℝ), (-66752829/312500000 : ℝ)] ![(43010424438969/100000000000000 : ℝ), (44050591154019/100000000000000 : ℝ), (12938984391121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057873811/2000000000 : ℝ)|^4177 ≤ (43010424438969/100000000000000 : ℝ)^3153
        have hw : |(1057873811/2000000000 : ℝ)|=(1057873811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692822307/5000000000 : ℝ)|^4177 ≤ (44050591154019/100000000000000 : ℝ)^3153
        have hw : |(2692822307/5000000000 : ℝ)|=(2692822307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66752829/312500000 : ℝ)|^4177 ≤ (12938984391121/100000000000000 : ℝ)^3153
        have hw : |(-66752829/312500000 : ℝ)|=(66752829/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_11 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2245451721/5000000000 : ℝ)*x 0 + (4299511123/10000000000 : ℝ)*x 1 + (53743891/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245451721/5000000000 : ℝ)^4177 ≤ (108211181687/312500000000 : ℝ)^3153 := by
    have hnat : (2245451721 : ℕ)^4177*312500000000^3153 ≤ 108211181687^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245451721 5000000000 108211181687 312500000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4299511123/10000000000 : ℝ)^4177 ≤ (8171552532159/25000000000000 : ℝ)^3153 := by
    have hnat : (4299511123 : ℕ)^4177*25000000000000^3153 ≤ 8171552532159^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299511123 10000000000 8171552532159 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53743891/125000000 : ℝ)^4177 ≤ (4085776463729/12500000000000 : ℝ)^3153 := by
    have hnat : (53743891 : ℕ)^4177*12500000000000^3153 ≤ 4085776463729^3153*125000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53743891 125000000 4085776463729 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245451721/5000000000 : ℝ), (4299511123/10000000000 : ℝ), (53743891/125000000 : ℝ)] ![(108211181687/312500000000 : ℝ), (8171552532159/25000000000000 : ℝ), (4085776463729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245451721/5000000000 : ℝ)|^4177 ≤ (108211181687/312500000000 : ℝ)^3153
        have hw : |(2245451721/5000000000 : ℝ)|=(2245451721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4299511123/10000000000 : ℝ)|^4177 ≤ (8171552532159/25000000000000 : ℝ)^3153
        have hw : |(4299511123/10000000000 : ℝ)|=(4299511123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53743891/125000000 : ℝ)|^4177 ≤ (4085776463729/12500000000000 : ℝ)^3153
        have hw : |(53743891/125000000 : ℝ)|=(53743891/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_12 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084997909/10000000000 : ℝ)*x 0 + (5439181621/10000000000 : ℝ)*x 1 + (5273334237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084997909/10000000000 : ℝ)^4177 ≤ (12530589885503/100000000000000 : ℝ)^3153 := by
    have hnat : (2084997909 : ℕ)^4177*100000000000000^3153 ≤ 12530589885503^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084997909 10000000000 12530589885503 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439181621/10000000000 : ℝ)^4177 ≤ (5578954150481/12500000000000 : ℝ)^3153 := by
    have hnat : (5439181621 : ℕ)^4177*12500000000000^3153 ≤ 5578954150481^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439181621 10000000000 5578954150481 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273334237/10000000000 : ℝ)^4177 ≤ (21418888446947/50000000000000 : ℝ)^3153 := by
    have hnat : (5273334237 : ℕ)^4177*50000000000000^3153 ≤ 21418888446947^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273334237 10000000000 21418888446947 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084997909/10000000000 : ℝ), (5439181621/10000000000 : ℝ), (5273334237/10000000000 : ℝ)] ![(12530589885503/100000000000000 : ℝ), (5578954150481/12500000000000 : ℝ), (21418888446947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084997909/10000000000 : ℝ)|^4177 ≤ (12530589885503/100000000000000 : ℝ)^3153
        have hw : |(-2084997909/10000000000 : ℝ)|=(2084997909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439181621/10000000000 : ℝ)|^4177 ≤ (5578954150481/12500000000000 : ℝ)^3153
        have hw : |(5439181621/10000000000 : ℝ)|=(5439181621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273334237/10000000000 : ℝ)|^4177 ≤ (21418888446947/50000000000000 : ℝ)^3153
        have hw : |(5273334237/10000000000 : ℝ)|=(5273334237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_13 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368683969/10000000000 : ℝ)*x 0 + (-1090173939/5000000000 : ℝ)*x 1 + (105466681/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368683969/10000000000 : ℝ)^4177 ≤ (43866905765971/100000000000000 : ℝ)^3153 := by
    have hnat : (5368683969 : ℕ)^4177*100000000000000^3153 ≤ 43866905765971^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368683969 10000000000 43866905765971 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090173939/5000000000 : ℝ)^4177 ≤ (1329531933573/10000000000000 : ℝ)^3153 := by
    have hnat : (1090173939 : ℕ)^4177*10000000000000^3153 ≤ 1329531933573^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090173939 5000000000 1329531933573 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105466681/200000000 : ℝ)^4177 ≤ (856755497629/2000000000000 : ℝ)^3153 := by
    have hnat : (105466681 : ℕ)^4177*2000000000000^3153 ≤ 856755497629^3153*200000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105466681 200000000 856755497629 2000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368683969/10000000000 : ℝ), (-1090173939/5000000000 : ℝ), (105466681/200000000 : ℝ)] ![(43866905765971/100000000000000 : ℝ), (1329531933573/10000000000000 : ℝ), (856755497629/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368683969/10000000000 : ℝ)|^4177 ≤ (43866905765971/100000000000000 : ℝ)^3153
        have hw : |(5368683969/10000000000 : ℝ)|=(5368683969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1090173939/5000000000 : ℝ)|^4177 ≤ (1329531933573/10000000000000 : ℝ)^3153
        have hw : |(-1090173939/5000000000 : ℝ)|=(1090173939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105466681/200000000 : ℝ)|^4177 ≤ (856755497629/2000000000000 : ℝ)^3153
        have hw : |(105466681/200000000 : ℝ)|=(105466681/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_14 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684342039/5000000000 : ℝ)*x 0 + (5273334133/10000000000 : ℝ)*x 1 + (-1090173811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684342039/5000000000 : ℝ)^4177 ≤ (21933453472923/50000000000000 : ℝ)^3153 := by
    have hnat : (2684342039 : ℕ)^4177*50000000000000^3153 ≤ 21933453472923^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684342039 5000000000 21933453472923 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273334133/10000000000 : ℝ)^4177 ≤ (21418887887337/50000000000000 : ℝ)^3153 := by
    have hnat : (5273334133 : ℕ)^4177*50000000000000^3153 ≤ 21418887887337^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273334133 10000000000 21418887887337 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090173811/5000000000 : ℝ)^4177 ≤ (3323829316929/25000000000000 : ℝ)^3153 := by
    have hnat : (1090173811 : ℕ)^4177*25000000000000^3153 ≤ 3323829316929^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090173811 5000000000 3323829316929 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684342039/5000000000 : ℝ), (5273334133/10000000000 : ℝ), (-1090173811/5000000000 : ℝ)] ![(21933453472923/50000000000000 : ℝ), (21418887887337/50000000000000 : ℝ), (3323829316929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684342039/5000000000 : ℝ)|^4177 ≤ (21933453472923/50000000000000 : ℝ)^3153
        have hw : |(2684342039/5000000000 : ℝ)|=(2684342039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273334133/10000000000 : ℝ)|^4177 ≤ (21418887887337/50000000000000 : ℝ)^3153
        have hw : |(5273334133/10000000000 : ℝ)|=(5273334133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1090173811/5000000000 : ℝ)|^4177 ≤ (3323829316929/25000000000000 : ℝ)^3153
        have hw : |(-1090173811/5000000000 : ℝ)|=(1090173811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_box_15 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117892713/5000000000 : ℝ)*x 0 + (4427067523/10000000000 : ℝ)*x 1 + (2213533981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117892713/5000000000 : ℝ)^4177 ≤ (32045958709899/100000000000000 : ℝ)^3153 := by
    have hnat : (2117892713 : ℕ)^4177*100000000000000^3153 ≤ 32045958709899^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117892713 5000000000 32045958709899 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4427067523/10000000000 : ℝ)^4177 ≤ (2123563650333/6250000000000 : ℝ)^3153 := by
    have hnat : (4427067523 : ℕ)^4177*6250000000000^3153 ≤ 2123563650333^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427067523 10000000000 2123563650333 6250000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213533981/5000000000 : ℝ)^4177 ≤ (16988511434407/50000000000000 : ℝ)^3153 := by
    have hnat : (2213533981 : ℕ)^4177*50000000000000^3153 ≤ 16988511434407^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213533981 5000000000 16988511434407 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117892713/5000000000 : ℝ), (4427067523/10000000000 : ℝ), (2213533981/5000000000 : ℝ)] ![(32045958709899/100000000000000 : ℝ), (2123563650333/6250000000000 : ℝ), (16988511434407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117892713/5000000000 : ℝ)|^4177 ≤ (32045958709899/100000000000000 : ℝ)^3153
        have hw : |(2117892713/5000000000 : ℝ)|=(2117892713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4427067523/10000000000 : ℝ)|^4177 ≤ (2123563650333/6250000000000 : ℝ)^3153
        have hw : |(4427067523/10000000000 : ℝ)|=(4427067523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2213533981/5000000000 : ℝ)|^4177 ≤ (16988511434407/50000000000000 : ℝ)^3153
        have hw : |(2213533981/5000000000 : ℝ)|=(2213533981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62233/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59313/100000 : ℝ) ∧ (39933/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83167/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11379/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (14132325628528391/100000000000000000000 : ℝ) := by
    have hpowers : (11379/100000 : ℝ)^8353 ≤ (14132325628528391/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11379 : ℕ)^8353*100000000000000000000^2048 ≤ 14132325628528391^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11379 100000 14132325628528391 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11379/100000 : ℝ)) (X := (14132325628528391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14059/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (33483868352995839/100000000000000000000 : ℝ) := by
    have hpowers : (14059/100000 : ℝ)^8353 ≤ (33483868352995839/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14059 : ℕ)^8353*100000000000000000000^2048 ≤ 33483868352995839^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14059 100000 33483868352995839 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14059/100000 : ℝ)) (X := (33483868352995839/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014132325628528391/50000000000000000000 : ℝ) ≤ (5000346461342611/5000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50014132325628528391/50000000000000000000 : ℝ)^2048 ≤ (5000346461342611/5000000000000000 : ℝ)^8353 := by
      have hnat : (50014132325628528391 : ℕ)^2048*5000000000000000^8353 ≤ 5000346461342611^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014132325628528391 50000000000000000000 5000346461342611 5000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000346461342611/5000000000000000 : ℝ)) (X := (50014132325628528391/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004761619398152423/10000000000000000000 : ℝ) ≤ (2000233450126661/2000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (10004761619398152423/10000000000000000000 : ℝ)^2048 ≤ (2000233450126661/2000000000000000 : ℝ)^8353 := by
      have hnat : (10004761619398152423 : ℕ)^2048*2000000000000000^8353 ≤ 2000233450126661^8353*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004761619398152423 10000000000000000000 2000233450126661 2000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000233450126661/2000000000000000 : ℝ)) (X := (10004761619398152423/10000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033483868352995839/50000000000000000000 : ℝ) ≤ (2500410394645347/2500000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50033483868352995839/50000000000000000000 : ℝ)^2048 ≤ (2500410394645347/2500000000000000 : ℝ)^8353 := by
      have hnat : (50033483868352995839 : ℕ)^2048*2500000000000000^8353 ≤ 2500410394645347^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033483868352995839 50000000000000000000 2500410394645347 2500000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500410394645347/2500000000000000 : ℝ)) (X := (50033483868352995839/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14132325628528391/100000000000000000000 : ℝ) ≤ ((13395531138676961023/13400000000000000000 : ℝ)+2*(474327948083/268000000000000 : ℝ)*(11379/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (13395531138676961023/13400000000000000000 : ℝ)+2*(474327948083/268000000000000 : ℝ)*(11379/100000 : ℝ)=(5000346461342611/5000000000000000 : ℝ) by norm_num, show 1+2*(14132325628528391/100000000000000000000 : ℝ)=(50014132325628528391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33483868352995839/100000000000000000000 : ℝ)+(14132325628528391/100000000000000000000 : ℝ) ≤ ((13395531138676961023/13400000000000000000 : ℝ)+(474327948083/268000000000000 : ℝ)*((14059/100000 : ℝ)+(11379/100000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (13395531138676961023/13400000000000000000 : ℝ)+(474327948083/268000000000000 : ℝ)*((14059/100000 : ℝ)+(11379/100000 : ℝ))=(2000233450126661/2000000000000000 : ℝ) by norm_num, show 1+(33483868352995839/100000000000000000000 : ℝ)+(14132325628528391/100000000000000000000 : ℝ)=(10004761619398152423/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33483868352995839/100000000000000000000 : ℝ) ≤ ((13395531138676961023/13400000000000000000 : ℝ)+2*(474327948083/268000000000000 : ℝ)*(14059/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (13395531138676961023/13400000000000000000 : ℝ)+2*(474327948083/268000000000000 : ℝ)*(14059/100000 : ℝ)=(2500410394645347/2500000000000000 : ℝ) by norm_num, show 1+2*(33483868352995839/100000000000000000000 : ℝ)=(50033483868352995839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13395531138676961023/13400000000000000000 : ℝ)*(X 1 0+X 2 0)+(474327948083/268000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (13395531138676961023/13400000000000000000 : ℝ)) (alpha := (474327948083/268000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13395531138676961023/13400000000000000000 : ℝ)*(X 0 1+X 2 1)+(474327948083/268000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (13395531138676961023/13400000000000000000 : ℝ)) (alpha := (474327948083/268000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13395531138676961023/13400000000000000000 : ℝ)*(X 0 2+X 1 2)+(474327948083/268000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (13395531138676961023/13400000000000000000 : ℝ)) (alpha := (474327948083/268000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2031571653/10000000000 : ℝ)*X 0 0+(537603549/1000000000 : ℝ)*X 0 1+(2688017449/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648079553/5000000000 : ℝ)*X 1 0+(-267493/1250000 : ℝ)*X 1 1+(1344008857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296158701/10000000000 : ℝ)*X 2 0+(21504141/40000000 : ℝ)*X 2 1+(-2139944783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1117336093/2500000000 : ℝ)*X 0 0+(4310430741/10000000000 : ℝ)*X 0 1+(4310431777/10000000000 : ℝ)*X 0 2+(1117336093/2500000000 : ℝ)*X 1 0+(4310430741/10000000000 : ℝ)*X 1 1+(4310431777/10000000000 : ℝ)*X 1 2+(1117336093/2500000000 : ℝ)*X 2 0+(4310430741/10000000000 : ℝ)*X 2 1+(4310431777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2285484059/10000000000 : ℝ)*X 0 0+(2640690549/5000000000 : ℝ)*X 0 1+(1320345257/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((167593859/312500000 : ℝ)*X 1 0+(-2177234921/10000000000 : ℝ)*X 1 1+(2640690439/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363003579/10000000000 : ℝ)*X 2 0+(5281381001/10000000000 : ℝ)*X 2 1+(-435446927/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4254297959/10000000000 : ℝ)*X 0 0+(441793381/1000000000 : ℝ)*X 0 1+(4417933741/10000000000 : ℝ)*X 0 2+(4254297959/10000000000 : ℝ)*X 1 0+(441793381/1000000000 : ℝ)*X 1 1+(4417933741/10000000000 : ℝ)*X 1 2+(4254297959/10000000000 : ℝ)*X 2 0+(441793381/1000000000 : ℝ)*X 2 1+(4417933741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1116182797/5000000000 : ℝ)*X 0 0+(2608485069/5000000000 : ℝ)*X 0 1+(2692822529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644684843/5000000000 : ℝ)*X 1 0+(-2136090297/10000000000 : ℝ)*X 1 1+(2692822079/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057873811/2000000000 : ℝ)*X 2 0+(2692822307/5000000000 : ℝ)*X 2 1+(-66752829/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2245451721/5000000000 : ℝ)*X 0 0+(4299511123/10000000000 : ℝ)*X 0 1+(53743891/125000000 : ℝ)*X 0 2+(2245451721/5000000000 : ℝ)*X 1 0+(4299511123/10000000000 : ℝ)*X 1 1+(53743891/125000000 : ℝ)*X 1 2+(2245451721/5000000000 : ℝ)*X 2 0+(4299511123/10000000000 : ℝ)*X 2 1+(53743891/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2084997909/10000000000 : ℝ)*X 0 0+(5439181621/10000000000 : ℝ)*X 0 1+(5273334237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368683969/10000000000 : ℝ)*X 1 0+(-1090173939/5000000000 : ℝ)*X 1 1+(105466681/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684342039/5000000000 : ℝ)*X 2 0+(5273334133/10000000000 : ℝ)*X 2 1+(-1090173811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2117892713/5000000000 : ℝ)*X 0 0+(4427067523/10000000000 : ℝ)*X 0 1+(2213533981/5000000000 : ℝ)*X 0 2+(2117892713/5000000000 : ℝ)*X 1 0+(4427067523/10000000000 : ℝ)*X 1 1+(2213533981/5000000000 : ℝ)*X 1 2+(2117892713/5000000000 : ℝ)*X 2 0+(4427067523/10000000000 : ℝ)*X 2 1+(2213533981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62233/100000 : ℝ) ≤ (-52118359648218568151550000038073/83750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4132131/10000000000000 : ℝ)*(upper0) + (84675621/100000000000000 : ℝ)*(lower2) + (2118043/3125000000000 : ℝ)*(upper4) + (32867853/100000000000000 : ℝ)*(upper5) + (492065070982961/12500000000000 : ℝ)*(major0) + (492065070982961/12500000000000 : ℝ)*(major1) + (492065070982961/12500000000000 : ℝ)*(major2) + (15637198621/100000000000000 : ℝ)*(sp1) + (496278451/12500000000000 : ℝ)*(sp3) + (329169292664851/6250000000000 : ℝ)*(sp4) + (5266699664449517/100000000000000 : ℝ)*(sp5) + (5266715301648139/100000000000000 : ℝ)*(sp6) + (164191593098891/6250000000000 : ℝ)*(sp7) + (6619010523/100000000000000 : ℝ)*(sp8) + (328383682476233/12500000000000 : ℝ)*(f.failure) + (5266715301648139/100000000000000 : ℝ)*(f.sum) + (2978385084813/1675000000000000000000000000 : ℝ)*base65 + (626803327942720897/167500000000000000000000000000000 : ℝ)*base68 + (2377040352162720897/167500000000000000000000000000000 : ℝ)*base70 + (1097399330252720897/167500000000000000000000000000000 : ℝ)*base72 + (61050992831/837500000000000000000000000 : ℝ)*base74 + (109490029272720897/167500000000000000000000000000000 : ℝ)*base76 + (2076433707885220897/167500000000000000000000000000000 : ℝ)*base78 + (1929394312940220897/167500000000000000000000000000000 : ℝ)*base80 + (87632502481/837500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3609387/312500000000000000000 : ℝ)*base89 + (3609387/312500000000000000000 : ℝ)*base91 + (3609387/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59313/100000 : ℝ) ≤ (397415456873357861133300559779963/670000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23086463/100000000000000 : ℝ)*(lower1) + (158594733/100000000000000 : ℝ)*(upper2) + (345963023/100000000000000 : ℝ)*(lower4) + (4000992805775927/100000000000000 : ℝ)*(major0) + (4000992805775927/100000000000000 : ℝ)*(major1) + (4000992805775927/100000000000000 : ℝ)*(major2) + (5312116723322307/100000000000000 : ℝ)*(sp0) + (5312089296128469/100000000000000 : ℝ)*(sp1) + (265598802590991/5000000000000 : ℝ)*(sp2) + (667523562695417/25000000000000 : ℝ)*(sp3) + (5772551063/20000000000000 : ℝ)*(sp5) + (1288609117/100000000000000 : ℝ)*(sp7) + (142107063963/100000000000000 : ℝ)*(sp10) + (358890369/25000000000000 : ℝ)*(sp12) + (534019107878157/20000000000000 : ℝ)*(f.failure) + (5312118158883783/100000000000000 : ℝ)*(f.sum) + (21668370108341/13400000000000000000000000000 : ℝ)*base65 + (6698627112812256679/1340000000000000000000000000000000 : ℝ)*base68 + (4446883671792256679/1340000000000000000000000000000000 : ℝ)*base70 + (8596177460472256679/1340000000000000000000000000000000 : ℝ)*base72 + (21143584581741/13400000000000000000000000000 : ℝ)*base73 + (947496970847743321/1340000000000000000000000000000000 : ℝ)*base75 + (8729361870812256679/1340000000000000000000000000000000 : ℝ)*base78 + (2094999264147743321/1340000000000000000000000000000000 : ℝ)*base79 + (38048641797341/13400000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (559177/500000000000000000000 : ℝ)*base90 + (559177/500000000000000000000 : ℝ)*base92 + (559177/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39933/50000 : ℝ) ≤ (267560218283818836442348866660687/335000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38681039/25000000000000 : ℝ)*(upper0) + (67435479/25000000000000 : ℝ)*(upper1) + (330237693/100000000000000 : ℝ)*(upper2) + (2234362496382359/50000000000000 : ℝ)*(major0) + (2234362496382359/50000000000000 : ℝ)*(major1) + (2234362496382359/50000000000000 : ℝ)*(major2) + (12918529679/20000000000000 : ℝ)*(sp2) + (80416154029/100000000000000 : ℝ)*(sp3) + (21525801127/100000000000000 : ℝ)*(sp4) + (2964280786868093/50000000000000 : ℝ)*(sp8) + (2964293303571217/50000000000000 : ℝ)*(sp9) + (5928522014494039/100000000000000 : ℝ)*(sp10) + (1491080027470521/50000000000000 : ℝ)*(sp11) + (3507605121/100000000000000 : ℝ)*(sp12) + (93195014721721/3125000000000 : ℝ)*(f.failure) + (2964293303571217/50000000000000 : ℝ)*(f.sum) + (21605684518403/6700000000000000000000000000 : ℝ)*base66 + (4730787531237643257/670000000000000000000000000000000 : ℝ)*base67 + (6475641460557643257/670000000000000000000000000000000 : ℝ)*base69 + (6122719790017643257/670000000000000000000000000000000 : ℝ)*base71 + (4524835595897/6700000000000000000000000000 : ℝ)*base73 + (7189402141387643257/670000000000000000000000000000000 : ℝ)*base75 + (7665299438297643257/670000000000000000000000000000000 : ℝ)*base77 + (251309945767643257/670000000000000000000000000000000 : ℝ)*base79 + (34864146380597/6700000000000000000000000000 : ℝ)*base81 + (762719/78125000000000000000 : ℝ)*base89 + (762719/78125000000000000000 : ℝ)*base91 + (762719/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83167/100000 : ℝ) ≤ (-272070912922283178474001995477/327148437500000000000000000000 : ℝ) := by norm_num
    linear_combination (330077/1000000000000 : ℝ)*(lower1) + (61518569/100000000000000 : ℝ)*(lower2) + (51120043/20000000000000 : ℝ)*(upper5) + (35185693159711/781250000000 : ℝ)*(major0) + (35185693159711/781250000000 : ℝ)*(major1) + (35185693159711/781250000000 : ℝ)*(major2) + (1876896479/100000000000000 : ℝ)*(sp0) + (4101930973/2000000000000 : ℝ)*(sp5) + (21249738997/10000000000000 : ℝ)*(sp6) + (42877586119/100000000000000 : ℝ)*(sp7) + (241185193272627/4000000000000 : ℝ)*(sp12) + (1205885322432701/20000000000000 : ℝ)*(sp13) + (1205883842264437/20000000000000 : ℝ)*(sp14) + (1502792158399957/50000000000000 : ℝ)*(sp15) + (1502813597193017/50000000000000 : ℝ)*(f.failure) + (3014815854356077/50000000000000 : ℝ)*(f.sum) + (12359848586817/1675000000000000000000000000 : ℝ)*base66 + (80234989316374397/10468750000000000000000000000000 : ℝ)*base68 + (89395817263469353/10468750000000000000000000000000 : ℝ)*base69 + (2865710583718147/10468750000000000000000000000000 : ℝ)*base72 + (1087008138473/418750000000000000000000000 : ℝ)*base74 + (89645674269499397/10468750000000000000000000000000 : ℝ)*base76 + (32118858162624397/10468750000000000000000000000000 : ℝ)*base78 + (29847342946061897/10468750000000000000000000000000 : ℝ)*base80 + (3789778596017/1675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (19666363/1250000000000000000000 : ℝ)*base89 + (19666363/1250000000000000000000 : ℝ)*base91 + (19666363/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1161_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59313/100000 : ℝ) else (39933/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83167/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1161_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1161_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59313/100000 : ℝ) else (39933/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83167/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1161_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1161_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59313/100000 : ℝ) else (39933/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83167/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1161_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

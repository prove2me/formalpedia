-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1554_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:47.136239+00:00
-- url     : https://prove2.me/submissions/4733ffef-33cf-4400-a3e6-7b580338c807

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
theorem support_rectangle_w1554_s0_0 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32843609/200000000 : ℝ)*x 0 + (2940607549/5000000000 : ℝ)*x 1 + (2436437757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32843609/200000000 : ℝ)^4605 ≤ (4898212504671/50000000000000 : ℝ)^3581 := by
    have hnat : (32843609 : ℕ)^4605*50000000000000^3581 ≤ 4898212504671^3581*200000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32843609 200000000 4898212504671 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2940607549/5000000000 : ℝ)^4605 ≤ (2021181532639/4000000000000 : ℝ)^3581 := by
    have hnat : (2940607549 : ℕ)^4605*4000000000000^3581 ≤ 2021181532639^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2940607549 5000000000 2021181532639 4000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2436437757/5000000000 : ℝ)^4605 ≤ (19837018328461/50000000000000 : ℝ)^3581 := by
    have hnat : (2436437757 : ℕ)^4605*50000000000000^3581 ≤ 19837018328461^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436437757 5000000000 19837018328461 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32843609/200000000 : ℝ), (2940607549/5000000000 : ℝ), (2436437757/5000000000 : ℝ)] ![(4898212504671/50000000000000 : ℝ), (2021181532639/4000000000000 : ℝ), (19837018328461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32843609/200000000 : ℝ)|^4605 ≤ (4898212504671/50000000000000 : ℝ)^3581
        have hw : |(-32843609/200000000 : ℝ)|=(32843609/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2940607549/5000000000 : ℝ)|^4605 ≤ (2021181532639/4000000000000 : ℝ)^3581
        have hw : |(2940607549/5000000000 : ℝ)|=(2940607549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2436437757/5000000000 : ℝ)|^4605 ≤ (19837018328461/50000000000000 : ℝ)^3581
        have hw : |(2436437757/5000000000 : ℝ)|=(2436437757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s0_1 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2734450933/5000000000 : ℝ)*x 0 + (-2204395229/10000000000 : ℝ)*x 1 + (4872875513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2734450933/5000000000 : ℝ)^4605 ≤ (46020540772321/100000000000000 : ℝ)^3581 := by
    have hnat : (2734450933 : ℕ)^4605*100000000000000^3581 ≤ 46020540772321^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734450933 5000000000 46020540772321 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204395229/10000000000 : ℝ)^4605 ≤ (14305422568483/100000000000000 : ℝ)^3581 := by
    have hnat : (2204395229 : ℕ)^4605*100000000000000^3581 ≤ 14305422568483^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204395229 10000000000 14305422568483 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4872875513/10000000000 : ℝ)^4605 ≤ (9918509161613/25000000000000 : ℝ)^3581 := by
    have hnat : (4872875513 : ℕ)^4605*25000000000000^3581 ≤ 9918509161613^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4872875513 10000000000 9918509161613 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2734450933/5000000000 : ℝ), (-2204395229/10000000000 : ℝ), (4872875513/10000000000 : ℝ)] ![(46020540772321/100000000000000 : ℝ), (14305422568483/100000000000000 : ℝ), (9918509161613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2734450933/5000000000 : ℝ)|^4605 ≤ (46020540772321/100000000000000 : ℝ)^3581
        have hw : |(2734450933/5000000000 : ℝ)|=(2734450933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2204395229/10000000000 : ℝ)|^4605 ≤ (14305422568483/100000000000000 : ℝ)^3581
        have hw : |(-2204395229/10000000000 : ℝ)|=(2204395229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4872875513/10000000000 : ℝ)|^4605 ≤ (9918509161613/25000000000000 : ℝ)^3581
        have hw : |(4872875513/10000000000 : ℝ)|=(4872875513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s0_2 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5468901903/10000000000 : ℝ)*x 0 + (4872875469/10000000000 : ℝ)*x 1 + (-440879047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5468901903/10000000000 : ℝ)^4605 ≤ (46020541172707/100000000000000 : ℝ)^3581 := by
    have hnat : (5468901903 : ℕ)^4605*100000000000000^3581 ≤ 46020541172707^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468901903 10000000000 46020541172707 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4872875469/10000000000 : ℝ)^4605 ≤ (9918509046443/25000000000000 : ℝ)^3581 := by
    have hnat : (4872875469 : ℕ)^4605*25000000000000^3581 ≤ 9918509046443^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4872875469 10000000000 9918509046443 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440879047/2000000000 : ℝ)^4605 ≤ (2861084523711/20000000000000 : ℝ)^3581 := by
    have hnat : (440879047 : ℕ)^4605*20000000000000^3581 ≤ 2861084523711^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440879047 2000000000 2861084523711 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5468901903/10000000000 : ℝ), (4872875469/10000000000 : ℝ), (-440879047/2000000000 : ℝ)] ![(46020541172707/100000000000000 : ℝ), (9918509046443/25000000000000 : ℝ), (2861084523711/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5468901903/10000000000 : ℝ)|^4605 ≤ (46020541172707/100000000000000 : ℝ)^3581
        have hw : |(5468901903/10000000000 : ℝ)|=(5468901903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4872875469/10000000000 : ℝ)|^4605 ≤ (9918509046443/25000000000000 : ℝ)^3581
        have hw : |(4872875469/10000000000 : ℝ)|=(4872875469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440879047/2000000000 : ℝ)|^4605 ≤ (2861084523711/20000000000000 : ℝ)^3581
        have hw : |(-440879047/2000000000 : ℝ)|=(440879047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s0_3 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4134003089/10000000000 : ℝ)*x 0 + (3092366669/10000000000 : ℝ)*x 1 + (2723346343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4134003089/10000000000 : ℝ)^4605 ≤ (32112242006479/100000000000000 : ℝ)^3581 := by
    have hnat : (4134003089 : ℕ)^4605*100000000000000^3581 ≤ 32112242006479^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134003089 10000000000 32112242006479 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3092366669/10000000000 : ℝ)^4605 ≤ (22107408329671/100000000000000 : ℝ)^3581 := by
    have hnat : (3092366669 : ℕ)^4605*100000000000000^3581 ≤ 22107408329671^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3092366669 10000000000 22107408329671 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723346343/5000000000 : ℝ)^4605 ≤ (2289017482719/5000000000000 : ℝ)^3581 := by
    have hnat : (2723346343 : ℕ)^4605*5000000000000^3581 ≤ 2289017482719^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723346343 5000000000 2289017482719 5000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4134003089/10000000000 : ℝ), (3092366669/10000000000 : ℝ), (2723346343/5000000000 : ℝ)] ![(32112242006479/100000000000000 : ℝ), (22107408329671/100000000000000 : ℝ), (2289017482719/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4134003089/10000000000 : ℝ)|^4605 ≤ (32112242006479/100000000000000 : ℝ)^3581
        have hw : |(4134003089/10000000000 : ℝ)|=(4134003089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3092366669/10000000000 : ℝ)|^4605 ≤ (22107408329671/100000000000000 : ℝ)^3581
        have hw : |(3092366669/10000000000 : ℝ)|=(3092366669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723346343/5000000000 : ℝ)|^4605 ≤ (2289017482719/5000000000000 : ℝ)^3581
        have hw : |(2723346343/5000000000 : ℝ)|=(2723346343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s0_4 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-205669723/1250000000 : ℝ)*x 0 + (4898376983/10000000000 : ℝ)*x 1 + (1170961429/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205669723/1250000000 : ℝ)^4605 ≤ (9820806204663/100000000000000 : ℝ)^3581 := by
    have hnat : (205669723 : ℕ)^4605*100000000000000^3581 ≤ 9820806204663^3581*1250000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205669723 1250000000 9820806204663 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4898376983/10000000000 : ℝ)^4605 ≤ (39941236390269/100000000000000 : ℝ)^3581 := by
    have hnat : (4898376983 : ℕ)^4605*100000000000000^3581 ≤ 39941236390269^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898376983 10000000000 39941236390269 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1170961429/2000000000 : ℝ)^4605 ≤ (10047591477527/20000000000000 : ℝ)^3581 := by
    have hnat : (1170961429 : ℕ)^4605*20000000000000^3581 ≤ 10047591477527^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170961429 2000000000 10047591477527 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205669723/1250000000 : ℝ), (4898376983/10000000000 : ℝ), (1170961429/2000000000 : ℝ)] ![(9820806204663/100000000000000 : ℝ), (39941236390269/100000000000000 : ℝ), (10047591477527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205669723/1250000000 : ℝ)|^4605 ≤ (9820806204663/100000000000000 : ℝ)^3581
        have hw : |(-205669723/1250000000 : ℝ)|=(205669723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4898376983/10000000000 : ℝ)|^4605 ≤ (39941236390269/100000000000000 : ℝ)^3581
        have hw : |(4898376983/10000000000 : ℝ)|=(4898376983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1170961429/2000000000 : ℝ)|^4605 ≤ (10047591477527/20000000000000 : ℝ)^3581
        have hw : |(1170961429/2000000000 : ℝ)|=(1170961429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s0_5 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193275867/10000000000 : ℝ)*x 0 + (-1222463961/10000000000 : ℝ)*x 1 + (5854806967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193275867/10000000000 : ℝ)^4605 ≤ (21529841201743/50000000000000 : ℝ)^3581 := by
    have hnat : (5193275867 : ℕ)^4605*50000000000000^3581 ≤ 21529841201743^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193275867 10000000000 21529841201743 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1222463961/10000000000 : ℝ)^4605 ≤ (83779526999/1250000000000 : ℝ)^3581 := by
    have hnat : (1222463961 : ℕ)^4605*1250000000000^3581 ≤ 83779526999^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222463961 10000000000 83779526999 1250000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5854806967/10000000000 : ℝ)^4605 ≤ (5023795542353/10000000000000 : ℝ)^3581 := by
    have hnat : (5854806967 : ℕ)^4605*10000000000000^3581 ≤ 5023795542353^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5854806967 10000000000 5023795542353 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193275867/10000000000 : ℝ), (-1222463961/10000000000 : ℝ), (5854806967/10000000000 : ℝ)] ![(21529841201743/50000000000000 : ℝ), (83779526999/1250000000000 : ℝ), (5023795542353/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193275867/10000000000 : ℝ)|^4605 ≤ (21529841201743/50000000000000 : ℝ)^3581
        have hw : |(5193275867/10000000000 : ℝ)|=(5193275867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1222463961/10000000000 : ℝ)|^4605 ≤ (83779526999/1250000000000 : ℝ)^3581
        have hw : |(-1222463961/10000000000 : ℝ)|=(1222463961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5854806967/10000000000 : ℝ)|^4605 ≤ (5023795542353/10000000000000 : ℝ)^3581
        have hw : |(5854806967/10000000000 : ℝ)|=(5854806967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s0_6 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193275643/10000000000 : ℝ)*x 0 + (585480749/1000000000 : ℝ)*x 1 + (-611231741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193275643/10000000000 : ℝ)^4605 ≤ (4305968001511/10000000000000 : ℝ)^3581 := by
    have hnat : (5193275643 : ℕ)^4605*10000000000000^3581 ≤ 4305968001511^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193275643 10000000000 4305968001511 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585480749/1000000000 : ℝ)^4605 ≤ (12559490298617/25000000000000 : ℝ)^3581 := by
    have hnat : (585480749 : ℕ)^4605*25000000000000^3581 ≤ 12559490298617^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585480749 1000000000 12559490298617 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611231741/5000000000 : ℝ)^4605 ≤ (209448711961/3125000000000 : ℝ)^3581 := by
    have hnat : (611231741 : ℕ)^4605*3125000000000^3581 ≤ 209448711961^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611231741 5000000000 209448711961 3125000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193275643/10000000000 : ℝ), (585480749/1000000000 : ℝ), (-611231741/5000000000 : ℝ)] ![(4305968001511/10000000000000 : ℝ), (12559490298617/25000000000000 : ℝ), (209448711961/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193275643/10000000000 : ℝ)|^4605 ≤ (4305968001511/10000000000000 : ℝ)^3581
        have hw : |(5193275643/10000000000 : ℝ)|=(5193275643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(585480749/1000000000 : ℝ)|^4605 ≤ (12559490298617/25000000000000 : ℝ)^3581
        have hw : |(585480749/1000000000 : ℝ)|=(585480749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-611231741/5000000000 : ℝ)|^4605 ≤ (209448711961/3125000000000 : ℝ)^3581
        have hw : |(-611231741/5000000000 : ℝ)|=(611231741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s0_7 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4141420517/10000000000 : ℝ)*x 0 + (336696883/625000000 : ℝ)*x 1 + (3154025129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4141420517/10000000000 : ℝ)^4605 ≤ (32186354228519/100000000000000 : ℝ)^3581 := by
    have hnat : (4141420517 : ℕ)^4605*100000000000000^3581 ≤ 32186354228519^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141420517 10000000000 32186354228519 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336696883/625000000 : ℝ)^4605 ≤ (45137783387471/100000000000000 : ℝ)^3581 := by
    have hnat : (336696883 : ℕ)^4605*100000000000000^3581 ≤ 45137783387471^3581*625000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336696883 625000000 45137783387471 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154025129/10000000000 : ℝ)^4605 ≤ (22675862364851/100000000000000 : ℝ)^3581 := by
    have hnat : (3154025129 : ℕ)^4605*100000000000000^3581 ≤ 22675862364851^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154025129 10000000000 22675862364851 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4141420517/10000000000 : ℝ), (336696883/625000000 : ℝ), (3154025129/10000000000 : ℝ)] ![(32186354228519/100000000000000 : ℝ), (45137783387471/100000000000000 : ℝ), (22675862364851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4141420517/10000000000 : ℝ)|^4605 ≤ (32186354228519/100000000000000 : ℝ)^3581
        have hw : |(4141420517/10000000000 : ℝ)|=(4141420517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336696883/625000000 : ℝ)|^4605 ≤ (45137783387471/100000000000000 : ℝ)^3581
        have hw : |(336696883/625000000 : ℝ)|=(336696883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154025129/10000000000 : ℝ)|^4605 ≤ (22675862364851/100000000000000 : ℝ)^3581
        have hw : |(3154025129/10000000000 : ℝ)|=(3154025129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1554_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3353/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3119/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4603/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4603 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4603*1^1024 ≤ 0^1024*1^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4603/1024 : ℝ) ≤ (1626346305390590671/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4603 ≤ (1626346305390590671/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4603*100000000000000000000^1024 ≤ 1626346305390590671^1024*5^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1626346305390590671 100000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1626346305390590671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4603 := by
      have hnat : (1 : ℕ)^1024*1^4603 ≤ 1^4603*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101626346305390590671/100000000000000000000 : ℝ) ≤ (2508988427298909/2500000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (101626346305390590671/100000000000000000000 : ℝ)^1024 ≤ (2508988427298909/2500000000000000 : ℝ)^4603 := by
      have hnat : (101626346305390590671 : ℕ)^1024*2500000000000000^4603 ≤ 2508988427298909^4603*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101626346305390590671 100000000000000000000 2508988427298909 2500000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508988427298909/2500000000000000 : ℝ)) (X := (101626346305390590671/100000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51626346305390590671/50000000000000000000 : ℝ) ≤ (1258988427298909/1250000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (51626346305390590671/50000000000000000000 : ℝ)^1024 ≤ (1258988427298909/1250000000000000 : ℝ)^4603 := by
      have hnat : (51626346305390590671 : ℕ)^1024*1250000000000000^4603 ≤ 1258988427298909^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51626346305390590671 50000000000000000000 1258988427298909 1250000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1258988427298909/1250000000000000 : ℝ)) (X := (51626346305390590671/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8988427298909/1000000000000000 : ℝ)*(0 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8988427298909/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1626346305390590671/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8988427298909/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4603/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8988427298909/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2508988427298909/2500000000000000 : ℝ) by norm_num, show 1+(1626346305390590671/100000000000000000000 : ℝ)+(0 : ℝ)=(101626346305390590671/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1626346305390590671/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8988427298909/1000000000000000 : ℝ)*(2/5 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8988427298909/1000000000000000 : ℝ)*(2/5 : ℝ)=(1258988427298909/1250000000000000 : ℝ) by norm_num, show 1+2*(1626346305390590671/100000000000000000000 : ℝ)=(51626346305390590671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8988427298909/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8988427298909/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8988427298909/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8988427298909/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8988427298909/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8988427298909/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-32843609/200000000 : ℝ)*X 0 0+(2940607549/5000000000 : ℝ)*X 0 1+(2436437757/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2734450933/5000000000 : ℝ)*X 1 0+(-2204395229/10000000000 : ℝ)*X 1 1+(4872875513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5468901903/10000000000 : ℝ)*X 2 0+(4872875469/10000000000 : ℝ)*X 2 1+(-440879047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4134003089/10000000000 : ℝ)*X 0 0+(3092366669/10000000000 : ℝ)*X 0 1+(2723346343/5000000000 : ℝ)*X 0 2+(4134003089/10000000000 : ℝ)*X 1 0+(3092366669/10000000000 : ℝ)*X 1 1+(2723346343/5000000000 : ℝ)*X 1 2+(4134003089/10000000000 : ℝ)*X 2 0+(3092366669/10000000000 : ℝ)*X 2 1+(2723346343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-205669723/1250000000 : ℝ)*X 0 0+(4898376983/10000000000 : ℝ)*X 0 1+(1170961429/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5193275867/10000000000 : ℝ)*X 1 0+(-1222463961/10000000000 : ℝ)*X 1 1+(5854806967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5193275643/10000000000 : ℝ)*X 2 0+(585480749/1000000000 : ℝ)*X 2 1+(-611231741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4141420517/10000000000 : ℝ)*X 0 0+(336696883/625000000 : ℝ)*X 0 1+(3154025129/10000000000 : ℝ)*X 0 2+(4141420517/10000000000 : ℝ)*X 1 0+(336696883/625000000 : ℝ)*X 1 1+(3154025129/10000000000 : ℝ)*X 1 2+(4141420517/10000000000 : ℝ)*X 2 0+(336696883/625000000 : ℝ)*X 2 1+(3154025129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77439536725785242922447/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15779877/100000000000000 : ℝ)*(base1) + (30871491/10000000000000 : ℝ)*(base19) + (157712247/50000000000000 : ℝ)*(base23) + (19533811/50000000000000 : ℝ)*(upper3) + (3900177/10000000000000 : ℝ)*(upper5) + (708241296950787/100000000000000 : ℝ)*(major0) + (708241296950787/100000000000000 : ℝ)*(major1) + (708241296950787/100000000000000 : ℝ)*(major2) + (123966307161207/12500000000000 : ℝ)*(sp0) + (247932816889153/25000000000000 : ℝ)*(sp1) + (247932815211757/25000000000000 : ℝ)*(sp2) + (424750465781341/100000000000000 : ℝ)*(sp3) + (1134761743/100000000000000 : ℝ)*(sp4) + (60555309/12500000000000 : ℝ)*(sp7) + (424750966003689/100000000000000 : ℝ)*(f.failure) + (495865788135761/50000000000000 : ℝ)*(f.sum) + (102561571258617/50000000000000000000000000000 : ℝ)*base66 + (1142682408408617/100000000000000000000000000000 : ℝ)*base68 + (16606461508617/100000000000000000000000000000 : ℝ)*base70 + (427327524708617/100000000000000000000000000000 : ℝ)*base72 + (381315458058617/50000000000000000000000000000 : ℝ)*base74 + (219483034791383/100000000000000000000000000000 : ℝ)*base75 + (446693153908617/100000000000000000000000000000 : ℝ)*base78 + (220299255908617/100000000000000000000000000000 : ℝ)*base80 + (21585350091383/50000000000000000000000000000 : ℝ)*base81 + (17469831/2500000000000000000000 : ℝ)*base89 + (17469831/2500000000000000000000 : ℝ)*base91 + (17469831/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (481043630901953881542963/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (270735967/12500000000000 : ℝ)*(base19) + (429986211/20000000000000 : ℝ)*(base23) + (50459/5000000000000 : ℝ)*(base32) + (157503337/50000000000000 : ℝ)*(upper3) + (147812711/50000000000000 : ℝ)*(upper5) + (746678925014469/100000000000000 : ℝ)*(major0) + (746678925014469/100000000000000 : ℝ)*(major1) + (746678925014469/100000000000000 : ℝ)*(major2) + (5745663087/100000000000000 : ℝ)*(sp1) + (6294720993/100000000000000 : ℝ)*(sp2) + (1045554505053259/100000000000000 : ℝ)*(sp4) + (1045546593502437/100000000000000 : ℝ)*(sp5) + (261386515100303/25000000000000 : ℝ)*(sp6) + (89560604654147/20000000000000 : ℝ)*(sp7) + (223901512139957/50000000000000 : ℝ)*(f.failure) + (1045554505053259/100000000000000 : ℝ)*(f.sum) + (87875184035679/50000000000000000000000000000 : ℝ)*base66 + (131516754785679/100000000000000000000000000000 : ℝ)*base68 + (943443875914321/100000000000000000000000000000 : ℝ)*base69 + (256060408685679/100000000000000000000000000000 : ℝ)*base72 + (151228547085679/50000000000000000000000000000 : ℝ)*base74 + (116380710414321/100000000000000000000000000000 : ℝ)*base75 + (185977513914321/100000000000000000000000000000 : ℝ)*base77 + (965212854785679/100000000000000000000000000000 : ℝ)*base80 + (109442849114321/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11924197/1250000000000000000000 : ℝ)*base90 + (11924197/1250000000000000000000 : ℝ)*base92 + (11924197/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1554_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3119/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1554_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1554_s1_0 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1784858563/10000000000 : ℝ)*x 0 + (693015403/1250000000 : ℝ)*x 1 + (1023616201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784858563/10000000000 : ℝ)^4605 ≤ (5452142431601/50000000000000 : ℝ)^3581 := by
    have hnat : (1784858563 : ℕ)^4605*50000000000000^3581 ≤ 5452142431601^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784858563 10000000000 5452142431601 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693015403/1250000000 : ℝ)^4605 ≤ (11709031111059/25000000000000 : ℝ)^3581 := by
    have hnat : (693015403 : ℕ)^4605*25000000000000^3581 ≤ 11709031111059^3581*1250000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693015403 1250000000 11709031111059 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023616201/2000000000 : ℝ)^4605 ≤ (8451918136493/20000000000000 : ℝ)^3581 := by
    have hnat : (1023616201 : ℕ)^4605*20000000000000^3581 ≤ 8451918136493^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023616201 2000000000 8451918136493 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1784858563/10000000000 : ℝ), (693015403/1250000000 : ℝ), (1023616201/2000000000 : ℝ)] ![(5452142431601/50000000000000 : ℝ), (11709031111059/25000000000000 : ℝ), (8451918136493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1784858563/10000000000 : ℝ)|^4605 ≤ (5452142431601/50000000000000 : ℝ)^3581
        have hw : |(-1784858563/10000000000 : ℝ)|=(1784858563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(693015403/1250000000 : ℝ)|^4605 ≤ (11709031111059/25000000000000 : ℝ)^3581
        have hw : |(693015403/1250000000 : ℝ)|=(693015403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023616201/2000000000 : ℝ)|^4605 ≤ (8451918136493/20000000000000 : ℝ)^3581
        have hw : |(1023616201/2000000000 : ℝ)|=(1023616201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s1_1 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537917263/1000000000 : ℝ)*x 0 + (-1004046897/5000000000 : ℝ)*x 1 + (319880047/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537917263/1000000000 : ℝ)^4605 ≤ (22525923096289/50000000000000 : ℝ)^3581 := by
    have hnat : (537917263 : ℕ)^4605*50000000000000^3581 ≤ 22525923096289^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537917263 1000000000 22525923096289 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004046897/5000000000 : ℝ)^4605 ≤ (3172141450341/25000000000000 : ℝ)^3581 := by
    have hnat : (1004046897 : ℕ)^4605*25000000000000^3581 ≤ 3172141450341^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004046897 5000000000 3172141450341 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319880047/625000000 : ℝ)^4605 ≤ (42259587996107/100000000000000 : ℝ)^3581 := by
    have hnat : (319880047 : ℕ)^4605*100000000000000^3581 ≤ 42259587996107^3581*625000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319880047 625000000 42259587996107 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537917263/1000000000 : ℝ), (-1004046897/5000000000 : ℝ), (319880047/625000000 : ℝ)] ![(22525923096289/50000000000000 : ℝ), (3172141450341/25000000000000 : ℝ), (42259587996107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537917263/1000000000 : ℝ)|^4605 ≤ (22525923096289/50000000000000 : ℝ)^3581
        have hw : |(537917263/1000000000 : ℝ)|=(537917263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1004046897/5000000000 : ℝ)|^4605 ≤ (3172141450341/25000000000000 : ℝ)^3581
        have hw : |(-1004046897/5000000000 : ℝ)|=(1004046897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319880047/625000000 : ℝ)|^4605 ≤ (42259587996107/100000000000000 : ℝ)^3581
        have hw : |(319880047/625000000 : ℝ)|=(319880047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s1_2 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379172617/10000000000 : ℝ)*x 0 + (511808079/1000000000 : ℝ)*x 1 + (-1004046881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379172617/10000000000 : ℝ)^4605 ≤ (22525923026283/50000000000000 : ℝ)^3581 := by
    have hnat : (5379172617 : ℕ)^4605*50000000000000^3581 ≤ 22525923026283^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379172617 10000000000 22525923026283 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511808079/1000000000 : ℝ)^4605 ≤ (42259588399591/100000000000000 : ℝ)^3581 := by
    have hnat : (511808079 : ℕ)^4605*100000000000000^3581 ≤ 42259588399591^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511808079 1000000000 42259588399591 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004046881/5000000000 : ℝ)^4605 ≤ (6344282770673/50000000000000 : ℝ)^3581 := by
    have hnat : (1004046881 : ℕ)^4605*50000000000000^3581 ≤ 6344282770673^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004046881 5000000000 6344282770673 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379172617/10000000000 : ℝ), (511808079/1000000000 : ℝ), (-1004046881/5000000000 : ℝ)] ![(22525923026283/50000000000000 : ℝ), (42259588399591/100000000000000 : ℝ), (6344282770673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379172617/10000000000 : ℝ)|^4605 ≤ (22525923026283/50000000000000 : ℝ)^3581
        have hw : |(5379172617/10000000000 : ℝ)|=(5379172617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(511808079/1000000000 : ℝ)|^4605 ≤ (42259588399591/100000000000000 : ℝ)^3581
        have hw : |(511808079/1000000000 : ℝ)|=(511808079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004046881/5000000000 : ℝ)|^4605 ≤ (6344282770673/50000000000000 : ℝ)^3581
        have hw : |(-1004046881/5000000000 : ℝ)|=(1004046881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s1_3 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4234286753/10000000000 : ℝ)*x 0 + (940190353/2500000000 : ℝ)*x 1 + (4755507823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234286753/10000000000 : ℝ)^4605 ≤ (33117437299357/100000000000000 : ℝ)^3581 := by
    have hnat : (4234286753 : ℕ)^4605*100000000000000^3581 ≤ 33117437299357^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234286753 10000000000 33117437299357 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940190353/2500000000 : ℝ)^4605 ≤ (28433108619381/100000000000000 : ℝ)^3581 := by
    have hnat : (940190353 : ℕ)^4605*100000000000000^3581 ≤ 28433108619381^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940190353 2500000000 28433108619381 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4755507823/10000000000 : ℝ)^4605 ≤ (7689890813379/20000000000000 : ℝ)^3581 := by
    have hnat : (4755507823 : ℕ)^4605*20000000000000^3581 ≤ 7689890813379^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4755507823 10000000000 7689890813379 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234286753/10000000000 : ℝ), (940190353/2500000000 : ℝ), (4755507823/10000000000 : ℝ)] ![(33117437299357/100000000000000 : ℝ), (28433108619381/100000000000000 : ℝ), (7689890813379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234286753/10000000000 : ℝ)|^4605 ≤ (33117437299357/100000000000000 : ℝ)^3581
        have hw : |(4234286753/10000000000 : ℝ)|=(4234286753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(940190353/2500000000 : ℝ)|^4605 ≤ (28433108619381/100000000000000 : ℝ)^3581
        have hw : |(940190353/2500000000 : ℝ)|=(940190353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4755507823/10000000000 : ℝ)|^4605 ≤ (7689890813379/20000000000000 : ℝ)^3581
        have hw : |(4755507823/10000000000 : ℝ)|=(4755507823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s1_4 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-89254571/500000000 : ℝ)*x 0 + (5122573169/10000000000 : ℝ)*x 1 + (5539563117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89254571/500000000 : ℝ)^4605 ≤ (10906114294453/100000000000000 : ℝ)^3581 := by
    have hnat : (89254571 : ℕ)^4605*100000000000000^3581 ≤ 10906114294453^3581*500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89254571 500000000 10906114294453 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5122573169/10000000000 : ℝ)^4605 ≤ (42307294543701/100000000000000 : ℝ)^3581 := by
    have hnat : (5122573169 : ℕ)^4605*100000000000000^3581 ≤ 42307294543701^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5122573169 10000000000 42307294543701 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5539563117/10000000000 : ℝ)^4605 ≤ (4678659113567/10000000000000 : ℝ)^3581 := by
    have hnat : (5539563117 : ℕ)^4605*10000000000000^3581 ≤ 4678659113567^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539563117 10000000000 4678659113567 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-89254571/500000000 : ℝ), (5122573169/10000000000 : ℝ), (5539563117/10000000000 : ℝ)] ![(10906114294453/100000000000000 : ℝ), (42307294543701/100000000000000 : ℝ), (4678659113567/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-89254571/500000000 : ℝ)|^4605 ≤ (10906114294453/100000000000000 : ℝ)^3581
        have hw : |(-89254571/500000000 : ℝ)|=(89254571/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5122573169/10000000000 : ℝ)|^4605 ≤ (42307294543701/100000000000000 : ℝ)^3581
        have hw : |(5122573169/10000000000 : ℝ)|=(5122573169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5539563117/10000000000 : ℝ)|^4605 ≤ (4678659113567/10000000000000 : ℝ)^3581
        have hw : |(5539563117/10000000000 : ℝ)|=(5539563117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s1_5 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266424521/10000000000 : ℝ)*x 0 + (-317322707/2000000000 : ℝ)*x 1 + (5539562247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266424521/10000000000 : ℝ)^4605 ≤ (21920593831059/50000000000000 : ℝ)^3581 := by
    have hnat : (5266424521 : ℕ)^4605*50000000000000^3581 ≤ 21920593831059^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266424521 10000000000 21920593831059 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317322707/2000000000 : ℝ)^4605 ≤ (4686115323473/50000000000000 : ℝ)^3581 := by
    have hnat : (317322707 : ℕ)^4605*50000000000000^3581 ≤ 4686115323473^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317322707 2000000000 4686115323473 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5539562247/10000000000 : ℝ)^4605 ≤ (4678658168657/10000000000000 : ℝ)^3581 := by
    have hnat : (5539562247 : ℕ)^4605*10000000000000^3581 ≤ 4678658168657^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539562247 10000000000 4678658168657 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266424521/10000000000 : ℝ), (-317322707/2000000000 : ℝ), (5539562247/10000000000 : ℝ)] ![(21920593831059/50000000000000 : ℝ), (4686115323473/50000000000000 : ℝ), (4678658168657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266424521/10000000000 : ℝ)|^4605 ≤ (21920593831059/50000000000000 : ℝ)^3581
        have hw : |(5266424521/10000000000 : ℝ)|=(5266424521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-317322707/2000000000 : ℝ)|^4605 ≤ (4686115323473/50000000000000 : ℝ)^3581
        have hw : |(-317322707/2000000000 : ℝ)|=(317322707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5539562247/10000000000 : ℝ)|^4605 ≤ (4678658168657/10000000000000 : ℝ)^3581
        have hw : |(5539562247/10000000000 : ℝ)|=(5539562247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s1_6 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263321317/500000000 : ℝ)*x 0 + (5539561739/10000000000 : ℝ)*x 1 + (-99163231/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263321317/500000000 : ℝ)^4605 ≤ (21920603567371/50000000000000 : ℝ)^3581 := by
    have hnat : (263321317 : ℕ)^4605*50000000000000^3581 ≤ 21920603567371^3581*500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263321317 500000000 21920603567371 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5539561739/10000000000 : ℝ)^4605 ≤ (9357315233833/20000000000000 : ℝ)^3581 := by
    have hnat : (5539561739 : ℕ)^4605*20000000000000^3581 ≤ 9357315233833^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539561739 10000000000 9357315233833 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99163231/625000000 : ℝ)^4605 ≤ (9372216677513/100000000000000 : ℝ)^3581 := by
    have hnat : (99163231 : ℕ)^4605*100000000000000^3581 ≤ 9372216677513^3581*625000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99163231 625000000 9372216677513 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263321317/500000000 : ℝ), (5539561739/10000000000 : ℝ), (-99163231/625000000 : ℝ)] ![(21920603567371/50000000000000 : ℝ), (9357315233833/20000000000000 : ℝ), (9372216677513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263321317/500000000 : ℝ)|^4605 ≤ (21920603567371/50000000000000 : ℝ)^3581
        have hw : |(263321317/500000000 : ℝ)|=(263321317/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5539561739/10000000000 : ℝ)|^4605 ≤ (9357315233833/20000000000000 : ℝ)^3581
        have hw : |(5539561739/10000000000 : ℝ)|=(5539561739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99163231/625000000 : ℝ)|^4605 ≤ (9372216677513/100000000000000 : ℝ)^3581
        have hw : |(-99163231/625000000 : ℝ)|=(99163231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s1_7 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4234831021/10000000000 : ℝ)*x 0 + (4745017323/10000000000 : ℝ)*x 1 + (377140917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234831021/10000000000 : ℝ)^4605 ≤ (33122911523207/100000000000000 : ℝ)^3581 := by
    have hnat : (4234831021 : ℕ)^4605*100000000000000^3581 ≤ 33122911523207^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234831021 10000000000 33122911523207 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4745017323/10000000000 : ℝ)^4605 ≤ (9585104027341/25000000000000 : ℝ)^3581 := by
    have hnat : (4745017323 : ℕ)^4605*25000000000000^3581 ≤ 9585104027341^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4745017323 10000000000 9585104027341 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377140917/1000000000 : ℝ)^4605 ≤ (1426833617653/5000000000000 : ℝ)^3581 := by
    have hnat : (377140917 : ℕ)^4605*5000000000000^3581 ≤ 1426833617653^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377140917 1000000000 1426833617653 5000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234831021/10000000000 : ℝ), (4745017323/10000000000 : ℝ), (377140917/1000000000 : ℝ)] ![(33122911523207/100000000000000 : ℝ), (9585104027341/25000000000000 : ℝ), (1426833617653/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234831021/10000000000 : ℝ)|^4605 ≤ (33122911523207/100000000000000 : ℝ)^3581
        have hw : |(4234831021/10000000000 : ℝ)|=(4234831021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4745017323/10000000000 : ℝ)|^4605 ≤ (9585104027341/25000000000000 : ℝ)^3581
        have hw : |(4745017323/10000000000 : ℝ)|=(4745017323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377140917/1000000000 : ℝ)|^4605 ≤ (1426833617653/5000000000000 : ℝ)^3581
        have hw : |(377140917/1000000000 : ℝ)|=(377140917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1554_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3119/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1777/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3581/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3119/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3119/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3119/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3119/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3119/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3119/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3353/100000 : ℝ) ^ (4603/1024 : ℝ) ≤ (23531576400307/100000000000000000000 : ℝ) := by
    have hpowers : (3353/100000 : ℝ)^4603 ≤ (23531576400307/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3353 : ℕ)^4603*100000000000000000000^1024 ≤ 23531576400307^1024*100000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3353 100000 23531576400307 100000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3353/100000 : ℝ)) (X := (23531576400307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3119/12500 : ℝ) ^ (4603/1024 : ℝ) ≤ (6092113291008331/3125000000000000000 : ℝ) := by
    have hpowers : (3119/12500 : ℝ)^4603 ≤ (6092113291008331/3125000000000000000 : ℝ)^1024 := by
      have hnat : (3119 : ℕ)^4603*3125000000000000000^1024 ≤ 6092113291008331^1024*12500^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3119 12500 6092113291008331 3125000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3119/12500 : ℝ)) (X := (6092113291008331/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000023531576400307/50000000000000000000 : ℝ) ≤ (10000001046983699/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (50000023531576400307/50000000000000000000 : ℝ)^1024 ≤ (10000001046983699/10000000000000000 : ℝ)^4603 := by
      have hnat : (50000023531576400307 : ℕ)^1024*10000000000000000^4603 ≤ 10000001046983699^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000023531576400307 50000000000000000000 10000001046983699 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001046983699/10000000000000000 : ℝ)) (X := (50000023531576400307/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100194971156888666899/100000000000000000000 : ℝ) ≤ (5002167057430093/5000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (100194971156888666899/100000000000000000000 : ℝ)^1024 ≤ (5002167057430093/5000000000000000 : ℝ)^4603 := by
      have hnat : (100194971156888666899 : ℕ)^1024*5000000000000000^4603 ≤ 5002167057430093^4603*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100194971156888666899 100000000000000000000 5002167057430093 5000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002167057430093/5000000000000000 : ℝ)) (X := (100194971156888666899/100000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1568592113291008331/1562500000000000000 : ℝ) ≤ (10008667182736673/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (1568592113291008331/1562500000000000000 : ℝ)^1024 ≤ (10008667182736673/10000000000000000 : ℝ)^4603 := by
      have hnat : (1568592113291008331 : ℕ)^1024*10000000000000000^4603 ≤ 10008667182736673^4603*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1568592113291008331 1562500000000000000 10008667182736673 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008667182736673/10000000000000000 : ℝ)) (X := (1568592113291008331/1562500000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23531576400307/100000000000000000000 : ℝ) ≤ ((215960965060621192879/215990000000000000000 : ℝ)+2*(4333067876487/2159900000000000 : ℝ)*(3353/100000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (215960965060621192879/215990000000000000000 : ℝ)+2*(4333067876487/2159900000000000 : ℝ)*(3353/100000 : ℝ)=(10000001046983699/10000000000000000 : ℝ) by norm_num, show 1+2*(23531576400307/100000000000000000000 : ℝ)=(50000023531576400307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6092113291008331/3125000000000000000 : ℝ)+(23531576400307/100000000000000000000 : ℝ) ≤ ((215960965060621192879/215990000000000000000 : ℝ)+(4333067876487/2159900000000000 : ℝ)*((3119/12500 : ℝ)+(3353/100000 : ℝ)))^(4603/1024 : ℝ) := by
    rw [show (215960965060621192879/215990000000000000000 : ℝ)+(4333067876487/2159900000000000 : ℝ)*((3119/12500 : ℝ)+(3353/100000 : ℝ))=(5002167057430093/5000000000000000 : ℝ) by norm_num, show 1+(6092113291008331/3125000000000000000 : ℝ)+(23531576400307/100000000000000000000 : ℝ)=(100194971156888666899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6092113291008331/3125000000000000000 : ℝ) ≤ ((215960965060621192879/215990000000000000000 : ℝ)+2*(4333067876487/2159900000000000 : ℝ)*(3119/12500 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (215960965060621192879/215990000000000000000 : ℝ)+2*(4333067876487/2159900000000000 : ℝ)*(3119/12500 : ℝ)=(10008667182736673/10000000000000000 : ℝ) by norm_num, show 1+2*(6092113291008331/3125000000000000000 : ℝ)=(1568592113291008331/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (215960965060621192879/215990000000000000000 : ℝ)*(X 1 0+X 2 0)+(4333067876487/2159900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (3353/100000 : ℝ)) (hi := (3119/12500 : ℝ)) (c := (215960965060621192879/215990000000000000000 : ℝ)) (alpha := (4333067876487/2159900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (215960965060621192879/215990000000000000000 : ℝ)*(X 0 1+X 2 1)+(4333067876487/2159900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (3353/100000 : ℝ)) (hi := (3119/12500 : ℝ)) (c := (215960965060621192879/215990000000000000000 : ℝ)) (alpha := (4333067876487/2159900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (215960965060621192879/215990000000000000000 : ℝ)*(X 0 2+X 1 2)+(4333067876487/2159900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (3353/100000 : ℝ)) (hi := (3119/12500 : ℝ)) (c := (215960965060621192879/215990000000000000000 : ℝ)) (alpha := (4333067876487/2159900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1784858563/10000000000 : ℝ)*X 0 0+(693015403/1250000000 : ℝ)*X 0 1+(1023616201/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537917263/1000000000 : ℝ)*X 1 0+(-1004046897/5000000000 : ℝ)*X 1 1+(319880047/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5379172617/10000000000 : ℝ)*X 2 0+(511808079/1000000000 : ℝ)*X 2 1+(-1004046881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4234286753/10000000000 : ℝ)*X 0 0+(940190353/2500000000 : ℝ)*X 0 1+(4755507823/10000000000 : ℝ)*X 0 2+(4234286753/10000000000 : ℝ)*X 1 0+(940190353/2500000000 : ℝ)*X 1 1+(4755507823/10000000000 : ℝ)*X 1 2+(4234286753/10000000000 : ℝ)*X 2 0+(940190353/2500000000 : ℝ)*X 2 1+(4755507823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-89254571/500000000 : ℝ)*X 0 0+(5122573169/10000000000 : ℝ)*X 0 1+(5539563117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266424521/10000000000 : ℝ)*X 1 0+(-317322707/2000000000 : ℝ)*X 1 1+(5539562247/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263321317/500000000 : ℝ)*X 2 0+(5539561739/10000000000 : ℝ)*X 2 1+(-99163231/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4234831021/10000000000 : ℝ)*X 0 0+(4745017323/10000000000 : ℝ)*X 0 1+(377140917/1000000000 : ℝ)*X 0 2+(4234831021/10000000000 : ℝ)*X 1 0+(4745017323/10000000000 : ℝ)*X 1 1+(377140917/1000000000 : ℝ)*X 1 2+(4234831021/10000000000 : ℝ)*X 2 0+(4745017323/10000000000 : ℝ)*X 2 1+(377140917/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16323222845721607672117391991/2159900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1113309/1250000000000 : ℝ)*(base1) + (26583611/2500000000000 : ℝ)*(base19) + (10576719/1000000000000 : ℝ)*(base23) + (57106281/50000000000000 : ℝ)*(upper3) + (3272447/2500000000000 : ℝ)*(upper5) + (335248644191281/20000000000000 : ℝ)*(major0) + (335248644191281/20000000000000 : ℝ)*(major1) + (335248644191281/20000000000000 : ℝ)*(major2) + (586797984705459/25000000000000 : ℝ)*(sp0) + (73349934456889/3125000000000 : ℝ)*(sp1) + (586799477073247/25000000000000 : ℝ)*(sp2) + (251321064054823/25000000000000 : ℝ)*(sp3) + (1779051943/25000000000000 : ℝ)*(sp4) + (575750131/20000000000000 : ℝ)*(sp7) + (201057444806933/20000000000000 : ℝ)*(f.failure) + (293399870745611/12500000000000 : ℝ)*(f.sum) + (2374937349723/2159900000000000000000000000 : ℝ)*base66 + (45645374847744012001/4319800000000000000000000000000000 : ℝ)*base68 + (15660142215310212001/4319800000000000000000000000000000 : ℝ)*base70 + (38649459914090012001/4319800000000000000000000000000000 : ℝ)*base72 + (29283958606049/5399750000000000000000000000 : ℝ)*base74 + (5636678699471812001/4319800000000000000000000000000000 : ℝ)*base76 + (34773611617738812001/4319800000000000000000000000000000 : ℝ)*base78 + (34984591349546412001/4319800000000000000000000000000000 : ℝ)*base80 + (67005195899343/21599000000000000000000000000 : ℝ)*base82 + (1012507/500000000000000000000 : ℝ)*base89 + (1012507/500000000000000000000 : ℝ)*base91 + (1012507/500000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26077029673159181955250529967/2699875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74146237/6250000000000 : ℝ)*(base19) + (249504411/10000000000000 : ℝ)*(base23) + (85646933/50000000000000 : ℝ)*(upper3) + (125972141/100000000000000 : ℝ)*(lower4) + (189995863/50000000000000 : ℝ)*(upper5) + (428156484949303/25000000000000 : ℝ)*(major0) + (428156484949303/25000000000000 : ℝ)*(major1) + (428156484949303/25000000000000 : ℝ)*(major2) + (885133929/25000000000000 : ℝ)*(sp1) + (7403522553/50000000000000 : ℝ)*(sp2) + (119907232926609/5000000000000 : ℝ)*(sp4) + (74941872864271/3125000000000 : ℝ)*(sp5) + (599531839110741/25000000000000 : ℝ)*(sp6) + (1027106899108691/100000000000000 : ℝ)*(sp7) + (1027106899108691/100000000000000 : ℝ)*(f.failure) + (119907232926609/5000000000000 : ℝ)*(f.sum) + (428303483394201/107995000000000000000000000000 : ℝ)*base66 + (44824202004508963337/5399750000000000000000000000000000 : ℝ)*base67 + (44235257119938213337/5399750000000000000000000000000000 : ℝ)*base69 + (30172098688031463337/5399750000000000000000000000000000 : ℝ)*base71 + (115338566963089/107995000000000000000000000000 : ℝ)*base73 + (63029652046377213337/5399750000000000000000000000000000 : ℝ)*base75 + (48652057456773963337/5399750000000000000000000000000000 : ℝ)*base77 + (44817777835537963337/5399750000000000000000000000000000 : ℝ)*base79 + (11128374663007/53997500000000000000000000000 : ℝ)*base81 + (20863811/2500000000000000000000 : ℝ)*base90 + (20863811/2500000000000000000000 : ℝ)*base92 + (20863811/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1554_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3119/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3581/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1554_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1554_s2_0 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360989811/2000000000 : ℝ)*x 0 + (1089122283/2000000000 : ℝ)*x 1 + (2601761009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360989811/2000000000 : ℝ)^4605 ≤ (2765593841413/25000000000000 : ℝ)^3581 := by
    have hnat : (360989811 : ℕ)^4605*25000000000000^3581 ≤ 2765593841413^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360989811 2000000000 2765593841413 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089122283/2000000000 : ℝ)^4605 ≤ (45768662903827/100000000000000 : ℝ)^3581 := by
    have hnat : (1089122283 : ℕ)^4605*100000000000000^3581 ≤ 45768662903827^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089122283 2000000000 45768662903827 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601761009/5000000000 : ℝ)^4605 ≤ (43168961709759/100000000000000 : ℝ)^3581 := by
    have hnat : (2601761009 : ℕ)^4605*100000000000000^3581 ≤ 43168961709759^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601761009 5000000000 43168961709759 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360989811/2000000000 : ℝ), (1089122283/2000000000 : ℝ), (2601761009/5000000000 : ℝ)] ![(2765593841413/25000000000000 : ℝ), (45768662903827/100000000000000 : ℝ), (43168961709759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360989811/2000000000 : ℝ)|^4605 ≤ (2765593841413/25000000000000 : ℝ)^3581
        have hw : |(-360989811/2000000000 : ℝ)|=(360989811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089122283/2000000000 : ℝ)|^4605 ≤ (45768662903827/100000000000000 : ℝ)^3581
        have hw : |(1089122283/2000000000 : ℝ)|=(1089122283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601761009/5000000000 : ℝ)|^4605 ≤ (43168961709759/100000000000000 : ℝ)^3581
        have hw : |(2601761009/5000000000 : ℝ)|=(2601761009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s2_1 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353835527/10000000000 : ℝ)*x 0 + (-1929293289/10000000000 : ℝ)*x 1 + (5203521977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353835527/10000000000 : ℝ)^4605 ≤ (44779145351719/100000000000000 : ℝ)^3581 := by
    have hnat : (5353835527 : ℕ)^4605*100000000000000^3581 ≤ 44779145351719^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353835527 10000000000 44779145351719 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929293289/10000000000 : ℝ)^4605 ≤ (6025946678111/50000000000000 : ℝ)^3581 := by
    have hnat : (1929293289 : ℕ)^4605*50000000000000^3581 ≤ 6025946678111^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929293289 10000000000 6025946678111 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203521977/10000000000 : ℝ)^4605 ≤ (21584480636177/50000000000000 : ℝ)^3581 := by
    have hnat : (5203521977 : ℕ)^4605*50000000000000^3581 ≤ 21584480636177^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203521977 10000000000 21584480636177 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353835527/10000000000 : ℝ), (-1929293289/10000000000 : ℝ), (5203521977/10000000000 : ℝ)] ![(44779145351719/100000000000000 : ℝ), (6025946678111/50000000000000 : ℝ), (21584480636177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353835527/10000000000 : ℝ)|^4605 ≤ (44779145351719/100000000000000 : ℝ)^3581
        have hw : |(5353835527/10000000000 : ℝ)|=(5353835527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929293289/10000000000 : ℝ)|^4605 ≤ (6025946678111/50000000000000 : ℝ)^3581
        have hw : |(-1929293289/10000000000 : ℝ)|=(1929293289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203521977/10000000000 : ℝ)|^4605 ≤ (21584480636177/50000000000000 : ℝ)^3581
        have hw : |(5203521977/10000000000 : ℝ)|=(5203521977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s2_2 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353836041/10000000000 : ℝ)*x 0 + (1300880311/2500000000 : ℝ)*x 1 + (-964646787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353836041/10000000000 : ℝ)^4605 ≤ (11194787720029/25000000000000 : ℝ)^3581 := by
    have hnat : (5353836041 : ℕ)^4605*25000000000000^3581 ≤ 11194787720029^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353836041 10000000000 11194787720029 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300880311/2500000000 : ℝ)^4605 ≤ (43168953452413/100000000000000 : ℝ)^3581 := by
    have hnat : (1300880311 : ℕ)^4605*100000000000000^3581 ≤ 43168953452413^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300880311 2500000000 43168953452413 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964646787/5000000000 : ℝ)^4605 ≤ (12051895645651/100000000000000 : ℝ)^3581 := by
    have hnat : (964646787 : ℕ)^4605*100000000000000^3581 ≤ 12051895645651^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964646787 5000000000 12051895645651 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353836041/10000000000 : ℝ), (1300880311/2500000000 : ℝ), (-964646787/5000000000 : ℝ)] ![(11194787720029/25000000000000 : ℝ), (43168953452413/100000000000000 : ℝ), (12051895645651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353836041/10000000000 : ℝ)|^4605 ≤ (11194787720029/25000000000000 : ℝ)^3581
        have hw : |(5353836041/10000000000 : ℝ)|=(5353836041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300880311/2500000000 : ℝ)|^4605 ≤ (43168953452413/100000000000000 : ℝ)^3581
        have hw : |(1300880311/2500000000 : ℝ)|=(1300880311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964646787/5000000000 : ℝ)|^4605 ≤ (12051895645651/100000000000000 : ℝ)^3581
        have hw : |(-964646787/5000000000 : ℝ)|=(964646787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s2_3 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849762047/2000000000 : ℝ)*x 0 + (993472811/2500000000 : ℝ)*x 1 + (2269569279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849762047/2000000000 : ℝ)^4605 ≤ (8315895685441/25000000000000 : ℝ)^3581 := by
    have hnat : (849762047 : ℕ)^4605*25000000000000^3581 ≤ 8315895685441^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849762047 2000000000 8315895685441 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993472811/2500000000 : ℝ)^4605 ≤ (15260906439801/50000000000000 : ℝ)^3581 := by
    have hnat : (993472811 : ℕ)^4605*50000000000000^3581 ≤ 15260906439801^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993472811 2500000000 15260906439801 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269569279/5000000000 : ℝ)^4605 ≤ (1810730217873/5000000000000 : ℝ)^3581 := by
    have hnat : (2269569279 : ℕ)^4605*5000000000000^3581 ≤ 1810730217873^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269569279 5000000000 1810730217873 5000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849762047/2000000000 : ℝ), (993472811/2500000000 : ℝ), (2269569279/5000000000 : ℝ)] ![(8315895685441/25000000000000 : ℝ), (15260906439801/50000000000000 : ℝ), (1810730217873/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849762047/2000000000 : ℝ)|^4605 ≤ (8315895685441/25000000000000 : ℝ)^3581
        have hw : |(849762047/2000000000 : ℝ)|=(849762047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993472811/2500000000 : ℝ)|^4605 ≤ (15260906439801/50000000000000 : ℝ)^3581
        have hw : |(993472811/2500000000 : ℝ)|=(993472811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269569279/5000000000 : ℝ)|^4605 ≤ (1810730217873/5000000000000 : ℝ)^3581
        have hw : |(2269569279/5000000000 : ℝ)|=(2269569279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s2_4 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-112811893/625000000 : ℝ)*x 0 + (2602490397/5000000000 : ℝ)*x 1 + (5444141303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112811893/625000000 : ℝ)^4605 ≤ (11062700344511/100000000000000 : ℝ)^3581 := by
    have hnat : (112811893 : ℕ)^4605*100000000000000^3581 ≤ 11062700344511^3581*625000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112811893 625000000 11062700344511 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602490397/5000000000 : ℝ)^4605 ≤ (21592262573809/50000000000000 : ℝ)^3581 := by
    have hnat : (2602490397 : ℕ)^4605*50000000000000^3581 ≤ 21592262573809^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602490397 5000000000 21592262573809 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444141303/10000000000 : ℝ)^4605 ≤ (22876387244893/50000000000000 : ℝ)^3581 := by
    have hnat : (5444141303 : ℕ)^4605*50000000000000^3581 ≤ 22876387244893^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444141303 10000000000 22876387244893 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112811893/625000000 : ℝ), (2602490397/5000000000 : ℝ), (5444141303/10000000000 : ℝ)] ![(11062700344511/100000000000000 : ℝ), (21592262573809/50000000000000 : ℝ), (22876387244893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112811893/625000000 : ℝ)|^4605 ≤ (11062700344511/100000000000000 : ℝ)^3581
        have hw : |(-112811893/625000000 : ℝ)|=(112811893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602490397/5000000000 : ℝ)|^4605 ≤ (21592262573809/50000000000000 : ℝ)^3581
        have hw : |(2602490397/5000000000 : ℝ)|=(2602490397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444141303/10000000000 : ℝ)|^4605 ≤ (22876387244893/50000000000000 : ℝ)^3581
        have hw : |(5444141303/10000000000 : ℝ)|=(5444141303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s2_5 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264495173/500000000 : ℝ)*x 0 + (-844337491/5000000000 : ℝ)*x 1 + (217765643/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264495173/500000000 : ℝ)^4605 ≤ (22046346346277/50000000000000 : ℝ)^3581 := by
    have hnat : (264495173 : ℕ)^4605*50000000000000^3581 ≤ 22046346346277^3581*500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264495173 500000000 22046346346277 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844337491/5000000000 : ℝ)^4605 ≤ (2030907055927/20000000000000 : ℝ)^3581 := by
    have hnat : (844337491 : ℕ)^4605*20000000000000^3581 ≤ 2030907055927^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844337491 5000000000 2030907055927 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217765643/400000000 : ℝ)^4605 ≤ (45752772025743/100000000000000 : ℝ)^3581 := by
    have hnat : (217765643 : ℕ)^4605*100000000000000^3581 ≤ 45752772025743^3581*400000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217765643 400000000 45752772025743 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264495173/500000000 : ℝ), (-844337491/5000000000 : ℝ), (217765643/400000000 : ℝ)] ![(22046346346277/50000000000000 : ℝ), (2030907055927/20000000000000 : ℝ), (45752772025743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264495173/500000000 : ℝ)|^4605 ≤ (22046346346277/50000000000000 : ℝ)^3581
        have hw : |(264495173/500000000 : ℝ)|=(264495173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-844337491/5000000000 : ℝ)|^4605 ≤ (2030907055927/20000000000000 : ℝ)^3581
        have hw : |(-844337491/5000000000 : ℝ)|=(844337491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217765643/400000000 : ℝ)|^4605 ≤ (45752772025743/100000000000000 : ℝ)^3581
        have hw : |(217765643/400000000 : ℝ)|=(217765643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s2_6 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289902453/10000000000 : ℝ)*x 0 + (2722071627/5000000000 : ℝ)*x 1 + (-422168333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289902453/10000000000 : ℝ)^4605 ≤ (11023170474693/25000000000000 : ℝ)^3581 := by
    have hnat : (5289902453 : ℕ)^4605*25000000000000^3581 ≤ 11023170474693^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289902453 10000000000 11023170474693 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722071627/5000000000 : ℝ)^4605 ≤ (22876397787321/50000000000000 : ℝ)^3581 := by
    have hnat : (2722071627 : ℕ)^4605*50000000000000^3581 ≤ 22876397787321^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722071627 5000000000 22876397787321 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422168333/2500000000 : ℝ)^4605 ≤ (5077261260221/50000000000000 : ℝ)^3581 := by
    have hnat : (422168333 : ℕ)^4605*50000000000000^3581 ≤ 5077261260221^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422168333 2500000000 5077261260221 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289902453/10000000000 : ℝ), (2722071627/5000000000 : ℝ), (-422168333/2500000000 : ℝ)] ![(11023170474693/25000000000000 : ℝ), (22876397787321/50000000000000 : ℝ), (5077261260221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289902453/10000000000 : ℝ)|^4605 ≤ (11023170474693/25000000000000 : ℝ)^3581
        have hw : |(5289902453/10000000000 : ℝ)|=(5289902453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722071627/5000000000 : ℝ)|^4605 ≤ (22876397787321/50000000000000 : ℝ)^3581
        have hw : |(2722071627/5000000000 : ℝ)|=(2722071627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422168333/2500000000 : ℝ)|^4605 ≤ (5077261260221/50000000000000 : ℝ)^3581
        have hw : |(-422168333/2500000000 : ℝ)|=(422168333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s2_7 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4248909663/10000000000 : ℝ)*x 0 + (4535731877/10000000000 : ℝ)*x 1 + (3977327821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248909663/10000000000 : ℝ)^4605 ≤ (33264583748869/100000000000000 : ℝ)^3581 := by
    have hnat : (4248909663 : ℕ)^4605*100000000000000^3581 ≤ 33264583748869^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248909663 10000000000 33264583748869 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535731877/10000000000 : ℝ)^4605 ≤ (36179656506597/100000000000000 : ℝ)^3581 := by
    have hnat : (4535731877 : ℕ)^4605*100000000000000^3581 ≤ 36179656506597^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535731877 10000000000 36179656506597 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3977327821/10000000000 : ℝ)^4605 ≤ (30555759725173/100000000000000 : ℝ)^3581 := by
    have hnat : (3977327821 : ℕ)^4605*100000000000000^3581 ≤ 30555759725173^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977327821 10000000000 30555759725173 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248909663/10000000000 : ℝ), (4535731877/10000000000 : ℝ), (3977327821/10000000000 : ℝ)] ![(33264583748869/100000000000000 : ℝ), (36179656506597/100000000000000 : ℝ), (30555759725173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248909663/10000000000 : ℝ)|^4605 ≤ (33264583748869/100000000000000 : ℝ)^3581
        have hw : |(4248909663/10000000000 : ℝ)|=(4248909663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535731877/10000000000 : ℝ)|^4605 ≤ (36179656506597/100000000000000 : ℝ)^3581
        have hw : |(4535731877/10000000000 : ℝ)|=(4535731877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3977327821/10000000000 : ℝ)|^4605 ≤ (30555759725173/100000000000000 : ℝ)^3581
        have hw : |(3977327821/10000000000 : ℝ)|=(3977327821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1554_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3581/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5363/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (991/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3581/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1777/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3581/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1777/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3581/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1777/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3581/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1777/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3581/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1777/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3581/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1777/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (1777/20000 : ℝ) ^ (4603/1024 : ℝ) ≤ (1879714767101981/100000000000000000000 : ℝ) := by
    have hpowers : (1777/20000 : ℝ)^4603 ≤ (1879714767101981/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1777 : ℕ)^4603*100000000000000000000^1024 ≤ 1879714767101981^1024*20000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1777 20000 1879714767101981 100000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1777/20000 : ℝ)) (X := (1879714767101981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3581/20000 : ℝ) ^ (4603/1024 : ℝ) ≤ (43856306196406761/100000000000000000000 : ℝ) := by
    have hpowers : (3581/20000 : ℝ)^4603 ≤ (43856306196406761/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3581 : ℕ)^4603*100000000000000000000^1024 ≤ 43856306196406761^1024*20000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3581 20000 43856306196406761 100000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3581/20000 : ℝ)) (X := (43856306196406761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001879714767101981/50000000000000000000 : ℝ) ≤ (5000041816202257/5000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (50001879714767101981/50000000000000000000 : ℝ)^1024 ≤ (5000041816202257/5000000000000000 : ℝ)^4603 := by
      have hnat : (50001879714767101981 : ℕ)^1024*5000000000000000^4603 ≤ 5000041816202257^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001879714767101981 50000000000000000000 5000041816202257 5000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000041816202257/5000000000000000 : ℝ)) (X := (50001879714767101981/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022868010481754371/50000000000000000000 : ℝ) ≤ (10001017279173597/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (50022868010481754371/50000000000000000000 : ℝ)^1024 ≤ (10001017279173597/10000000000000000 : ℝ)^4603 := by
      have hnat : (50022868010481754371 : ℕ)^1024*10000000000000000^4603 ≤ 10001017279173597^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022868010481754371 50000000000000000000 10001017279173597 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001017279173597/10000000000000000 : ℝ)) (X := (50022868010481754371/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043856306196406761/50000000000000000000 : ℝ) ≤ (250048773148567/250000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (50043856306196406761/50000000000000000000 : ℝ)^1024 ≤ (250048773148567/250000000000000 : ℝ)^4603 := by
      have hnat : (50043856306196406761 : ℕ)^1024*250000000000000^4603 ≤ 250048773148567^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043856306196406761 50000000000000000000 250048773148567 250000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250048773148567/250000000000000 : ℝ)) (X := (50043856306196406761/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1879714767101981/100000000000000000000 : ℝ) ≤ ((9018416346120211137/9020000000000000000 : ℝ)+2*(933646769083/902000000000000 : ℝ)*(1777/20000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (9018416346120211137/9020000000000000000 : ℝ)+2*(933646769083/902000000000000 : ℝ)*(1777/20000 : ℝ)=(5000041816202257/5000000000000000 : ℝ) by norm_num, show 1+2*(1879714767101981/100000000000000000000 : ℝ)=(50001879714767101981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43856306196406761/100000000000000000000 : ℝ)+(1879714767101981/100000000000000000000 : ℝ) ≤ ((9018416346120211137/9020000000000000000 : ℝ)+(933646769083/902000000000000 : ℝ)*((3581/20000 : ℝ)+(1777/20000 : ℝ)))^(4603/1024 : ℝ) := by
    rw [show (9018416346120211137/9020000000000000000 : ℝ)+(933646769083/902000000000000 : ℝ)*((3581/20000 : ℝ)+(1777/20000 : ℝ))=(10001017279173597/10000000000000000 : ℝ) by norm_num, show 1+(43856306196406761/100000000000000000000 : ℝ)+(1879714767101981/100000000000000000000 : ℝ)=(50022868010481754371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43856306196406761/100000000000000000000 : ℝ) ≤ ((9018416346120211137/9020000000000000000 : ℝ)+2*(933646769083/902000000000000 : ℝ)*(3581/20000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (9018416346120211137/9020000000000000000 : ℝ)+2*(933646769083/902000000000000 : ℝ)*(3581/20000 : ℝ)=(250048773148567/250000000000000 : ℝ) by norm_num, show 1+2*(43856306196406761/100000000000000000000 : ℝ)=(50043856306196406761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9018416346120211137/9020000000000000000 : ℝ)*(X 1 0+X 2 0)+(933646769083/902000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (1777/20000 : ℝ)) (hi := (3581/20000 : ℝ)) (c := (9018416346120211137/9020000000000000000 : ℝ)) (alpha := (933646769083/902000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9018416346120211137/9020000000000000000 : ℝ)*(X 0 1+X 2 1)+(933646769083/902000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (1777/20000 : ℝ)) (hi := (3581/20000 : ℝ)) (c := (9018416346120211137/9020000000000000000 : ℝ)) (alpha := (933646769083/902000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9018416346120211137/9020000000000000000 : ℝ)*(X 0 2+X 1 2)+(933646769083/902000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (1777/20000 : ℝ)) (hi := (3581/20000 : ℝ)) (c := (9018416346120211137/9020000000000000000 : ℝ)) (alpha := (933646769083/902000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-360989811/2000000000 : ℝ)*X 0 0+(1089122283/2000000000 : ℝ)*X 0 1+(2601761009/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353835527/10000000000 : ℝ)*X 1 0+(-1929293289/10000000000 : ℝ)*X 1 1+(5203521977/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353836041/10000000000 : ℝ)*X 2 0+(1300880311/2500000000 : ℝ)*X 2 1+(-964646787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((849762047/2000000000 : ℝ)*X 0 0+(993472811/2500000000 : ℝ)*X 0 1+(2269569279/5000000000 : ℝ)*X 0 2+(849762047/2000000000 : ℝ)*X 1 0+(993472811/2500000000 : ℝ)*X 1 1+(2269569279/5000000000 : ℝ)*X 1 2+(849762047/2000000000 : ℝ)*X 2 0+(993472811/2500000000 : ℝ)*X 2 1+(2269569279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-112811893/625000000 : ℝ)*X 0 0+(2602490397/5000000000 : ℝ)*X 0 1+(5444141303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264495173/500000000 : ℝ)*X 1 0+(-844337491/5000000000 : ℝ)*X 1 1+(217765643/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289902453/10000000000 : ℝ)*X 2 0+(2722071627/5000000000 : ℝ)*X 2 1+(-422168333/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4248909663/10000000000 : ℝ)*X 0 0+(4535731877/10000000000 : ℝ)*X 0 1+(3977327821/10000000000 : ℝ)*X 0 2+(4248909663/10000000000 : ℝ)*X 1 0+(4535731877/10000000000 : ℝ)*X 1 1+(3977327821/10000000000 : ℝ)*X 1 2+(4248909663/10000000000 : ℝ)*X 2 0+(4535731877/10000000000 : ℝ)*X 2 1+(3977327821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180996040126577149362531/45100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (531023453/25000000000000 : ℝ)*(base19) + (2088825121/100000000000000 : ℝ)*(base23) + (543531921/100000000000000 : ℝ)*(upper3) + (11560137/5000000000000 : ℝ)*(upper4) + (13209783/25000000000000 : ℝ)*(upper5) + (2949959488764281/100000000000000 : ℝ)*(major0) + (2949959488764281/100000000000000 : ℝ)*(major1) + (2949959488764281/100000000000000 : ℝ)*(major2) + (1032682841563439/25000000000000 : ℝ)*(sp0) + (4130748290879689/100000000000000 : ℝ)*(sp1) + (206537416307419/5000000000000 : ℝ)*(sp2) + (884574707881857/50000000000000 : ℝ)*(sp3) + (148818123/781250000000 : ℝ)*(sp4) + (4753254369/25000000000000 : ℝ)*(sp7) + (176916842878119/10000000000000 : ℝ)*(f.failure) + (4130750414973501/100000000000000 : ℝ)*(f.sum) + (49423101798277/45100000000000000000000000000 : ℝ)*base66 + (7672717796299227497/902000000000000000000000000000000 : ℝ)*base67 + (665308810491227497/902000000000000000000000000000000 : ℝ)*base69 + (258451247674772503/902000000000000000000000000000000 : ℝ)*base72 + (122775056354623/45100000000000000000000000000 : ℝ)*base73 + (8538651130565227497/902000000000000000000000000000000 : ℝ)*base75 + (9735632181928772503/902000000000000000000000000000000 : ℝ)*base78 + (226423849788772503/902000000000000000000000000000000 : ℝ)*base80 + (60109574155523/45100000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2257801/250000000000000000000 : ℝ)*base89 + (2257801/250000000000000000000 : ℝ)*base91 + (2257801/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (556993290503171687193899103/112750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116423801/50000000000000 : ℝ)*(base8) + (118235289/25000000000000 : ℝ)*(base21) + (57845309/100000000000000 : ℝ)*(base29) + (15219461/25000000000000 : ℝ)*(lower2) + (84435499/100000000000000 : ℝ)*(lower4) + (64567883/50000000000000 : ℝ)*(upper5) + (746514475600827/25000000000000 : ℝ)*(major0) + (373257245031077/12500000000000 : ℝ)*(major1) + (373257245031077/12500000000000 : ℝ)*(major2) + (27331355261/100000000000000 : ℝ)*(sp2) + (1045324472438527/25000000000000 : ℝ)*(sp4) + (4181298064756401/100000000000000 : ℝ)*(sp5) + (261329391278749/6250000000000 : ℝ)*(sp6) + (1790817633226399/100000000000000 : ℝ)*(sp7) + (1790817633226399/100000000000000 : ℝ)*(f.failure) + (418129812260171/10000000000000 : ℝ)*(f.sum) + (8841972359337/1025000000000000000000000000 : ℝ)*base65 + (4581894244014959/10250000000000000000000000000000 : ℝ)*base67 + (38783258692985041/10250000000000000000000000000000 : ℝ)*base70 + (493524987196130299/225500000000000000000000000000000 : ℝ)*base71 + (121251124686873/22550000000000000000000000000 : ℝ)*base73 + (522047685963790451/112750000000000000000000000000000 : ℝ)*base76 + (4038462786274630299/225500000000000000000000000000000 : ℝ)*base77 + (117772947551459549/112750000000000000000000000000000 : ℝ)*base79 + (12534551169927/22550000000000000000000000000 : ℝ)*base82 + (21960079/2500000000000000000000 : ℝ)*base90 + (3039921/2500000000000000000000 : ℝ)*base91 + (3039921/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1554_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3581/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (991/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1554_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1554_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (991/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1554_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1554_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1554_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (991/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1554_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

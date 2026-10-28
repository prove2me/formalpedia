-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1202_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:49.327155+00:00
-- url     : https://prove2.me/submissions/261ea96a-2197-4cbd-86d6-7a00d2d48e92

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
theorem support_rectangle_w1202_s0_0 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872965319/10000000000 : ℝ)*x 0 + (3020283029/5000000000 : ℝ)*x 1 + (478801363/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872965319/10000000000 : ℝ)^8395 ≤ (10909261626639/100000000000000 : ℝ)^6347 := by
    have hnat : (1872965319 : ℕ)^8395*100000000000000^6347 ≤ 10909261626639^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872965319 10000000000 10909261626639 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3020283029/5000000000 : ℝ)^8395 ≤ (25668914170487/50000000000000 : ℝ)^6347 := by
    have hnat : (3020283029 : ℕ)^8395*50000000000000^6347 ≤ 25668914170487^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020283029 5000000000 25668914170487 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478801363/1000000000 : ℝ)^8395 ≤ (18876455013949/50000000000000 : ℝ)^6347 := by
    have hnat : (478801363 : ℕ)^8395*50000000000000^6347 ≤ 18876455013949^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478801363 1000000000 18876455013949 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872965319/10000000000 : ℝ), (3020283029/5000000000 : ℝ), (478801363/1000000000 : ℝ)] ![(10909261626639/100000000000000 : ℝ), (25668914170487/50000000000000 : ℝ), (18876455013949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872965319/10000000000 : ℝ)|^8395 ≤ (10909261626639/100000000000000 : ℝ)^6347
        have hw : |(-1872965319/10000000000 : ℝ)|=(1872965319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3020283029/5000000000 : ℝ)|^8395 ≤ (25668914170487/50000000000000 : ℝ)^6347
        have hw : |(3020283029/5000000000 : ℝ)|=(3020283029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478801363/1000000000 : ℝ)|^8395 ≤ (18876455013949/50000000000000 : ℝ)^6347
        have hw : |(478801363/1000000000 : ℝ)|=(478801363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s0_1 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5513412911/10000000000 : ℝ)*x 0 + (-2590114929/10000000000 : ℝ)*x 1 + (4788013603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513412911/10000000000 : ℝ)^8395 ≤ (22748571574797/50000000000000 : ℝ)^6347 := by
    have hnat : (5513412911 : ℕ)^8395*50000000000000^6347 ≤ 22748571574797^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513412911 10000000000 22748571574797 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590114929/10000000000 : ℝ)^8395 ≤ (16749947083859/100000000000000 : ℝ)^6347 := by
    have hnat : (2590114929 : ℕ)^8395*100000000000000^6347 ≤ 16749947083859^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590114929 10000000000 16749947083859 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4788013603/10000000000 : ℝ)^8395 ≤ (4719113718289/12500000000000 : ℝ)^6347 := by
    have hnat : (4788013603 : ℕ)^8395*12500000000000^6347 ≤ 4719113718289^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788013603 10000000000 4719113718289 12500000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513412911/10000000000 : ℝ), (-2590114929/10000000000 : ℝ), (4788013603/10000000000 : ℝ)] ![(22748571574797/50000000000000 : ℝ), (16749947083859/100000000000000 : ℝ), (4719113718289/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513412911/10000000000 : ℝ)|^8395 ≤ (22748571574797/50000000000000 : ℝ)^6347
        have hw : |(5513412911/10000000000 : ℝ)|=(5513412911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2590114929/10000000000 : ℝ)|^8395 ≤ (16749947083859/100000000000000 : ℝ)^6347
        have hw : |(-2590114929/10000000000 : ℝ)|=(2590114929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4788013603/10000000000 : ℝ)|^8395 ≤ (4719113718289/12500000000000 : ℝ)^6347
        have hw : |(4788013603/10000000000 : ℝ)|=(4788013603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s0_2 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5513413179/10000000000 : ℝ)*x 0 + (2394006673/5000000000 : ℝ)*x 1 + (-2590114901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513413179/10000000000 : ℝ)^8395 ≤ (45497146074761/100000000000000 : ℝ)^6347 := by
    have hnat : (5513413179 : ℕ)^8395*100000000000000^6347 ≤ 45497146074761^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513413179 10000000000 45497146074761 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2394006673/5000000000 : ℝ)^8395 ≤ (37752907066031/100000000000000 : ℝ)^6347 := by
    have hnat : (2394006673 : ℕ)^8395*100000000000000^6347 ≤ 37752907066031^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394006673 5000000000 37752907066031 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590114901/10000000000 : ℝ)^8395 ≤ (16749946844359/100000000000000 : ℝ)^6347 := by
    have hnat : (2590114901 : ℕ)^8395*100000000000000^6347 ≤ 16749946844359^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590114901 10000000000 16749946844359 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513413179/10000000000 : ℝ), (2394006673/5000000000 : ℝ), (-2590114901/10000000000 : ℝ)] ![(45497146074761/100000000000000 : ℝ), (37752907066031/100000000000000 : ℝ), (16749946844359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513413179/10000000000 : ℝ)|^8395 ≤ (45497146074761/100000000000000 : ℝ)^6347
        have hw : |(5513413179/10000000000 : ℝ)|=(5513413179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2394006673/5000000000 : ℝ)|^8395 ≤ (37752907066031/100000000000000 : ℝ)^6347
        have hw : |(2394006673/5000000000 : ℝ)|=(2394006673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2590114901/10000000000 : ℝ)|^8395 ≤ (16749946844359/100000000000000 : ℝ)^6347
        have hw : |(-2590114901/10000000000 : ℝ)|=(2590114901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s0_3 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1049045341/2500000000 : ℝ)*x 0 + (3118460633/10000000000 : ℝ)*x 1 + (5639741881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049045341/2500000000 : ℝ)^8395 ≤ (31707341410631/100000000000000 : ℝ)^6347 := by
    have hnat : (1049045341 : ℕ)^8395*100000000000000^6347 ≤ 31707341410631^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049045341 2500000000 31707341410631 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118460633/10000000000 : ℝ)^8395 ≤ (1070579440059/5000000000000 : ℝ)^6347 := by
    have hnat : (3118460633 : ℕ)^8395*5000000000000^6347 ≤ 1070579440059^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118460633 10000000000 1070579440059 5000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5639741881/10000000000 : ℝ)^8395 ≤ (1465033430449/3125000000000 : ℝ)^6347 := by
    have hnat : (5639741881 : ℕ)^8395*3125000000000^6347 ≤ 1465033430449^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639741881 10000000000 1465033430449 3125000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049045341/2500000000 : ℝ), (3118460633/10000000000 : ℝ), (5639741881/10000000000 : ℝ)] ![(31707341410631/100000000000000 : ℝ), (1070579440059/5000000000000 : ℝ), (1465033430449/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049045341/2500000000 : ℝ)|^8395 ≤ (31707341410631/100000000000000 : ℝ)^6347
        have hw : |(1049045341/2500000000 : ℝ)|=(1049045341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118460633/10000000000 : ℝ)|^8395 ≤ (1070579440059/5000000000000 : ℝ)^6347
        have hw : |(3118460633/10000000000 : ℝ)|=(3118460633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5639741881/10000000000 : ℝ)|^8395 ≤ (1465033430449/3125000000000 : ℝ)^6347
        have hw : |(5639741881/10000000000 : ℝ)|=(5639741881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s0_4 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-469484213/2500000000 : ℝ)*x 0 + (4820294349/10000000000 : ℝ)*x 1 + (375446643/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469484213/2500000000 : ℝ)^8395 ≤ (437903153833/4000000000000 : ℝ)^6347 := by
    have hnat : (469484213 : ℕ)^8395*4000000000000^6347 ≤ 437903153833^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469484213 2500000000 437903153833 4000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4820294349/10000000000 : ℝ)^8395 ≤ (38089934841127/100000000000000 : ℝ)^6347 := by
    have hnat : (4820294349 : ℕ)^8395*100000000000000^6347 ≤ 38089934841127^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820294349 10000000000 38089934841127 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375446643/625000000 : ℝ)^8395 ≤ (50962486306387/100000000000000 : ℝ)^6347 := by
    have hnat : (375446643 : ℕ)^8395*100000000000000^6347 ≤ 50962486306387^6347*625000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375446643 625000000 50962486306387 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469484213/2500000000 : ℝ), (4820294349/10000000000 : ℝ), (375446643/625000000 : ℝ)] ![(437903153833/4000000000000 : ℝ), (38089934841127/100000000000000 : ℝ), (50962486306387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469484213/2500000000 : ℝ)|^8395 ≤ (437903153833/4000000000000 : ℝ)^6347
        have hw : |(-469484213/2500000000 : ℝ)|=(469484213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4820294349/10000000000 : ℝ)|^8395 ≤ (38089934841127/100000000000000 : ℝ)^6347
        have hw : |(4820294349/10000000000 : ℝ)|=(4820294349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(375446643/625000000 : ℝ)|^8395 ≤ (50962486306387/100000000000000 : ℝ)^6347
        have hw : |(375446643/625000000 : ℝ)|=(375446643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s0_5 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (25863927/50000000 : ℝ)*x 0 + (-685490857/5000000000 : ℝ)*x 1 + (6007148113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25863927/50000000 : ℝ)^8395 ≤ (8363370176269/20000000000000 : ℝ)^6347 := by
    have hnat : (25863927 : ℕ)^8395*20000000000000^6347 ≤ 8363370176269^6347*50000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25863927 50000000 8363370176269 20000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685490857/5000000000 : ℝ)^8395 ≤ (1805160577561/25000000000000 : ℝ)^6347 := by
    have hnat : (685490857 : ℕ)^8395*25000000000000^6347 ≤ 1805160577561^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685490857 5000000000 1805160577561 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6007148113/10000000000 : ℝ)^8395 ≤ (50962506784857/100000000000000 : ℝ)^6347 := by
    have hnat : (6007148113 : ℕ)^8395*100000000000000^6347 ≤ 50962506784857^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6007148113 10000000000 50962506784857 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25863927/50000000 : ℝ), (-685490857/5000000000 : ℝ), (6007148113/10000000000 : ℝ)] ![(8363370176269/20000000000000 : ℝ), (1805160577561/25000000000000 : ℝ), (50962506784857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25863927/50000000 : ℝ)|^8395 ≤ (8363370176269/20000000000000 : ℝ)^6347
        have hw : |(25863927/50000000 : ℝ)|=(25863927/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-685490857/5000000000 : ℝ)|^8395 ≤ (1805160577561/25000000000000 : ℝ)^6347
        have hw : |(-685490857/5000000000 : ℝ)|=(685490857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6007148113/10000000000 : ℝ)|^8395 ≤ (50962506784857/100000000000000 : ℝ)^6347
        have hw : |(6007148113/10000000000 : ℝ)|=(6007148113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s0_6 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (161649601/312500000 : ℝ)*x 0 + (9386167/15625000 : ℝ)*x 1 + (-1370980889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161649601/312500000 : ℝ)^8395 ≤ (41816870469997/100000000000000 : ℝ)^6347 := by
    have hnat : (161649601 : ℕ)^8395*100000000000000^6347 ≤ 41816870469997^6347*312500000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161649601 312500000 41816870469997 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9386167/15625000 : ℝ)^8395 ≤ (25481246474633/50000000000000 : ℝ)^6347 := by
    have hnat : (9386167 : ℕ)^8395*50000000000000^6347 ≤ 25481246474633^6347*15625000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9386167 15625000 25481246474633 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370980889/10000000000 : ℝ)^8395 ≤ (1805159140781/25000000000000 : ℝ)^6347 := by
    have hnat : (1370980889 : ℕ)^8395*25000000000000^6347 ≤ 1805159140781^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370980889 10000000000 1805159140781 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161649601/312500000 : ℝ), (9386167/15625000 : ℝ), (-1370980889/10000000000 : ℝ)] ![(41816870469997/100000000000000 : ℝ), (25481246474633/50000000000000 : ℝ), (1805159140781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161649601/312500000 : ℝ)|^8395 ≤ (41816870469997/100000000000000 : ℝ)^6347
        have hw : |(161649601/312500000 : ℝ)|=(161649601/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9386167/15625000 : ℝ)|^8395 ≤ (25481246474633/50000000000000 : ℝ)^6347
        have hw : |(9386167/15625000 : ℝ)|=(9386167/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1370980889/10000000000 : ℝ)|^8395 ≤ (1805159140781/25000000000000 : ℝ)^6347
        have hw : |(-1370980889/10000000000 : ℝ)|=(1370980889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s0_7 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (841237683/2000000000 : ℝ)*x 0 + (5574766939/10000000000 : ℝ)*x 1 + (796431953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841237683/2000000000 : ℝ)^8395 ≤ (3180739458413/10000000000000 : ℝ)^6347 := by
    have hnat : (841237683 : ℕ)^8395*10000000000000^6347 ≤ 3180739458413^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841237683 2000000000 3180739458413 10000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5574766939/10000000000 : ℝ)^8395 ≤ (46168009431617/100000000000000 : ℝ)^6347 := by
    have hnat : (5574766939 : ℕ)^8395*100000000000000^6347 ≤ 46168009431617^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5574766939 10000000000 46168009431617 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796431953/2500000000 : ℝ)^8395 ≤ (22024595964661/100000000000000 : ℝ)^6347 := by
    have hnat : (796431953 : ℕ)^8395*100000000000000^6347 ≤ 22024595964661^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796431953 2500000000 22024595964661 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841237683/2000000000 : ℝ), (5574766939/10000000000 : ℝ), (796431953/2500000000 : ℝ)] ![(3180739458413/10000000000000 : ℝ), (46168009431617/100000000000000 : ℝ), (22024595964661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841237683/2000000000 : ℝ)|^8395 ≤ (3180739458413/10000000000000 : ℝ)^6347
        have hw : |(841237683/2000000000 : ℝ)|=(841237683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5574766939/10000000000 : ℝ)|^8395 ≤ (46168009431617/100000000000000 : ℝ)^6347
        have hw : |(5574766939/10000000000 : ℝ)|=(5574766939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796431953/2500000000 : ℝ)|^8395 ≤ (22024595964661/100000000000000 : ℝ)^6347
        have hw : |(796431953/2500000000 : ℝ)|=(796431953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1202_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (329/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27587/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4197/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4197 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4197*1^1024 ≤ 0^1024*1^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4197/1024 : ℝ) ≤ (467756701938615789/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4197 ≤ (467756701938615789/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4197*20000000000000000000^1024 ≤ 467756701938615789^1024*5^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 467756701938615789 20000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (467756701938615789/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4197 := by
      have hnat : (1 : ℕ)^1024*1^4197 ≤ 1^4197*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20467756701938615789/20000000000000000000 : ℝ) ≤ (5028282423634451/5000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (20467756701938615789/20000000000000000000 : ℝ)^1024 ≤ (5028282423634451/5000000000000000 : ℝ)^4197 := by
      have hnat : (20467756701938615789 : ℕ)^1024*5000000000000000^4197 ≤ 5028282423634451^4197*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20467756701938615789 20000000000000000000 5028282423634451 5000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028282423634451/5000000000000000 : ℝ)) (X := (20467756701938615789/20000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10467756701938615789/10000000000000000000 : ℝ) ≤ (2528282423634451/2500000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (10467756701938615789/10000000000000000000 : ℝ)^1024 ≤ (2528282423634451/2500000000000000 : ℝ)^4197 := by
      have hnat : (10467756701938615789 : ℕ)^1024*2500000000000000^4197 ≤ 2528282423634451^4197*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10467756701938615789 10000000000000000000 2528282423634451 2500000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528282423634451/2500000000000000 : ℝ)) (X := (10467756701938615789/10000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28282423634451/2000000000000000 : ℝ)*(0 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28282423634451/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(467756701938615789/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28282423634451/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4197/1024 : ℝ) := by
    rw [show (1 : ℝ)+(28282423634451/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028282423634451/5000000000000000 : ℝ) by norm_num, show 1+(467756701938615789/20000000000000000000 : ℝ)+(0 : ℝ)=(20467756701938615789/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(467756701938615789/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28282423634451/2000000000000000 : ℝ)*(2/5 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28282423634451/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528282423634451/2500000000000000 : ℝ) by norm_num, show 1+2*(467756701938615789/20000000000000000000 : ℝ)=(10467756701938615789/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28282423634451/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28282423634451/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28282423634451/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28282423634451/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28282423634451/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28282423634451/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1872965319/10000000000 : ℝ)*X 0 0+(3020283029/5000000000 : ℝ)*X 0 1+(478801363/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513412911/10000000000 : ℝ)*X 1 0+(-2590114929/10000000000 : ℝ)*X 1 1+(4788013603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5513413179/10000000000 : ℝ)*X 2 0+(2394006673/5000000000 : ℝ)*X 2 1+(-2590114901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1049045341/2500000000 : ℝ)*X 0 0+(3118460633/10000000000 : ℝ)*X 0 1+(5639741881/10000000000 : ℝ)*X 0 2+(1049045341/2500000000 : ℝ)*X 1 0+(3118460633/10000000000 : ℝ)*X 1 1+(5639741881/10000000000 : ℝ)*X 1 2+(1049045341/2500000000 : ℝ)*X 2 0+(3118460633/10000000000 : ℝ)*X 2 1+(5639741881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-469484213/2500000000 : ℝ)*X 0 0+(4820294349/10000000000 : ℝ)*X 0 1+(375446643/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((25863927/50000000 : ℝ)*X 1 0+(-685490857/5000000000 : ℝ)*X 1 1+(6007148113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((161649601/312500000 : ℝ)*X 2 0+(9386167/15625000 : ℝ)*X 2 1+(-1370980889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((841237683/2000000000 : ℝ)*X 0 0+(5574766939/10000000000 : ℝ)*X 0 1+(796431953/2500000000 : ℝ)*X 0 2+(841237683/2000000000 : ℝ)*X 1 0+(5574766939/10000000000 : ℝ)*X 1 1+(796431953/2500000000 : ℝ)*X 1 2+(841237683/2000000000 : ℝ)*X 2 0+(5574766939/10000000000 : ℝ)*X 2 1+(796431953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (211541804240318273069349/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18964309/50000000000000 : ℝ)*(base1) + (506236303/50000000000000 : ℝ)*(base19) + (970803461/100000000000000 : ℝ)*(base23) + (80477099/100000000000000 : ℝ)*(base24) + (49652869/20000000000000 : ℝ)*(upper3) + (298750483697933/50000000000000 : ℝ)*(major0) + (298750483697933/50000000000000 : ℝ)*(major1) + (298750483697933/50000000000000 : ℝ)*(major2) + (798373126092639/100000000000000 : ℝ)*(sp0) + (399187100564811/50000000000000 : ℝ)*(sp1) + (199593540580417/25000000000000 : ℝ)*(sp2) + (99156184256989/25000000000000 : ℝ)*(sp3) + (2125438207/100000000000000 : ℝ)*(sp4) + (1805205057/100000000000000 : ℝ)*(sp7) + (396626580161631/100000000000000 : ℝ)*(f.failure) + (199593803400557/25000000000000 : ℝ)*(f.sum) + (149772475410217/50000000000000000000000000000 : ℝ)*base66 + (514113698689783/100000000000000000000000000000 : ℝ)*base67 + (21242274310217/100000000000000000000000000000 : ℝ)*base70 + (499826668189783/100000000000000000000000000000 : ℝ)*base71 + (185502695360217/50000000000000000000000000000 : ℝ)*base74 + (141342437689783/100000000000000000000000000000 : ℝ)*base75 + (412915375189783/100000000000000000000000000000 : ℝ)*base77 + (606999516389783/100000000000000000000000000000 : ℝ)*base79 + (227885486310217/50000000000000000000000000000 : ℝ)*base82 + (459233/250000000000000000000 : ℝ)*base89 + (459233/250000000000000000000 : ℝ)*base91 + (459233/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19600120771555163302101/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58383191/100000000000000 : ℝ)*(base1) + (857812529/50000000000000 : ℝ)*(base19) + (2099102361/100000000000000 : ℝ)*(base23) + (73862451/20000000000000 : ℝ)*(upper3) + (129808611/100000000000000 : ℝ)*(upper5) + (63057170871717/10000000000000 : ℝ)*(major0) + (63057170871717/10000000000000 : ℝ)*(major1) + (63057170871717/10000000000000 : ℝ)*(major2) + (3563246669/100000000000000 : ℝ)*(sp1) + (4855215517/100000000000000 : ℝ)*(sp2) + (52660248452929/6250000000000 : ℝ)*(sp4) + (421279318995973/50000000000000 : ℝ)*(sp5) + (168511392509159/20000000000000 : ℝ)*(sp6) + (418579180852527/100000000000000 : ℝ)*(sp7) + (209289619617859/50000000000000 : ℝ)*(f.failure) + (842563916863673/100000000000000 : ℝ)*(f.sum) + (7831403047633/10000000000000000000000000000 : ℝ)*base66 + (11420505057633/20000000000000000000000000000 : ℝ)*base68 + (177865412397633/20000000000000000000000000000 : ℝ)*base70 + (184345108557633/20000000000000000000000000000 : ℝ)*base72 + (37821943642367/10000000000000000000000000000 : ℝ)*base73 + (129431321857633/20000000000000000000000000000 : ℝ)*base76 + (91858231037633/20000000000000000000000000000 : ℝ)*base78 + (170910263977633/20000000000000000000000000000 : ℝ)*base80 + (48492480797633/10000000000000000000000000000 : ℝ)*base82 + (152163/125000000000000000000 : ℝ)*base90 + (152163/125000000000000000000 : ℝ)*base92 + (152163/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1202_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (329/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27587/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1202_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1202_s1_0 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036640013/5000000000 : ℝ)*x 0 + (1421444281/2500000000 : ℝ)*x 1 + (5014576487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036640013/5000000000 : ℝ)^8395 ≤ (12478504337833/100000000000000 : ℝ)^6347 := by
    have hnat : (1036640013 : ℕ)^8395*100000000000000^6347 ≤ 12478504337833^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036640013 5000000000 12478504337833 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1421444281/2500000000 : ℝ)^8395 ≤ (11846971770573/25000000000000 : ℝ)^6347 := by
    have hnat : (1421444281 : ℕ)^8395*25000000000000^6347 ≤ 11846971770573^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421444281 2500000000 11846971770573 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5014576487/10000000000 : ℝ)^8395 ≤ (40133608565113/100000000000000 : ℝ)^6347 := by
    have hnat : (5014576487 : ℕ)^8395*100000000000000^6347 ≤ 40133608565113^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014576487 10000000000 40133608565113 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036640013/5000000000 : ℝ), (1421444281/2500000000 : ℝ), (5014576487/10000000000 : ℝ)] ![(12478504337833/100000000000000 : ℝ), (11846971770573/25000000000000 : ℝ), (40133608565113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036640013/5000000000 : ℝ)|^8395 ≤ (12478504337833/100000000000000 : ℝ)^6347
        have hw : |(-1036640013/5000000000 : ℝ)|=(1036640013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1421444281/2500000000 : ℝ)|^8395 ≤ (11846971770573/25000000000000 : ℝ)^6347
        have hw : |(1421444281/2500000000 : ℝ)|=(1421444281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5014576487/10000000000 : ℝ)|^8395 ≤ (40133608565113/100000000000000 : ℝ)^6347
        have hw : |(5014576487/10000000000 : ℝ)|=(5014576487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s1_1 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5415838897/10000000000 : ℝ)*x 0 + (-2434407401/10000000000 : ℝ)*x 1 + (5014576901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415838897/10000000000 : ℝ)^8395 ≤ (22217597661989/50000000000000 : ℝ)^6347 := by
    have hnat : (5415838897 : ℕ)^8395*50000000000000^6347 ≤ 22217597661989^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415838897 10000000000 22217597661989 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2434407401/10000000000 : ℝ)^8395 ≤ (3857797926691/25000000000000 : ℝ)^6347 := by
    have hnat : (2434407401 : ℕ)^8395*25000000000000^6347 ≤ 3857797926691^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434407401 10000000000 3857797926691 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5014576901/10000000000 : ℝ)^8395 ≤ (40133612947659/100000000000000 : ℝ)^6347 := by
    have hnat : (5014576901 : ℕ)^8395*100000000000000^6347 ≤ 40133612947659^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014576901 10000000000 40133612947659 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415838897/10000000000 : ℝ), (-2434407401/10000000000 : ℝ), (5014576901/10000000000 : ℝ)] ![(22217597661989/50000000000000 : ℝ), (3857797926691/25000000000000 : ℝ), (40133612947659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415838897/10000000000 : ℝ)|^8395 ≤ (22217597661989/50000000000000 : ℝ)^6347
        have hw : |(5415838897/10000000000 : ℝ)|=(5415838897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2434407401/10000000000 : ℝ)|^8395 ≤ (3857797926691/25000000000000 : ℝ)^6347
        have hw : |(-2434407401/10000000000 : ℝ)|=(2434407401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5014576901/10000000000 : ℝ)|^8395 ≤ (40133612947659/100000000000000 : ℝ)^6347
        have hw : |(5014576901/10000000000 : ℝ)|=(5014576901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s1_2 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5415837749/10000000000 : ℝ)*x 0 + (5014577637/10000000000 : ℝ)*x 1 + (-1217203979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415837749/10000000000 : ℝ)^8395 ≤ (22217591432887/50000000000000 : ℝ)^6347 := by
    have hnat : (5415837749 : ℕ)^8395*50000000000000^6347 ≤ 22217591432887^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415837749 10000000000 22217591432887 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014577637/10000000000 : ℝ)^8395 ≤ (10033405184713/25000000000000 : ℝ)^6347 := by
    have hnat : (5014577637 : ℕ)^8395*25000000000000^6347 ≤ 10033405184713^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014577637 10000000000 10033405184713 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217203979/5000000000 : ℝ)^8395 ≤ (15431196376729/100000000000000 : ℝ)^6347 := by
    have hnat : (1217203979 : ℕ)^8395*100000000000000^6347 ≤ 15431196376729^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217203979 5000000000 15431196376729 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415837749/10000000000 : ℝ), (5014577637/10000000000 : ℝ), (-1217203979/5000000000 : ℝ)] ![(22217591432887/50000000000000 : ℝ), (10033405184713/25000000000000 : ℝ), (15431196376729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415837749/10000000000 : ℝ)|^8395 ≤ (22217591432887/50000000000000 : ℝ)^6347
        have hw : |(5415837749/10000000000 : ℝ)|=(5415837749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5014577637/10000000000 : ℝ)|^8395 ≤ (10033405184713/25000000000000 : ℝ)^6347
        have hw : |(5014577637/10000000000 : ℝ)|=(5014577637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217203979/5000000000 : ℝ)|^8395 ≤ (15431196376729/100000000000000 : ℝ)^6347
        have hw : |(-1217203979/5000000000 : ℝ)|=(1217203979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s1_3 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4312311773/10000000000 : ℝ)*x 0 + (3688163209/10000000000 : ℝ)*x 1 + (629904153/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312311773/10000000000 : ℝ)^8395 ≤ (32873148326513/100000000000000 : ℝ)^6347 := by
    have hnat : (4312311773 : ℕ)^8395*100000000000000^6347 ≤ 32873148326513^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312311773 10000000000 32873148326513 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688163209/10000000000 : ℝ)^8395 ≤ (26732023499653/100000000000000 : ℝ)^6347 := by
    have hnat : (3688163209 : ℕ)^8395*100000000000000^6347 ≤ 26732023499653^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688163209 10000000000 26732023499653 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629904153/1250000000 : ℝ)^8395 ≤ (40394828164889/100000000000000 : ℝ)^6347 := by
    have hnat : (629904153 : ℕ)^8395*100000000000000^6347 ≤ 40394828164889^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629904153 1250000000 40394828164889 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312311773/10000000000 : ℝ), (3688163209/10000000000 : ℝ), (629904153/1250000000 : ℝ)] ![(32873148326513/100000000000000 : ℝ), (26732023499653/100000000000000 : ℝ), (40394828164889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312311773/10000000000 : ℝ)|^8395 ≤ (32873148326513/100000000000000 : ℝ)^6347
        have hw : |(4312311773/10000000000 : ℝ)|=(4312311773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688163209/10000000000 : ℝ)|^8395 ≤ (26732023499653/100000000000000 : ℝ)^6347
        have hw : |(3688163209/10000000000 : ℝ)|=(3688163209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(629904153/1250000000 : ℝ)|^8395 ≤ (40394828164889/100000000000000 : ℝ)^6347
        have hw : |(629904153/1250000000 : ℝ)|=(629904153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s1_4 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074004413/10000000000 : ℝ)*x 0 + (1255882953/2500000000 : ℝ)*x 1 + (5676649547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074004413/10000000000 : ℝ)^8395 ≤ (12484271363693/100000000000000 : ℝ)^6347 := by
    have hnat : (2074004413 : ℕ)^8395*100000000000000^6347 ≤ 12484271363693^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074004413 10000000000 12484271363693 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255882953/2500000000 : ℝ)^8395 ≤ (40228435686319/100000000000000 : ℝ)^6347 := by
    have hnat : (1255882953 : ℕ)^8395*100000000000000^6347 ≤ 40228435686319^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255882953 2500000000 40228435686319 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5676649547/10000000000 : ℝ)^8395 ≤ (47287292941943/100000000000000 : ℝ)^6347 := by
    have hnat : (5676649547 : ℕ)^8395*100000000000000^6347 ≤ 47287292941943^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676649547 10000000000 47287292941943 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074004413/10000000000 : ℝ), (1255882953/2500000000 : ℝ), (5676649547/10000000000 : ℝ)] ![(12484271363693/100000000000000 : ℝ), (40228435686319/100000000000000 : ℝ), (47287292941943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074004413/10000000000 : ℝ)|^8395 ≤ (12484271363693/100000000000000 : ℝ)^6347
        have hw : |(-2074004413/10000000000 : ℝ)|=(2074004413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255882953/2500000000 : ℝ)|^8395 ≤ (40228435686319/100000000000000 : ℝ)^6347
        have hw : |(1255882953/2500000000 : ℝ)|=(1255882953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5676649547/10000000000 : ℝ)|^8395 ≤ (47287292941943/100000000000000 : ℝ)^6347
        have hw : |(5676649547/10000000000 : ℝ)|=(5676649547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s1_5 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243246541/10000000000 : ℝ)*x 0 + (-221542039/1250000000 : ℝ)*x 1 + (709581009/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243246541/10000000000 : ℝ)^8395 ≤ (42571906945899/100000000000000 : ℝ)^6347 := by
    have hnat : (5243246541 : ℕ)^8395*100000000000000^6347 ≤ 42571906945899^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243246541 10000000000 42571906945899 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221542039/1250000000 : ℝ)^8395 ≤ (2028163269009/20000000000000 : ℝ)^6347 := by
    have hnat : (221542039 : ℕ)^8395*20000000000000^6347 ≤ 2028163269009^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221542039 1250000000 2028163269009 20000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709581009/1250000000 : ℝ)^8395 ≤ (23643638345163/50000000000000 : ℝ)^6347 := by
    have hnat : (709581009 : ℕ)^8395*50000000000000^6347 ≤ 23643638345163^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709581009 1250000000 23643638345163 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243246541/10000000000 : ℝ), (-221542039/1250000000 : ℝ), (709581009/1250000000 : ℝ)] ![(42571906945899/100000000000000 : ℝ), (2028163269009/20000000000000 : ℝ), (23643638345163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243246541/10000000000 : ℝ)|^8395 ≤ (42571906945899/100000000000000 : ℝ)^6347
        have hw : |(5243246541/10000000000 : ℝ)|=(5243246541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221542039/1250000000 : ℝ)|^8395 ≤ (2028163269009/20000000000000 : ℝ)^6347
        have hw : |(-221542039/1250000000 : ℝ)|=(221542039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709581009/1250000000 : ℝ)|^8395 ≤ (23643638345163/50000000000000 : ℝ)^6347
        have hw : |(709581009/1250000000 : ℝ)|=(709581009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s1_6 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243246623/10000000000 : ℝ)*x 0 + (567664859/1000000000 : ℝ)*x 1 + (-886167721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243246623/10000000000 : ℝ)^8395 ≤ (42571907826519/100000000000000 : ℝ)^6347 := by
    have hnat : (5243246623 : ℕ)^8395*100000000000000^6347 ≤ 42571907826519^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243246623 10000000000 42571907826519 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (567664859/1000000000 : ℝ)^8395 ≤ (47287282397673/100000000000000 : ℝ)^6347 := by
    have hnat : (567664859 : ℕ)^8395*100000000000000^6347 ≤ 47287282397673^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567664859 1000000000 47287282397673 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886167721/5000000000 : ℝ)^8395 ≤ (5070404880459/50000000000000 : ℝ)^6347 := by
    have hnat : (886167721 : ℕ)^8395*50000000000000^6347 ≤ 5070404880459^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886167721 5000000000 5070404880459 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243246623/10000000000 : ℝ), (567664859/1000000000 : ℝ), (-886167721/5000000000 : ℝ)] ![(42571907826519/100000000000000 : ℝ), (47287282397673/100000000000000 : ℝ), (5070404880459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243246623/10000000000 : ℝ)|^8395 ≤ (42571907826519/100000000000000 : ℝ)^6347
        have hw : |(5243246623/10000000000 : ℝ)|=(5243246623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(567664859/1000000000 : ℝ)|^8395 ≤ (47287282397673/100000000000000 : ℝ)^6347
        have hw : |(567664859/1000000000 : ℝ)|=(567664859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-886167721/5000000000 : ℝ)|^8395 ≤ (5070404880459/50000000000000 : ℝ)^6347
        have hw : |(-886167721/5000000000 : ℝ)|=(886167721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s1_7 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (431377167/1000000000 : ℝ)*x 0 + (25106029/50000000 : ℝ)*x 1 + (741307807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431377167/1000000000 : ℝ)^8395 ≤ (8221967263591/25000000000000 : ℝ)^6347 := by
    have hnat : (431377167 : ℕ)^8395*25000000000000^6347 ≤ 8221967263591^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431377167 1000000000 8221967263591 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25106029/50000000 : ℝ)^8395 ≤ (20101900254463/50000000000000 : ℝ)^6347 := by
    have hnat : (25106029 : ℕ)^8395*50000000000000^6347 ≤ 20101900254463^6347*50000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25106029 50000000 20101900254463 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (741307807/2000000000 : ℝ)^8395 ≤ (13454165207143/50000000000000 : ℝ)^6347 := by
    have hnat : (741307807 : ℕ)^8395*50000000000000^6347 ≤ 13454165207143^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741307807 2000000000 13454165207143 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431377167/1000000000 : ℝ), (25106029/50000000 : ℝ), (741307807/2000000000 : ℝ)] ![(8221967263591/25000000000000 : ℝ), (20101900254463/50000000000000 : ℝ), (13454165207143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431377167/1000000000 : ℝ)|^8395 ≤ (8221967263591/25000000000000 : ℝ)^6347
        have hw : |(431377167/1000000000 : ℝ)|=(431377167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25106029/50000000 : ℝ)|^8395 ≤ (20101900254463/50000000000000 : ℝ)^6347
        have hw : |(25106029/50000000 : ℝ)|=(25106029/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(741307807/2000000000 : ℝ)|^8395 ≤ (13454165207143/50000000000000 : ℝ)^6347
        have hw : |(741307807/2000000000 : ℝ)|=(741307807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1202_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5979/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20171/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27587/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27587/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27587/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27587/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27587/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27587/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (329/50000 : ℝ) ^ (4197/1024 : ℝ) ≤ (28552823897/25000000000000000000 : ℝ) := by
    have hpowers : (329/50000 : ℝ)^4197 ≤ (28552823897/25000000000000000000 : ℝ)^1024 := by
      have hnat : (329 : ℕ)^4197*25000000000000000000^1024 ≤ 28552823897^1024*50000^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        329 50000 28552823897 25000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (329/50000 : ℝ)) (X := (28552823897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27587/100000 : ℝ) ^ (4197/1024 : ℝ) ≤ (255048640655585373/50000000000000000000 : ℝ) := by
    have hpowers : (27587/100000 : ℝ)^4197 ≤ (255048640655585373/50000000000000000000 : ℝ)^1024 := by
      have hnat : (27587 : ℕ)^4197*50000000000000000000^1024 ≤ 255048640655585373^1024*100000^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27587 100000 255048640655585373 50000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27587/100000 : ℝ)) (X := (255048640655585373/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000028552823897/12500000000000000000 : ℝ) ≤ (5000000002786571/5000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (12500000028552823897/12500000000000000000 : ℝ)^1024 ≤ (5000000002786571/5000000000000000 : ℝ)^4197 := by
      have hnat : (12500000028552823897 : ℕ)^1024*5000000000000000^4197 ≤ 5000000002786571^4197*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000028552823897 12500000000000000000 5000000002786571 5000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000002786571/5000000000000000 : ℝ)) (X := (12500000028552823897/12500000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50255048697761233167/50000000000000000000 : ℝ) ≤ (2503105405940547/2500000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (50255048697761233167/50000000000000000000 : ℝ)^1024 ≤ (2503105405940547/2500000000000000 : ℝ)^4197 := by
      have hnat : (50255048697761233167 : ℕ)^1024*2500000000000000^4197 ≤ 2503105405940547^4197*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50255048697761233167 50000000000000000000 2503105405940547 2500000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503105405940547/2500000000000000 : ℝ)) (X := (50255048697761233167/50000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25255048640655585373/25000000000000000000 : ℝ) ≤ (5012421620975617/5000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (25255048640655585373/25000000000000000000 : ℝ)^1024 ≤ (5012421620975617/5000000000000000 : ℝ)^4197 := by
      have hnat : (25255048640655585373 : ℕ)^1024*5000000000000000^4197 ≤ 5012421620975617^4197*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25255048640655585373 25000000000000000000 5012421620975617 5000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012421620975617/5000000000000000 : ℝ)) (X := (25255048640655585373/25000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28552823897/25000000000000000000 : ℝ) ≤ ((19233832378610168313/19235000000000000000 : ℝ)+2*(6210809094523/1346450000000000 : ℝ)*(329/50000 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (19233832378610168313/19235000000000000000 : ℝ)+2*(6210809094523/1346450000000000 : ℝ)*(329/50000 : ℝ)=(5000000002786571/5000000000000000 : ℝ) by norm_num, show 1+2*(28552823897/25000000000000000000 : ℝ)=(12500000028552823897/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(255048640655585373/50000000000000000000 : ℝ)+(28552823897/25000000000000000000 : ℝ) ≤ ((19233832378610168313/19235000000000000000 : ℝ)+(6210809094523/1346450000000000 : ℝ)*((27587/100000 : ℝ)+(329/50000 : ℝ)))^(4197/1024 : ℝ) := by
    rw [show (19233832378610168313/19235000000000000000 : ℝ)+(6210809094523/1346450000000000 : ℝ)*((27587/100000 : ℝ)+(329/50000 : ℝ))=(2503105405940547/2500000000000000 : ℝ) by norm_num, show 1+(255048640655585373/50000000000000000000 : ℝ)+(28552823897/25000000000000000000 : ℝ)=(50255048697761233167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(255048640655585373/50000000000000000000 : ℝ) ≤ ((19233832378610168313/19235000000000000000 : ℝ)+2*(6210809094523/1346450000000000 : ℝ)*(27587/100000 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (19233832378610168313/19235000000000000000 : ℝ)+2*(6210809094523/1346450000000000 : ℝ)*(27587/100000 : ℝ)=(5012421620975617/5000000000000000 : ℝ) by norm_num, show 1+2*(255048640655585373/50000000000000000000 : ℝ)=(25255048640655585373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19233832378610168313/19235000000000000000 : ℝ)*(X 1 0+X 2 0)+(6210809094523/1346450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (329/50000 : ℝ)) (hi := (27587/100000 : ℝ)) (c := (19233832378610168313/19235000000000000000 : ℝ)) (alpha := (6210809094523/1346450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19233832378610168313/19235000000000000000 : ℝ)*(X 0 1+X 2 1)+(6210809094523/1346450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (329/50000 : ℝ)) (hi := (27587/100000 : ℝ)) (c := (19233832378610168313/19235000000000000000 : ℝ)) (alpha := (6210809094523/1346450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19233832378610168313/19235000000000000000 : ℝ)*(X 0 2+X 1 2)+(6210809094523/1346450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (329/50000 : ℝ)) (hi := (27587/100000 : ℝ)) (c := (19233832378610168313/19235000000000000000 : ℝ)) (alpha := (6210809094523/1346450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1036640013/5000000000 : ℝ)*X 0 0+(1421444281/2500000000 : ℝ)*X 0 1+(5014576487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415838897/10000000000 : ℝ)*X 1 0+(-2434407401/10000000000 : ℝ)*X 1 1+(5014576901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5415837749/10000000000 : ℝ)*X 2 0+(5014577637/10000000000 : ℝ)*X 2 1+(-1217203979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312311773/10000000000 : ℝ)*X 0 0+(3688163209/10000000000 : ℝ)*X 0 1+(629904153/1250000000 : ℝ)*X 0 2+(4312311773/10000000000 : ℝ)*X 1 0+(3688163209/10000000000 : ℝ)*X 1 1+(629904153/1250000000 : ℝ)*X 1 2+(4312311773/10000000000 : ℝ)*X 2 0+(3688163209/10000000000 : ℝ)*X 2 1+(629904153/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2074004413/10000000000 : ℝ)*X 0 0+(1255882953/2500000000 : ℝ)*X 0 1+(5676649547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243246541/10000000000 : ℝ)*X 1 0+(-221542039/1250000000 : ℝ)*X 1 1+(709581009/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5243246623/10000000000 : ℝ)*X 2 0+(567664859/1000000000 : ℝ)*X 2 1+(-886167721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431377167/1000000000 : ℝ)*X 0 0+(25106029/50000000 : ℝ)*X 0 1+(741307807/2000000000 : ℝ)*X 0 2+(431377167/1000000000 : ℝ)*X 1 0+(25106029/50000000 : ℝ)*X 1 1+(741307807/2000000000 : ℝ)*X 1 2+(431377167/1000000000 : ℝ)*X 2 0+(25106029/50000000 : ℝ)*X 2 1+(741307807/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (309121575226374027603987/134645000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2234449/25000000000000 : ℝ)*(base16) + (27406223/4000000000000 : ℝ)*(base19) + (122222881/25000000000000 : ℝ)*(base23) + (11980763/20000000000000 : ℝ)*(upper2) + (85784027/50000000000000 : ℝ)*(upper3) + (557509082530037/50000000000000 : ℝ)*(major0) + (557509082530037/50000000000000 : ℝ)*(major1) + (557509082530037/50000000000000 : ℝ)*(major2) + (1489873615773239/100000000000000 : ℝ)*(sp0) + (744938176737963/50000000000000 : ℝ)*(sp1) + (372469139669443/25000000000000 : ℝ)*(sp2) + (370078217796741/50000000000000 : ℝ)*(sp3) + (1715898029/50000000000000 : ℝ)*(sp4) + (692607453/25000000000000 : ℝ)*(sp7) + (370079603011647/50000000000000 : ℝ)*(f.failure) + (1489877047569297/100000000000000 : ℝ)*(f.sum) + (60547399131503/67322500000000000000000000000 : ℝ)*base66 + (27936003626135576933/6732250000000000000000000000000000 : ℝ)*base68 + (427777284121173067/6732250000000000000000000000000000 : ℝ)*base69 + (4667016262523923067/6732250000000000000000000000000000 : ℝ)*base71 + (31000110273917/16830625000000000000000000000 : ℝ)*base74 + (32720934452454576933/6732250000000000000000000000000000 : ℝ)*base76 + (5064746780530423067/6732250000000000000000000000000000 : ℝ)*base77 + (2511008688317576933/6732250000000000000000000000000000 : ℝ)*base80 + (4794206012833/16830625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (767521/125000000000000000000 : ℝ)*base89 + (767521/125000000000000000000 : ℝ)*base91 + (767521/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28592559990878374532640882741/3366125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90153817/50000000000000 : ℝ)*(base1) + (1728087577/100000000000000 : ℝ)*(base19) + (177364491/10000000000000 : ℝ)*(base23) + (230307/2500000000000 : ℝ)*(upper3) + (220976427/100000000000000 : ℝ)*(upper5) + (1145884174234983/100000000000000 : ℝ)*(major0) + (1145884174234983/100000000000000 : ℝ)*(major1) + (1145884174234983/100000000000000 : ℝ)*(major2) + (1547062953/25000000000000 : ℝ)*(sp1) + (3422428627/50000000000000 : ℝ)*(sp2) + (1531119901804593/100000000000000 : ℝ)*(sp4) + (153111180515757/10000000000000 : ℝ)*(sp5) + (765555551497397/50000000000000 : ℝ)*(sp6) + (190162040881289/25000000000000 : ℝ)*(sp7) + (76064834383279/10000000000000 : ℝ)*(f.failure) + (1531119721496959/100000000000000 : ℝ)*(f.sum) + (210760111983123/134645000000000000000000000000 : ℝ)*base65 + (86147265050027755753/13464500000000000000000000000000000 : ℝ)*base67 + (21962120716189744247/13464500000000000000000000000000000 : ℝ)*base70 + (32994671039826755753/13464500000000000000000000000000000 : ℝ)*base71 + (210638735124879/67322500000000000000000000000 : ℝ)*base73 + (30720020715285755753/13464500000000000000000000000000000 : ℝ)*base75 + (48694746954503755753/13464500000000000000000000000000000 : ℝ)*base77 + (121695473947368755753/13464500000000000000000000000000000 : ℝ)*base79 + (225825543049941/67322500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (227103/25000000000000000000 : ℝ)*base90 + (227103/25000000000000000000 : ℝ)*base92 + (227103/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1202_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20171/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1202_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1202_s2_0 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123355169/10000000000 : ℝ)*x 0 + (2749882399/5000000000 : ℝ)*x 1 + (516869091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123355169/10000000000 : ℝ)^8395 ≤ (6439343787019/50000000000000 : ℝ)^6347 := by
    have hnat : (2123355169 : ℕ)^8395*50000000000000^6347 ≤ 6439343787019^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123355169 10000000000 6439343787019 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749882399/5000000000 : ℝ)^8395 ≤ (5668529530401/12500000000000 : ℝ)^6347 := by
    have hnat : (2749882399 : ℕ)^8395*12500000000000^6347 ≤ 5668529530401^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749882399 5000000000 5668529530401 12500000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516869091/1000000000 : ℝ)^8395 ≤ (41773076158541/100000000000000 : ℝ)^6347 := by
    have hnat : (516869091 : ℕ)^8395*100000000000000^6347 ≤ 41773076158541^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516869091 1000000000 41773076158541 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123355169/10000000000 : ℝ), (2749882399/5000000000 : ℝ), (516869091/1000000000 : ℝ)] ![(6439343787019/50000000000000 : ℝ), (5668529530401/12500000000000 : ℝ), (41773076158541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123355169/10000000000 : ℝ)|^8395 ≤ (6439343787019/50000000000000 : ℝ)^6347
        have hw : |(-2123355169/10000000000 : ℝ)|=(2123355169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749882399/5000000000 : ℝ)|^8395 ≤ (5668529530401/12500000000000 : ℝ)^6347
        have hw : |(2749882399/5000000000 : ℝ)|=(2749882399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516869091/1000000000 : ℝ)|^8395 ≤ (41773076158541/100000000000000 : ℝ)^6347
        have hw : |(516869091/1000000000 : ℝ)|=(516869091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s2_1 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (134283233/250000000 : ℝ)*x 0 + (-1147544851/5000000000 : ℝ)*x 1 + (5168695451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134283233/250000000 : ℝ)^8395 ≤ (10988203710349/25000000000000 : ℝ)^6347 := by
    have hnat : (134283233 : ℕ)^8395*25000000000000^6347 ≤ 10988203710349^6347*250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134283233 250000000 10988203710349 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147544851/5000000000 : ℝ)^8395 ≤ (14274060442297/100000000000000 : ℝ)^6347 := by
    have hnat : (1147544851 : ℕ)^8395*100000000000000^6347 ≤ 14274060442297^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147544851 5000000000 14274060442297 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5168695451/10000000000 : ℝ)^8395 ≤ (10443281175191/25000000000000 : ℝ)^6347 := by
    have hnat : (5168695451 : ℕ)^8395*25000000000000^6347 ≤ 10443281175191^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168695451 10000000000 10443281175191 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134283233/250000000 : ℝ), (-1147544851/5000000000 : ℝ), (5168695451/10000000000 : ℝ)] ![(10988203710349/25000000000000 : ℝ), (14274060442297/100000000000000 : ℝ), (10443281175191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134283233/250000000 : ℝ)|^8395 ≤ (10988203710349/25000000000000 : ℝ)^6347
        have hw : |(134283233/250000000 : ℝ)|=(134283233/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1147544851/5000000000 : ℝ)|^8395 ≤ (14274060442297/100000000000000 : ℝ)^6347
        have hw : |(-1147544851/5000000000 : ℝ)|=(1147544851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5168695451/10000000000 : ℝ)|^8395 ≤ (10443281175191/25000000000000 : ℝ)^6347
        have hw : |(5168695451/10000000000 : ℝ)|=(5168695451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s2_2 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685665657/5000000000 : ℝ)*x 0 + (2584346339/5000000000 : ℝ)*x 1 + (-1147545341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685665657/5000000000 : ℝ)^8395 ≤ (43952836422929/100000000000000 : ℝ)^6347 := by
    have hnat : (2685665657 : ℕ)^8395*100000000000000^6347 ≤ 43952836422929^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685665657 5000000000 43952836422929 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584346339/5000000000 : ℝ)^8395 ≤ (10443273764511/25000000000000 : ℝ)^6347 := by
    have hnat : (2584346339 : ℕ)^8395*25000000000000^6347 ≤ 10443273764511^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584346339 5000000000 10443273764511 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147545341/5000000000 : ℝ)^8395 ≤ (14274068503989/100000000000000 : ℝ)^6347 := by
    have hnat : (1147545341 : ℕ)^8395*100000000000000^6347 ≤ 14274068503989^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147545341 5000000000 14274068503989 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685665657/5000000000 : ℝ), (2584346339/5000000000 : ℝ), (-1147545341/5000000000 : ℝ)] ![(43952836422929/100000000000000 : ℝ), (10443273764511/25000000000000 : ℝ), (14274068503989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685665657/5000000000 : ℝ)|^8395 ≤ (43952836422929/100000000000000 : ℝ)^6347
        have hw : |(2685665657/5000000000 : ℝ)|=(2685665657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2584346339/5000000000 : ℝ)|^8395 ≤ (10443273764511/25000000000000 : ℝ)^6347
        have hw : |(2584346339/5000000000 : ℝ)|=(2584346339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1147545341/5000000000 : ℝ)|^8395 ≤ (14274068503989/100000000000000 : ℝ)^6347
        have hw : |(-1147545341/5000000000 : ℝ)|=(1147545341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s2_3 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271675603/625000000 : ℝ)*x 0 + (4026083123/10000000000 : ℝ)*x 1 + (586562851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271675603/625000000 : ℝ)^8395 ≤ (33221433392849/100000000000000 : ℝ)^6347 := by
    have hnat : (271675603 : ℕ)^8395*100000000000000^6347 ≤ 33221433392849^6347*625000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271675603 625000000 33221433392849 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026083123/10000000000 : ℝ)^8395 ≤ (3001852915453/10000000000000 : ℝ)^6347 := by
    have hnat : (4026083123 : ℕ)^8395*10000000000000^6347 ≤ 3001852915453^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026083123 10000000000 3001852915453 10000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586562851/1250000000 : ℝ)^8395 ≤ (36760037439859/100000000000000 : ℝ)^6347 := by
    have hnat : (586562851 : ℕ)^8395*100000000000000^6347 ≤ 36760037439859^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586562851 1250000000 36760037439859 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271675603/625000000 : ℝ), (4026083123/10000000000 : ℝ), (586562851/1250000000 : ℝ)] ![(33221433392849/100000000000000 : ℝ), (3001852915453/10000000000000 : ℝ), (36760037439859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271675603/625000000 : ℝ)|^8395 ≤ (33221433392849/100000000000000 : ℝ)^6347
        have hw : |(271675603/625000000 : ℝ)|=(271675603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026083123/10000000000 : ℝ)|^8395 ≤ (3001852915453/10000000000000 : ℝ)^6347
        have hw : |(4026083123/10000000000 : ℝ)|=(4026083123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(586562851/1250000000 : ℝ)|^8395 ≤ (36760037439859/100000000000000 : ℝ)^6347
        have hw : |(586562851/1250000000 : ℝ)|=(586562851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s2_4 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-132715077/625000000 : ℝ)*x 0 + (2585440583/5000000000 : ℝ)*x 1 + (1374388597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132715077/625000000 : ℝ)^8395 ≤ (6439689002681/50000000000000 : ℝ)^6347 := by
    have hnat : (132715077 : ℕ)^8395*50000000000000^6347 ≤ 6439689002681^6347*625000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132715077 625000000 6439689002681 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585440583/5000000000 : ℝ)^8395 ≤ (41796491077781/100000000000000 : ℝ)^6347 := by
    have hnat : (2585440583 : ℕ)^8395*100000000000000^6347 ≤ 41796491077781^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585440583 5000000000 41796491077781 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374388597/2500000000 : ℝ)^8395 ≤ (9064826181789/20000000000000 : ℝ)^6347 := by
    have hnat : (1374388597 : ℕ)^8395*20000000000000^6347 ≤ 9064826181789^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374388597 2500000000 9064826181789 20000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132715077/625000000 : ℝ), (2585440583/5000000000 : ℝ), (1374388597/2500000000 : ℝ)] ![(6439689002681/50000000000000 : ℝ), (41796491077781/100000000000000 : ℝ), (9064826181789/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132715077/625000000 : ℝ)|^8395 ≤ (6439689002681/50000000000000 : ℝ)^6347
        have hw : |(-132715077/625000000 : ℝ)|=(132715077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585440583/5000000000 : ℝ)|^8395 ≤ (41796491077781/100000000000000 : ℝ)^6347
        have hw : |(2585440583/5000000000 : ℝ)|=(2585440583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1374388597/2500000000 : ℝ)|^8395 ≤ (9064826181789/20000000000000 : ℝ)^6347
        have hw : |(1374388597/2500000000 : ℝ)|=(1374388597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s2_5 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2114799/4000000 : ℝ)*x 0 + (-983114541/5000000000 : ℝ)*x 1 + (549755441/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114799/4000000 : ℝ)^8395 ≤ (8608478387611/20000000000000 : ℝ)^6347 := by
    have hnat : (2114799 : ℕ)^8395*20000000000000^6347 ≤ 8608478387611^6347*4000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114799 4000000 8608478387611 20000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983114541/5000000000 : ℝ)^8395 ≤ (2908369224909/25000000000000 : ℝ)^6347 := by
    have hnat : (983114541 : ℕ)^8395*25000000000000^6347 ≤ 2908369224909^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983114541 5000000000 2908369224909 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549755441/1000000000 : ℝ)^8395 ≤ (2832758196803/6250000000000 : ℝ)^6347 := by
    have hnat : (549755441 : ℕ)^8395*6250000000000^6347 ≤ 2832758196803^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549755441 1000000000 2832758196803 6250000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114799/4000000 : ℝ), (-983114541/5000000000 : ℝ), (549755441/1000000000 : ℝ)] ![(8608478387611/20000000000000 : ℝ), (2908369224909/25000000000000 : ℝ), (2832758196803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114799/4000000 : ℝ)|^8395 ≤ (8608478387611/20000000000000 : ℝ)^6347
        have hw : |(2114799/4000000 : ℝ)|=(2114799/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983114541/5000000000 : ℝ)|^8395 ≤ (2908369224909/25000000000000 : ℝ)^6347
        have hw : |(-983114541/5000000000 : ℝ)|=(983114541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549755441/1000000000 : ℝ)|^8395 ≤ (2832758196803/6250000000000 : ℝ)^6347
        have hw : |(549755441/1000000000 : ℝ)|=(549755441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s2_6 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643498837/5000000000 : ℝ)*x 0 + (5497554431/10000000000 : ℝ)*x 1 + (-1966228813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643498837/5000000000 : ℝ)^8395 ≤ (21521196905853/50000000000000 : ℝ)^6347 := by
    have hnat : (2643498837 : ℕ)^8395*50000000000000^6347 ≤ 21521196905853^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643498837 5000000000 21521196905853 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497554431/10000000000 : ℝ)^8395 ≤ (22662065688923/50000000000000 : ℝ)^6347 := by
    have hnat : (5497554431 : ℕ)^8395*50000000000000^6347 ≤ 22662065688923^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497554431 10000000000 22662065688923 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966228813/10000000000 : ℝ)^8395 ≤ (11633474794501/100000000000000 : ℝ)^6347 := by
    have hnat : (1966228813 : ℕ)^8395*100000000000000^6347 ≤ 11633474794501^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966228813 10000000000 11633474794501 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643498837/5000000000 : ℝ), (5497554431/10000000000 : ℝ), (-1966228813/10000000000 : ℝ)] ![(21521196905853/50000000000000 : ℝ), (22662065688923/50000000000000 : ℝ), (11633474794501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643498837/5000000000 : ℝ)|^8395 ≤ (21521196905853/50000000000000 : ℝ)^6347
        have hw : |(2643498837/5000000000 : ℝ)|=(2643498837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497554431/10000000000 : ℝ)|^8395 ≤ (22662065688923/50000000000000 : ℝ)^6347
        have hw : |(5497554431/10000000000 : ℝ)|=(5497554431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966228813/10000000000 : ℝ)|^8395 ≤ (11633474794501/100000000000000 : ℝ)^6347
        have hw : |(-1966228813/10000000000 : ℝ)|=(1966228813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s2_7 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (434698527/1000000000 : ℝ)*x 0 + (234404837/500000000 : ℝ)*x 1 + (2015265457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434698527/1000000000 : ℝ)^8395 ≤ (6644641746699/20000000000000 : ℝ)^6347 := by
    have hnat : (434698527 : ℕ)^8395*20000000000000^6347 ≤ 6644641746699^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434698527 1000000000 6644641746699 20000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234404837/500000000 : ℝ)^8395 ≤ (234972101/640000000 : ℝ)^6347 := by
    have hnat : (234404837 : ℕ)^8395*640000000^6347 ≤ 234972101^6347*500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234404837 500000000 234972101 640000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015265457/5000000000 : ℝ)^8395 ≤ (15031200233441/50000000000000 : ℝ)^6347 := by
    have hnat : (2015265457 : ℕ)^8395*50000000000000^6347 ≤ 15031200233441^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015265457 5000000000 15031200233441 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434698527/1000000000 : ℝ), (234404837/500000000 : ℝ), (2015265457/5000000000 : ℝ)] ![(6644641746699/20000000000000 : ℝ), (234972101/640000000 : ℝ), (15031200233441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434698527/1000000000 : ℝ)|^8395 ≤ (6644641746699/20000000000000 : ℝ)^6347
        have hw : |(434698527/1000000000 : ℝ)|=(434698527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(234404837/500000000 : ℝ)|^8395 ≤ (234972101/640000000 : ℝ)^6347
        have hw : |(234404837/500000000 : ℝ)|=(234404837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015265457/5000000000 : ℝ)|^8395 ≤ (15031200233441/50000000000000 : ℝ)^6347
        have hw : |(2015265457/5000000000 : ℝ)|=(2015265457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1202_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9333/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16331/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20171/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20171/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20171/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20171/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20171/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20171/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5979/100000 : ℝ) ^ (4197/1024 : ℝ) ≤ (193588539262557/20000000000000000000 : ℝ) := by
    have hpowers : (5979/100000 : ℝ)^4197 ≤ (193588539262557/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5979 : ℕ)^4197*20000000000000000000^1024 ≤ 193588539262557^1024*100000^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5979 100000 193588539262557 20000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5979/100000 : ℝ)) (X := (193588539262557/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20171/100000 : ℝ) ^ (4197/1024 : ℝ) ≤ (141362113100198617/100000000000000000000 : ℝ) := by
    have hpowers : (20171/100000 : ℝ)^4197 ≤ (141362113100198617/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20171 : ℕ)^4197*100000000000000000000^1024 ≤ 141362113100198617^1024*100000^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20171 100000 141362113100198617 100000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20171/100000 : ℝ)) (X := (141362113100198617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000193588539262557/10000000000000000000 : ℝ) ≤ (1250005904015177/1250000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (10000193588539262557/10000000000000000000 : ℝ)^1024 ≤ (1250005904015177/1250000000000000 : ℝ)^4197 := by
      have hnat : (10000193588539262557 : ℕ)^1024*1250000000000000^4197 ≤ 1250005904015177^4197*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000193588539262557 10000000000000000000 1250005904015177 1250000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250005904015177/1250000000000000 : ℝ)) (X := (10000193588539262557/10000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50071165027898255701/50000000000000000000 : ℝ) ≤ (5001735377987539/5000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (50071165027898255701/50000000000000000000 : ℝ)^1024 ≤ (5001735377987539/5000000000000000 : ℝ)^4197 := by
      have hnat : (50071165027898255701 : ℕ)^1024*5000000000000000^4197 ≤ 5001735377987539^4197*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50071165027898255701 50000000000000000000 5001735377987539 5000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001735377987539/5000000000000000 : ℝ)) (X := (50071165027898255701/50000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50141362113100198617/50000000000000000000 : ℝ) ≤ (500344713991437/500000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (50141362113100198617/50000000000000000000 : ℝ)^1024 ≤ (500344713991437/500000000000000 : ℝ)^4197 := by
      have hnat : (50141362113100198617 : ℕ)^1024*500000000000000^4197 ≤ 500344713991437^4197*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50141362113100198617 50000000000000000000 500344713991437 500000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500344713991437/500000000000000 : ℝ)) (X := (50141362113100198617/50000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(193588539262557/20000000000000000000 : ℝ) ≤ ((35469932955006261419/35480000000000000000 : ℝ)+2*(1711761926831/709600000000000 : ℝ)*(5979/100000 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (35469932955006261419/35480000000000000000 : ℝ)+2*(1711761926831/709600000000000 : ℝ)*(5979/100000 : ℝ)=(1250005904015177/1250000000000000 : ℝ) by norm_num, show 1+2*(193588539262557/20000000000000000000 : ℝ)=(10000193588539262557/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(141362113100198617/100000000000000000000 : ℝ)+(193588539262557/20000000000000000000 : ℝ) ≤ ((35469932955006261419/35480000000000000000 : ℝ)+(1711761926831/709600000000000 : ℝ)*((20171/100000 : ℝ)+(5979/100000 : ℝ)))^(4197/1024 : ℝ) := by
    rw [show (35469932955006261419/35480000000000000000 : ℝ)+(1711761926831/709600000000000 : ℝ)*((20171/100000 : ℝ)+(5979/100000 : ℝ))=(5001735377987539/5000000000000000 : ℝ) by norm_num, show 1+(141362113100198617/100000000000000000000 : ℝ)+(193588539262557/20000000000000000000 : ℝ)=(50071165027898255701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(141362113100198617/100000000000000000000 : ℝ) ≤ ((35469932955006261419/35480000000000000000 : ℝ)+2*(1711761926831/709600000000000 : ℝ)*(20171/100000 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (35469932955006261419/35480000000000000000 : ℝ)+2*(1711761926831/709600000000000 : ℝ)*(20171/100000 : ℝ)=(500344713991437/500000000000000 : ℝ) by norm_num, show 1+2*(141362113100198617/100000000000000000000 : ℝ)=(50141362113100198617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35469932955006261419/35480000000000000000 : ℝ)*(X 1 0+X 2 0)+(1711761926831/709600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (5979/100000 : ℝ)) (hi := (20171/100000 : ℝ)) (c := (35469932955006261419/35480000000000000000 : ℝ)) (alpha := (1711761926831/709600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35469932955006261419/35480000000000000000 : ℝ)*(X 0 1+X 2 1)+(1711761926831/709600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (5979/100000 : ℝ)) (hi := (20171/100000 : ℝ)) (c := (35469932955006261419/35480000000000000000 : ℝ)) (alpha := (1711761926831/709600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35469932955006261419/35480000000000000000 : ℝ)*(X 0 2+X 1 2)+(1711761926831/709600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (5979/100000 : ℝ)) (hi := (20171/100000 : ℝ)) (c := (35469932955006261419/35480000000000000000 : ℝ)) (alpha := (1711761926831/709600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2123355169/10000000000 : ℝ)*X 0 0+(2749882399/5000000000 : ℝ)*X 0 1+(516869091/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((134283233/250000000 : ℝ)*X 1 0+(-1147544851/5000000000 : ℝ)*X 1 1+(5168695451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685665657/5000000000 : ℝ)*X 2 0+(2584346339/5000000000 : ℝ)*X 2 1+(-1147545341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271675603/625000000 : ℝ)*X 0 0+(4026083123/10000000000 : ℝ)*X 0 1+(586562851/1250000000 : ℝ)*X 0 2+(271675603/625000000 : ℝ)*X 1 0+(4026083123/10000000000 : ℝ)*X 1 1+(586562851/1250000000 : ℝ)*X 1 2+(271675603/625000000 : ℝ)*X 2 0+(4026083123/10000000000 : ℝ)*X 2 1+(586562851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-132715077/625000000 : ℝ)*X 0 0+(2585440583/5000000000 : ℝ)*X 0 1+(1374388597/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2114799/4000000 : ℝ)*X 1 0+(-983114541/5000000000 : ℝ)*X 1 1+(549755441/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643498837/5000000000 : ℝ)*X 2 0+(5497554431/10000000000 : ℝ)*X 2 1+(-1966228813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434698527/1000000000 : ℝ)*X 0 0+(234404837/500000000 : ℝ)*X 0 1+(2015265457/5000000000 : ℝ)*X 0 2+(434698527/1000000000 : ℝ)*X 1 0+(234404837/500000000 : ℝ)*X 1 1+(2015265457/5000000000 : ℝ)*X 1 2+(434698527/1000000000 : ℝ)*X 2 0+(234404837/500000000 : ℝ)*X 2 1+(2015265457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1279938710538462197000954553/221750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (965755919/100000000000000 : ℝ)*(base19) + (910270301/50000000000000 : ℝ)*(base23) + (119620923/100000000000000 : ℝ)*(upper2) + (77600541/12500000000000 : ℝ)*(upper3) + (65696469/25000000000000 : ℝ)*(upper4) + (282571286462557/12500000000000 : ℝ)*(major0) + (282571286462557/12500000000000 : ℝ)*(major1) + (282571286462557/12500000000000 : ℝ)*(major2) + (755129059625903/25000000000000 : ℝ)*(sp0) + (302055229160459/10000000000000 : ℝ)*(sp1) + (1510275718409953/50000000000000 : ℝ)*(sp2) + (1500567484916423/100000000000000 : ℝ)*(sp3) + (37018856897/100000000000000 : ℝ)*(sp4) + (19648724317/100000000000000 : ℝ)*(sp7) + (1500587133640741/100000000000000 : ℝ)*(f.failure) + (755138314340127/25000000000000 : ℝ)*(f.sum) + (11671437271603/4435000000000000000000000000 : ℝ)*base66 + (2384882756556038383/443500000000000000000000000000000 : ℝ)*base67 + (611714500447538383/443500000000000000000000000000000 : ℝ)*base69 + (720280632351538383/443500000000000000000000000000000 : ℝ)*base71 + (4255518939813/1108750000000000000000000000 : ℝ)*base73 + (2549481694518538383/443500000000000000000000000000000 : ℝ)*base75 + (914197599497538383/443500000000000000000000000000000 : ℝ)*base77 + (4723504384991038383/443500000000000000000000000000000 : ℝ)*base79 + (14487766352183/4435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1231963/250000000000000000000 : ℝ)*base89 + (1231963/250000000000000000000 : ℝ)*base91 + (1231963/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35142180656310462596853/3548000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1157680523/50000000000000 : ℝ)*(base19) + (497606241/20000000000000 : ℝ)*(base23) + (287748741/100000000000000 : ℝ)*(upper3) + (1881483/50000000000000 : ℝ)*(lower4) + (1630989/800000000000 : ℝ)*(upper5) + (229096182211477/10000000000000 : ℝ)*(major0) + (229096182211477/10000000000000 : ℝ)*(major1) + (229096182211477/10000000000000 : ℝ)*(major2) + (23154744823/100000000000000 : ℝ)*(sp1) + (13608549663/50000000000000 : ℝ)*(sp2) + (1530581002969699/50000000000000 : ℝ)*(sp4) + (3061136535833529/100000000000000 : ℝ)*(sp5) + (1530566150404433/50000000000000 : ℝ)*(sp6) + (760380654065303/50000000000000 : ℝ)*(sp7) + (760380654065303/50000000000000 : ℝ)*(f.failure) + (1530581002969699/50000000000000 : ℝ)*(f.sum) + (1592504677649/709600000000000000000000000 : ℝ)*base66 + (542914146464944137/354800000000000000000000000000000 : ℝ)*base68 + (278047000495055863/354800000000000000000000000000000 : ℝ)*base69 + (1035432949730544137/354800000000000000000000000000000 : ℝ)*base72 + (9651501210219/3548000000000000000000000000 : ℝ)*base73 + (2045444049422144137/354800000000000000000000000000000 : ℝ)*base76 + (484748740367055863/354800000000000000000000000000000 : ℝ)*base77 + (1017587718846255863/354800000000000000000000000000000 : ℝ)*base79 + (93515473173/141920000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (63671/125000000000000000000 : ℝ)*base90 + (63671/125000000000000000000 : ℝ)*base92 + (63671/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1202_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1202_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1202_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1202_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1202_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1202_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1202_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

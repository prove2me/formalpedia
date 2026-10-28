-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:50.445989+00:00
-- url     : https://prove2.me/submissions/efddf557-8444-46f0-94ac-e0073836370e

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
theorem support_rectangle_w1131_s0_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-947648733/5000000000 : ℝ)*x 0 + (189277371/312500000 : ℝ)*x 1 + (4779079467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947648733/5000000000 : ℝ)^2081 ≤ (86051271313/781250000000 : ℝ)^1569 := by
    have hnat : (947648733 : ℕ)^2081*781250000000^1569 ≤ 86051271313^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947648733 5000000000 86051271313 781250000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189277371/312500000 : ℝ)^2081 ≤ (803547478331/1562500000000 : ℝ)^1569 := by
    have hnat : (189277371 : ℕ)^2081*1562500000000^1569 ≤ 803547478331^1569*312500000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189277371 312500000 803547478331 1562500000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4779079467/10000000000 : ℝ)^2081 ≤ (586849978889/1562500000000 : ℝ)^1569 := by
    have hnat : (4779079467 : ℕ)^2081*1562500000000^1569 ≤ 586849978889^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779079467 10000000000 586849978889 1562500000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947648733/5000000000 : ℝ), (189277371/312500000 : ℝ), (4779079467/10000000000 : ℝ)] ![(86051271313/781250000000 : ℝ), (803547478331/1562500000000 : ℝ), (586849978889/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947648733/5000000000 : ℝ)|^2081 ≤ (86051271313/781250000000 : ℝ)^1569
        have hw : |(-947648733/5000000000 : ℝ)|=(947648733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(189277371/312500000 : ℝ)|^2081 ≤ (803547478331/1562500000000 : ℝ)^1569
        have hw : |(189277371/312500000 : ℝ)|=(189277371/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4779079467/10000000000 : ℝ)|^2081 ≤ (586849978889/1562500000000 : ℝ)^1569
        have hw : |(4779079467/10000000000 : ℝ)|=(4779079467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s0_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5517411833/10000000000 : ℝ)*x 0 + (-525783799/2000000000 : ℝ)*x 1 + (2389540059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517411833/10000000000 : ℝ)^2081 ≤ (45442043498771/100000000000000 : ℝ)^1569 := by
    have hnat : (5517411833 : ℕ)^2081*100000000000000^1569 ≤ 45442043498771^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517411833 10000000000 45442043498771 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525783799/2000000000 : ℝ)^2081 ≤ (3399910210441/20000000000000 : ℝ)^1569 := by
    have hnat : (525783799 : ℕ)^2081*20000000000000^1569 ≤ 3399910210441^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525783799 2000000000 3399910210441 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389540059/5000000000 : ℝ)^2081 ≤ (37558405434569/100000000000000 : ℝ)^1569 := by
    have hnat : (2389540059 : ℕ)^2081*100000000000000^1569 ≤ 37558405434569^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389540059 5000000000 37558405434569 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517411833/10000000000 : ℝ), (-525783799/2000000000 : ℝ), (2389540059/5000000000 : ℝ)] ![(45442043498771/100000000000000 : ℝ), (3399910210441/20000000000000 : ℝ), (37558405434569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517411833/10000000000 : ℝ)|^2081 ≤ (45442043498771/100000000000000 : ℝ)^1569
        have hw : |(5517411833/10000000000 : ℝ)|=(5517411833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525783799/2000000000 : ℝ)|^2081 ≤ (3399910210441/20000000000000 : ℝ)^1569
        have hw : |(-525783799/2000000000 : ℝ)|=(525783799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2389540059/5000000000 : ℝ)|^2081 ≤ (37558405434569/100000000000000 : ℝ)^1569
        have hw : |(2389540059/5000000000 : ℝ)|=(2389540059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s0_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1379354011/2500000000 : ℝ)*x 0 + (4779078447/10000000000 : ℝ)*x 1 + (-2628915663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379354011/2500000000 : ℝ)^2081 ≤ (4544208949867/10000000000000 : ℝ)^1569 := by
    have hnat : (1379354011 : ℕ)^2081*10000000000000^1569 ≤ 4544208949867^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379354011 2500000000 4544208949867 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4779078447/10000000000 : ℝ)^2081 ≤ (18779194008483/50000000000000 : ℝ)^1569 := by
    have hnat : (4779078447 : ℕ)^2081*50000000000000^1569 ≤ 18779194008483^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779078447 10000000000 18779194008483 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628915663/10000000000 : ℝ)^2081 ≤ (106247015471/625000000000 : ℝ)^1569 := by
    have hnat : (2628915663 : ℕ)^2081*625000000000^1569 ≤ 106247015471^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628915663 10000000000 106247015471 625000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379354011/2500000000 : ℝ), (4779078447/10000000000 : ℝ), (-2628915663/10000000000 : ℝ)] ![(4544208949867/10000000000000 : ℝ), (18779194008483/50000000000000 : ℝ), (106247015471/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379354011/2500000000 : ℝ)|^2081 ≤ (4544208949867/10000000000000 : ℝ)^1569
        have hw : |(1379354011/2500000000 : ℝ)|=(1379354011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4779078447/10000000000 : ℝ)|^2081 ≤ (18779194008483/50000000000000 : ℝ)^1569
        have hw : |(4779078447/10000000000 : ℝ)|=(4779078447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2628915663/10000000000 : ℝ)|^2081 ≤ (106247015471/625000000000 : ℝ)^1569
        have hw : |(-2628915663/10000000000 : ℝ)|=(2628915663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s0_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1050470651/2500000000 : ℝ)*x 0 + (1560796489/5000000000 : ℝ)*x 1 + (5658252949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050470651/2500000000 : ℝ)^2081 ≤ (3957994669103/12500000000000 : ℝ)^1569 := by
    have hnat : (1050470651 : ℕ)^2081*12500000000000^1569 ≤ 3957994669103^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050470651 2500000000 3957994669103 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560796489/5000000000 : ℝ)^2081 ≤ (5337278766373/25000000000000 : ℝ)^1569 := by
    have hnat : (1560796489 : ℕ)^2081*25000000000000^1569 ≤ 5337278766373^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560796489 5000000000 5337278766373 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5658252949/10000000000 : ℝ)^2081 ≤ (46986927559061/100000000000000 : ℝ)^1569 := by
    have hnat : (5658252949 : ℕ)^2081*100000000000000^1569 ≤ 46986927559061^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658252949 10000000000 46986927559061 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050470651/2500000000 : ℝ), (1560796489/5000000000 : ℝ), (5658252949/10000000000 : ℝ)] ![(3957994669103/12500000000000 : ℝ), (5337278766373/25000000000000 : ℝ), (46986927559061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050470651/2500000000 : ℝ)|^2081 ≤ (3957994669103/12500000000000 : ℝ)^1569
        have hw : |(1050470651/2500000000 : ℝ)|=(1050470651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560796489/5000000000 : ℝ)|^2081 ≤ (5337278766373/25000000000000 : ℝ)^1569
        have hw : |(1560796489/5000000000 : ℝ)|=(1560796489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5658252949/10000000000 : ℝ)|^2081 ≤ (46986927559061/100000000000000 : ℝ)^1569
        have hw : |(5658252949/10000000000 : ℝ)|=(5658252949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s0_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-59389847/312500000 : ℝ)*x 0 + (601506053/1250000000 : ℝ)*x 1 + (6022748877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59389847/312500000 : ℝ)^2081 ≤ (1381811186527/12500000000000 : ℝ)^1569 := by
    have hnat : (59389847 : ℕ)^2081*12500000000000^1569 ≤ 1381811186527^1569*312500000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59389847 312500000 1381811186527 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601506053/1250000000 : ℝ)^2081 ≤ (9475608875349/25000000000000 : ℝ)^1569 := by
    have hnat : (601506053 : ℕ)^2081*25000000000000^1569 ≤ 9475608875349^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601506053 1250000000 9475608875349 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6022748877/10000000000 : ℝ)^2081 ≤ (51043074988563/100000000000000 : ℝ)^1569 := by
    have hnat : (6022748877 : ℕ)^2081*100000000000000^1569 ≤ 51043074988563^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022748877 10000000000 51043074988563 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59389847/312500000 : ℝ), (601506053/1250000000 : ℝ), (6022748877/10000000000 : ℝ)] ![(1381811186527/12500000000000 : ℝ), (9475608875349/25000000000000 : ℝ), (51043074988563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59389847/312500000 : ℝ)|^2081 ≤ (1381811186527/12500000000000 : ℝ)^1569
        have hw : |(-59389847/312500000 : ℝ)|=(59389847/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601506053/1250000000 : ℝ)|^2081 ≤ (9475608875349/25000000000000 : ℝ)^1569
        have hw : |(601506053/1250000000 : ℝ)|=(601506053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6022748877/10000000000 : ℝ)|^2081 ≤ (51043074988563/100000000000000 : ℝ)^1569
        have hw : |(6022748877/10000000000 : ℝ)|=(6022748877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s0_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1292565487/2500000000 : ℝ)*x 0 + (-1385248559/10000000000 : ℝ)*x 1 + (602274879/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292565487/2500000000 : ℝ)^2081 ≤ (41689361670269/100000000000000 : ℝ)^1569 := by
    have hnat : (1292565487 : ℕ)^2081*100000000000000^1569 ≤ 41689361670269^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292565487 2500000000 41689361670269 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385248559/10000000000 : ℝ)^2081 ≤ (7267564312051/100000000000000 : ℝ)^1569 := by
    have hnat : (1385248559 : ℕ)^2081*100000000000000^1569 ≤ 7267564312051^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385248559 10000000000 7267564312051 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (602274879/1000000000 : ℝ)^2081 ≤ (51043074010627/100000000000000 : ℝ)^1569 := by
    have hnat : (602274879 : ℕ)^2081*100000000000000^1569 ≤ 51043074010627^1569*1000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602274879 1000000000 51043074010627 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292565487/2500000000 : ℝ), (-1385248559/10000000000 : ℝ), (602274879/1000000000 : ℝ)] ![(41689361670269/100000000000000 : ℝ), (7267564312051/100000000000000 : ℝ), (51043074010627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292565487/2500000000 : ℝ)|^2081 ≤ (41689361670269/100000000000000 : ℝ)^1569
        have hw : |(1292565487/2500000000 : ℝ)|=(1292565487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1385248559/10000000000 : ℝ)|^2081 ≤ (7267564312051/100000000000000 : ℝ)^1569
        have hw : |(-1385248559/10000000000 : ℝ)|=(1385248559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(602274879/1000000000 : ℝ)|^2081 ≤ (51043074010627/100000000000000 : ℝ)^1569
        have hw : |(602274879/1000000000 : ℝ)|=(602274879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s0_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (517026197/1000000000 : ℝ)*x 0 + (1505687197/2500000000 : ℝ)*x 1 + (-86578033/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517026197/1000000000 : ℝ)^2081 ≤ (41689361905549/100000000000000 : ℝ)^1569 := by
    have hnat : (517026197 : ℕ)^2081*100000000000000^1569 ≤ 41689361905549^1569*1000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517026197 1000000000 41689361905549 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1505687197/2500000000 : ℝ)^2081 ≤ (25521536994073/50000000000000 : ℝ)^1569 := by
    have hnat : (1505687197 : ℕ)^2081*50000000000000^1569 ≤ 25521536994073^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505687197 2500000000 25521536994073 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86578033/625000000 : ℝ)^2081 ≤ (363378204817/5000000000000 : ℝ)^1569 := by
    have hnat : (86578033 : ℕ)^2081*5000000000000^1569 ≤ 363378204817^1569*625000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86578033 625000000 363378204817 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517026197/1000000000 : ℝ), (1505687197/2500000000 : ℝ), (-86578033/625000000 : ℝ)] ![(41689361905549/100000000000000 : ℝ), (25521536994073/50000000000000 : ℝ), (363378204817/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517026197/1000000000 : ℝ)|^2081 ≤ (41689361905549/100000000000000 : ℝ)^1569
        have hw : |(517026197/1000000000 : ℝ)|=(517026197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1505687197/2500000000 : ℝ)|^2081 ≤ (25521536994073/50000000000000 : ℝ)^1569
        have hw : |(1505687197/2500000000 : ℝ)|=(1505687197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86578033/625000000 : ℝ)|^2081 ≤ (363378204817/5000000000000 : ℝ)^1569
        have hw : |(-86578033/625000000 : ℝ)|=(86578033/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s0_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2106080713/5000000000 : ℝ)*x 0 + (2796401817/5000000000 : ℝ)*x 1 + (637868491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106080713/5000000000 : ℝ)^2081 ≤ (6353346446193/20000000000000 : ℝ)^1569 := by
    have hnat : (2106080713 : ℕ)^2081*20000000000000^1569 ≤ 6353346446193^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106080713 5000000000 6353346446193 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796401817/5000000000 : ℝ)^2081 ≤ (46267434892329/100000000000000 : ℝ)^1569 := by
    have hnat : (2796401817 : ℕ)^2081*100000000000000^1569 ≤ 46267434892329^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796401817 5000000000 46267434892329 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637868491/2000000000 : ℝ)^2081 ≤ (4393166571627/20000000000000 : ℝ)^1569 := by
    have hnat : (637868491 : ℕ)^2081*20000000000000^1569 ≤ 4393166571627^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637868491 2000000000 4393166571627 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106080713/5000000000 : ℝ), (2796401817/5000000000 : ℝ), (637868491/2000000000 : ℝ)] ![(6353346446193/20000000000000 : ℝ), (46267434892329/100000000000000 : ℝ), (4393166571627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106080713/5000000000 : ℝ)|^2081 ≤ (6353346446193/20000000000000 : ℝ)^1569
        have hw : |(2106080713/5000000000 : ℝ)|=(2106080713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796401817/5000000000 : ℝ)|^2081 ≤ (46267434892329/100000000000000 : ℝ)^1569
        have hw : |(2796401817/5000000000 : ℝ)|=(2796401817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637868491/2000000000 : ℝ)|^2081 ≤ (4393166571627/20000000000000 : ℝ)^1569
        have hw : |(637868491/2000000000 : ℝ)|=(637868491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (23/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27857/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8323/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8323 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8323*1^2048 ≤ 0^2048*1^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8323/2048 : ℝ) ≤ (1207134880518719891/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8323 ≤ (1207134880518719891/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8323*50000000000000000000^2048 ≤ 1207134880518719891^2048*5^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1207134880518719891 50000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1207134880518719891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8323 := by
      have hnat : (1 : ℕ)^2048*1^8323 ≤ 1^8323*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51207134880518719891/50000000000000000000 : ℝ) ≤ (2011774720654041/2000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (51207134880518719891/50000000000000000000 : ℝ)^2048 ≤ (2011774720654041/2000000000000000 : ℝ)^8323 := by
      have hnat : (51207134880518719891 : ℕ)^2048*2000000000000000^8323 ≤ 2011774720654041^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51207134880518719891 50000000000000000000 2011774720654041 2000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011774720654041/2000000000000000 : ℝ)) (X := (51207134880518719891/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26207134880518719891/25000000000000000000 : ℝ) ≤ (1011774720654041/1000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (26207134880518719891/25000000000000000000 : ℝ)^2048 ≤ (1011774720654041/1000000000000000 : ℝ)^8323 := by
      have hnat : (26207134880518719891 : ℕ)^2048*1000000000000000^8323 ≤ 1011774720654041^8323*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26207134880518719891 25000000000000000000 1011774720654041 1000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011774720654041/1000000000000000 : ℝ)) (X := (26207134880518719891/25000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11774720654041/800000000000000 : ℝ)*(0 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11774720654041/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1207134880518719891/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11774720654041/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11774720654041/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011774720654041/2000000000000000 : ℝ) by norm_num, show 1+(1207134880518719891/50000000000000000000 : ℝ)+(0 : ℝ)=(51207134880518719891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1207134880518719891/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11774720654041/800000000000000 : ℝ)*(2/5 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11774720654041/800000000000000 : ℝ)*(2/5 : ℝ)=(1011774720654041/1000000000000000 : ℝ) by norm_num, show 1+2*(1207134880518719891/50000000000000000000 : ℝ)=(26207134880518719891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11774720654041/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11774720654041/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11774720654041/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11774720654041/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11774720654041/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11774720654041/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-947648733/5000000000 : ℝ)*X 0 0+(189277371/312500000 : ℝ)*X 0 1+(4779079467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5517411833/10000000000 : ℝ)*X 1 0+(-525783799/2000000000 : ℝ)*X 1 1+(2389540059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1379354011/2500000000 : ℝ)*X 2 0+(4779078447/10000000000 : ℝ)*X 2 1+(-2628915663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050470651/2500000000 : ℝ)*X 0 0+(1560796489/5000000000 : ℝ)*X 0 1+(5658252949/10000000000 : ℝ)*X 0 2+(1050470651/2500000000 : ℝ)*X 1 0+(1560796489/5000000000 : ℝ)*X 1 1+(5658252949/10000000000 : ℝ)*X 1 2+(1050470651/2500000000 : ℝ)*X 2 0+(1560796489/5000000000 : ℝ)*X 2 1+(5658252949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-59389847/312500000 : ℝ)*X 0 0+(601506053/1250000000 : ℝ)*X 0 1+(6022748877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292565487/2500000000 : ℝ)*X 1 0+(-1385248559/10000000000 : ℝ)*X 1 1+(602274879/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517026197/1000000000 : ℝ)*X 2 0+(1505687197/2500000000 : ℝ)*X 2 1+(-86578033/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2106080713/5000000000 : ℝ)*X 0 0+(2796401817/5000000000 : ℝ)*X 0 1+(637868491/2000000000 : ℝ)*X 0 2+(2106080713/5000000000 : ℝ)*X 1 0+(2796401817/5000000000 : ℝ)*X 1 1+(637868491/2000000000 : ℝ)*X 1 2+(2106080713/5000000000 : ℝ)*X 2 0+(2796401817/5000000000 : ℝ)*X 2 1+(637868491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (170680458766840854812583/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20105503/50000000000000 : ℝ)*(base1) + (600609447/50000000000000 : ℝ)*(base19) + (1402227407/100000000000000 : ℝ)*(base23) + (396288777/100000000000000 : ℝ)*(base24) + (2017903/625000000000 : ℝ)*(upper3) + (588412957767993/100000000000000 : ℝ)*(major0) + (588412957767993/100000000000000 : ℝ)*(major1) + (588412957767993/100000000000000 : ℝ)*(major2) + (48912543090253/6250000000000 : ℝ)*(sp0) + (391301074899027/50000000000000 : ℝ)*(sp1) + (195650388125191/25000000000000 : ℝ)*(sp2) + (78844007604021/20000000000000 : ℝ)*(sp3) + (1350891953/50000000000000 : ℝ)*(sp4) + (2344054207/100000000000000 : ℝ)*(sp7) + (394222422285319/100000000000000 : ℝ)*(f.failure) + (195650837754237/25000000000000 : ℝ)*(f.sum) + (57203935509713/40000000000000000000000000000 : ℝ)*base65 + (439889701669713/80000000000000000000000000000 : ℝ)*base67 + (170301791269713/80000000000000000000000000000 : ℝ)*base69 + (87436849189713/80000000000000000000000000000 : ℝ)*base71 + (125097487989713/40000000000000000000000000000 : ℝ)*base73 + (299409439749713/80000000000000000000000000000 : ℝ)*base75 + (65833921530287/80000000000000000000000000000 : ℝ)*base78 + (127700941029713/80000000000000000000000000000 : ℝ)*base79 + (63948756010287/40000000000000000000000000000 : ℝ)*base82 + (2571247/1000000000000000000000 : ℝ)*base89 + (2571247/1000000000000000000000 : ℝ)*base91 + (2571247/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113947282127906988098427/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20805753/50000000000000 : ℝ)*(base1) + (693866741/100000000000000 : ℝ)*(base19) + (174149769/25000000000000 : ℝ)*(base23) + (901329/1250000000000 : ℝ)*(upper3) + (16675489/20000000000000 : ℝ)*(upper5) + (621017455832849/100000000000000 : ℝ)*(major0) + (621017455832849/100000000000000 : ℝ)*(major1) + (621017455832849/100000000000000 : ℝ)*(major2) + (1379904707/100000000000000 : ℝ)*(sp1) + (171029737/12500000000000 : ℝ)*(sp2) + (103246026557471/12500000000000 : ℝ)*(sp4) + (412983048538407/50000000000000 : ℝ)*(sp5) + (825966106011291/100000000000000 : ℝ)*(sp6) + (83213320849971/20000000000000 : ℝ)*(sp7) + (208033322930681/50000000000000 : ℝ)*(f.failure) + (412984085424131/50000000000000 : ℝ)*(f.sum) + (33148558072809/40000000000000000000000000000 : ℝ)*base65 + (429145356232809/80000000000000000000000000000 : ℝ)*base67 + (247094312487191/80000000000000000000000000000 : ℝ)*base70 + (251877534247191/80000000000000000000000000000 : ℝ)*base72 + (135209549232809/40000000000000000000000000000 : ℝ)*base73 + (157829508487191/80000000000000000000000000000 : ℝ)*base76 + (361928341527191/80000000000000000000000000000 : ℝ)*base78 + (191573618807191/80000000000000000000000000000 : ℝ)*base80 + (65008320767191/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4636753/500000000000000000000 : ℝ)*base89 + (4636753/500000000000000000000 : ℝ)*base91 + (4636753/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1131_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (23/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27857/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1131_s1_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050379949/5000000000 : ℝ)*x 0 + (2852225909/5000000000 : ℝ)*x 1 + (4999962153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050379949/5000000000 : ℝ)^2081 ≤ (6312808318923/50000000000000 : ℝ)^1569 := by
    have hnat : (1050379949 : ℕ)^2081*50000000000000^1569 ≤ 6312808318923^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050379949 5000000000 6312808318923 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2852225909/5000000000 : ℝ)^2081 ≤ (47496437065319/100000000000000 : ℝ)^1569 := by
    have hnat : (2852225909 : ℕ)^2081*100000000000000^1569 ≤ 47496437065319^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852225909 5000000000 47496437065319 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999962153/10000000000 : ℝ)^2081 ≤ (39877946277037/100000000000000 : ℝ)^1569 := by
    have hnat : (4999962153 : ℕ)^2081*100000000000000^1569 ≤ 39877946277037^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999962153 10000000000 39877946277037 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050379949/5000000000 : ℝ), (2852225909/5000000000 : ℝ), (4999962153/10000000000 : ℝ)] ![(6312808318923/50000000000000 : ℝ), (47496437065319/100000000000000 : ℝ), (39877946277037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050379949/5000000000 : ℝ)|^2081 ≤ (6312808318923/50000000000000 : ℝ)^1569
        have hw : |(-1050379949/5000000000 : ℝ)|=(1050379949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2852225909/5000000000 : ℝ)|^2081 ≤ (47496437065319/100000000000000 : ℝ)^1569
        have hw : |(2852225909/5000000000 : ℝ)|=(2852225909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999962153/10000000000 : ℝ)|^2081 ≤ (39877946277037/100000000000000 : ℝ)^1569
        have hw : |(4999962153/10000000000 : ℝ)|=(4999962153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s1_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5419725141/10000000000 : ℝ)*x 0 + (-1240577323/5000000000 : ℝ)*x 1 + (4999961697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419725141/10000000000 : ℝ)^2081 ≤ (4437803389789/10000000000000 : ℝ)^1569 := by
    have hnat : (5419725141 : ℕ)^2081*10000000000000^1569 ≤ 4437803389789^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419725141 10000000000 4437803389789 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1240577323/5000000000 : ℝ)^2081 ≤ (15744024634083/100000000000000 : ℝ)^1569 := by
    have hnat : (1240577323 : ℕ)^2081*100000000000000^1569 ≤ 15744024634083^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240577323 5000000000 15744024634083 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999961697/10000000000 : ℝ)^2081 ≤ (1993897072667/5000000000000 : ℝ)^1569 := by
    have hnat : (4999961697 : ℕ)^2081*5000000000000^1569 ≤ 1993897072667^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999961697 10000000000 1993897072667 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419725141/10000000000 : ℝ), (-1240577323/5000000000 : ℝ), (4999961697/10000000000 : ℝ)] ![(4437803389789/10000000000000 : ℝ), (15744024634083/100000000000000 : ℝ), (1993897072667/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419725141/10000000000 : ℝ)|^2081 ≤ (4437803389789/10000000000000 : ℝ)^1569
        have hw : |(5419725141/10000000000 : ℝ)|=(5419725141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1240577323/5000000000 : ℝ)|^2081 ≤ (15744024634083/100000000000000 : ℝ)^1569
        have hw : |(-1240577323/5000000000 : ℝ)|=(1240577323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999961697/10000000000 : ℝ)|^2081 ≤ (1993897072667/5000000000000 : ℝ)^1569
        have hw : |(4999961697/10000000000 : ℝ)|=(4999961697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s1_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2709863441/5000000000 : ℝ)*x 0 + (4999960133/10000000000 : ℝ)*x 1 + (-496230873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709863441/5000000000 : ℝ)^2081 ≤ (44378052805591/100000000000000 : ℝ)^1569 := by
    have hnat : (2709863441 : ℕ)^2081*100000000000000^1569 ≤ 44378052805591^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709863441 5000000000 44378052805591 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4999960133/10000000000 : ℝ)^2081 ≤ (7975584981781/20000000000000 : ℝ)^1569 := by
    have hnat : (4999960133 : ℕ)^2081*20000000000000^1569 ≤ 7975584981781^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999960133 10000000000 7975584981781 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496230873/2000000000 : ℝ)^2081 ≤ (7872011134579/50000000000000 : ℝ)^1569 := by
    have hnat : (496230873 : ℕ)^2081*50000000000000^1569 ≤ 7872011134579^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496230873 2000000000 7872011134579 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709863441/5000000000 : ℝ), (4999960133/10000000000 : ℝ), (-496230873/2000000000 : ℝ)] ![(44378052805591/100000000000000 : ℝ), (7975584981781/20000000000000 : ℝ), (7872011134579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709863441/5000000000 : ℝ)|^2081 ≤ (44378052805591/100000000000000 : ℝ)^1569
        have hw : |(2709863441/5000000000 : ℝ)|=(2709863441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4999960133/10000000000 : ℝ)|^2081 ≤ (7975584981781/20000000000000 : ℝ)^1569
        have hw : |(4999960133/10000000000 : ℝ)|=(4999960133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496230873/2000000000 : ℝ)|^2081 ≤ (7872011134579/50000000000000 : ℝ)^1569
        have hw : |(-496230873/2000000000 : ℝ)|=(496230873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s1_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4318370133/10000000000 : ℝ)*x 0 + (1837489353/5000000000 : ℝ)*x 1 + (5073517203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318370133/10000000000 : ℝ)^2081 ≤ (32833450855767/100000000000000 : ℝ)^1569 := by
    have hnat : (4318370133 : ℕ)^2081*100000000000000^1569 ≤ 32833450855767^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318370133 10000000000 32833450855767 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1837489353/5000000000 : ℝ)^2081 ≤ (13254327590437/50000000000000 : ℝ)^1569 := by
    have hnat : (1837489353 : ℕ)^2081*50000000000000^1569 ≤ 13254327590437^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837489353 5000000000 13254327590437 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073517203/10000000000 : ℝ)^2081 ≤ (40657893948107/100000000000000 : ℝ)^1569 := by
    have hnat : (5073517203 : ℕ)^2081*100000000000000^1569 ≤ 40657893948107^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073517203 10000000000 40657893948107 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318370133/10000000000 : ℝ), (1837489353/5000000000 : ℝ), (5073517203/10000000000 : ℝ)] ![(32833450855767/100000000000000 : ℝ), (13254327590437/50000000000000 : ℝ), (40657893948107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318370133/10000000000 : ℝ)|^2081 ≤ (32833450855767/100000000000000 : ℝ)^1569
        have hw : |(4318370133/10000000000 : ℝ)|=(4318370133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1837489353/5000000000 : ℝ)|^2081 ≤ (13254327590437/50000000000000 : ℝ)^1569
        have hw : |(1837489353/5000000000 : ℝ)|=(1837489353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073517203/10000000000 : ℝ)|^2081 ≤ (40657893948107/100000000000000 : ℝ)^1569
        have hw : |(5073517203/10000000000 : ℝ)|=(5073517203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s1_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050790891/5000000000 : ℝ)*x 0 + (125240539/250000000 : ℝ)*x 1 + (1423650029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050790891/5000000000 : ℝ)^2081 ≤ (252643369641/2000000000000 : ℝ)^1569 := by
    have hnat : (1050790891 : ℕ)^2081*2000000000000^1569 ≤ 252643369641^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050790891 5000000000 252643369641 2000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125240539/250000000 : ℝ)^2081 ≤ (4997519802167/12500000000000 : ℝ)^1569 := by
    have hnat : (125240539 : ℕ)^2081*12500000000000^1569 ≤ 4997519802167^1569*250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125240539 250000000 4997519802167 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1423650029/2500000000 : ℝ)^2081 ≤ (473876730887/1000000000000 : ℝ)^1569 := by
    have hnat : (1423650029 : ℕ)^2081*1000000000000^1569 ≤ 473876730887^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423650029 2500000000 473876730887 1000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050790891/5000000000 : ℝ), (125240539/250000000 : ℝ), (1423650029/2500000000 : ℝ)] ![(252643369641/2000000000000 : ℝ), (4997519802167/12500000000000 : ℝ), (473876730887/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050790891/5000000000 : ℝ)|^2081 ≤ (252643369641/2000000000000 : ℝ)^1569
        have hw : |(-1050790891/5000000000 : ℝ)|=(1050790891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125240539/250000000 : ℝ)|^2081 ≤ (4997519802167/12500000000000 : ℝ)^1569
        have hw : |(125240539/250000000 : ℝ)|=(125240539/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1423650029/2500000000 : ℝ)|^2081 ≤ (473876730887/1000000000000 : ℝ)^1569
        have hw : |(1423650029/2500000000 : ℝ)|=(1423650029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s1_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5239206641/10000000000 : ℝ)*x 0 + (-893257837/5000000000 : ℝ)*x 1 + (5694600177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239206641/10000000000 : ℝ)^2081 ≤ (42428292439963/100000000000000 : ℝ)^1569 := by
    have hnat : (5239206641 : ℕ)^2081*100000000000000^1569 ≤ 42428292439963^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239206641 10000000000 42428292439963 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (893257837/5000000000 : ℝ)^2081 ≤ (10184033777731/100000000000000 : ℝ)^1569 := by
    have hnat : (893257837 : ℕ)^2081*100000000000000^1569 ≤ 10184033777731^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893257837 5000000000 10184033777731 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5694600177/10000000000 : ℝ)^2081 ≤ (23693836880979/50000000000000 : ℝ)^1569 := by
    have hnat : (5694600177 : ℕ)^2081*50000000000000^1569 ≤ 23693836880979^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5694600177 10000000000 23693836880979 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239206641/10000000000 : ℝ), (-893257837/5000000000 : ℝ), (5694600177/10000000000 : ℝ)] ![(42428292439963/100000000000000 : ℝ), (10184033777731/100000000000000 : ℝ), (23693836880979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239206641/10000000000 : ℝ)|^2081 ≤ (42428292439963/100000000000000 : ℝ)^1569
        have hw : |(5239206641/10000000000 : ℝ)|=(5239206641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-893257837/5000000000 : ℝ)|^2081 ≤ (10184033777731/100000000000000 : ℝ)^1569
        have hw : |(-893257837/5000000000 : ℝ)|=(893257837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5694600177/10000000000 : ℝ)|^2081 ≤ (23693836880979/50000000000000 : ℝ)^1569
        have hw : |(5694600177/10000000000 : ℝ)|=(5694600177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s1_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5239206591/10000000000 : ℝ)*x 0 + (5694600149/10000000000 : ℝ)*x 1 + (-893257893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239206591/10000000000 : ℝ)^2081 ≤ (1060707297573/2500000000000 : ℝ)^1569 := by
    have hnat : (5239206591 : ℕ)^2081*2500000000000^1569 ≤ 1060707297573^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239206591 10000000000 1060707297573 2500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5694600149/10000000000 : ℝ)^2081 ≤ (23693836726461/50000000000000 : ℝ)^1569 := by
    have hnat : (5694600149 : ℕ)^2081*50000000000000^1569 ≤ 23693836726461^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5694600149 10000000000 23693836726461 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893257893/5000000000 : ℝ)^2081 ≤ (1018403462453/10000000000000 : ℝ)^1569 := by
    have hnat : (893257893 : ℕ)^2081*10000000000000^1569 ≤ 1018403462453^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893257893 5000000000 1018403462453 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239206591/10000000000 : ℝ), (5694600149/10000000000 : ℝ), (-893257893/5000000000 : ℝ)] ![(1060707297573/2500000000000 : ℝ), (23693836726461/50000000000000 : ℝ), (1018403462453/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239206591/10000000000 : ℝ)|^2081 ≤ (1060707297573/2500000000000 : ℝ)^1569
        have hw : |(5239206591/10000000000 : ℝ)|=(5239206591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5694600149/10000000000 : ℝ)|^2081 ≤ (23693836726461/50000000000000 : ℝ)^1569
        have hw : |(5694600149/10000000000 : ℝ)|=(5694600149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893257893/5000000000 : ℝ)|^2081 ≤ (1018403462453/10000000000000 : ℝ)^1569
        have hw : |(-893257893/5000000000 : ℝ)|=(893257893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s1_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (863999693/2000000000 : ℝ)*x 0 + (2527171147/5000000000 : ℝ)*x 1 + (923633729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863999693/2000000000 : ℝ)^2081 ≤ (8212468114017/25000000000000 : ℝ)^1569 := by
    have hnat : (863999693 : ℕ)^2081*25000000000000^1569 ≤ 8212468114017^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863999693 2000000000 8212468114017 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2527171147/5000000000 : ℝ)^2081 ≤ (40454213158471/100000000000000 : ℝ)^1569 := by
    have hnat : (2527171147 : ℕ)^2081*100000000000000^1569 ≤ 40454213158471^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527171147 5000000000 40454213158471 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923633729/2500000000 : ℝ)^2081 ≤ (2669591438057/10000000000000 : ℝ)^1569 := by
    have hnat : (923633729 : ℕ)^2081*10000000000000^1569 ≤ 2669591438057^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923633729 2500000000 2669591438057 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863999693/2000000000 : ℝ), (2527171147/5000000000 : ℝ), (923633729/2500000000 : ℝ)] ![(8212468114017/25000000000000 : ℝ), (40454213158471/100000000000000 : ℝ), (2669591438057/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863999693/2000000000 : ℝ)|^2081 ≤ (8212468114017/25000000000000 : ℝ)^1569
        have hw : |(863999693/2000000000 : ℝ)|=(863999693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2527171147/5000000000 : ℝ)|^2081 ≤ (40454213158471/100000000000000 : ℝ)^1569
        have hw : |(2527171147/5000000000 : ℝ)|=(2527171147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(923633729/2500000000 : ℝ)|^2081 ≤ (2669591438057/10000000000000 : ℝ)^1569
        have hw : |(923633729/2500000000 : ℝ)|=(923633729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27857/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1397/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20487/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27857/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (23/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27857/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (23/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27857/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (23/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27857/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (23/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27857/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (23/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27857/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (23/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (23/6250 : ℝ) ^ (8323/2048 : ℝ) ≤ (12814188573/100000000000000000000 : ℝ) := by
    have hpowers : (23/6250 : ℝ)^8323 ≤ (12814188573/100000000000000000000 : ℝ)^2048 := by
      have hnat : (23 : ℕ)^8323*100000000000000000000^2048 ≤ 12814188573^2048*6250^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23 6250 12814188573 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23/6250 : ℝ)) (X := (12814188573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27857/100000 : ℝ) ^ (8323/2048 : ℝ) ≤ (277461476583032673/50000000000000000000 : ℝ) := by
    have hpowers : (27857/100000 : ℝ)^8323 ≤ (277461476583032673/50000000000000000000 : ℝ)^2048 := by
      have hnat : (27857 : ℕ)^8323*50000000000000000000^2048 ≤ 277461476583032673^2048*100000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27857 100000 277461476583032673 50000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27857/100000 : ℝ)) (X := (277461476583032673/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000012814188573/50000000000000000000 : ℝ) ≤ (16000000001009/16000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50000000012814188573/50000000000000000000 : ℝ)^2048 ≤ (16000000001009/16000000000000 : ℝ)^8323 := by
      have hnat : (50000000012814188573 : ℕ)^2048*16000000000000^8323 ≤ 16000000001009^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000012814188573 50000000000000000000 16000000001009 16000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16000000001009/16000000000000 : ℝ)) (X := (50000000012814188573/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100554922965980253919/100000000000000000000 : ℝ) ≤ (10013626246963751/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (100554922965980253919/100000000000000000000 : ℝ)^2048 ≤ (10013626246963751/10000000000000000 : ℝ)^8323 := by
      have hnat : (100554922965980253919 : ℕ)^2048*10000000000000000^8323 ≤ 10013626246963751^8323*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100554922965980253919 100000000000000000000 10013626246963751 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013626246963751/10000000000000000 : ℝ)) (X := (100554922965980253919/100000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25277461476583032673/25000000000000000000 : ℝ) ≤ (10027252493296877/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (25277461476583032673/25000000000000000000 : ℝ)^2048 ≤ (10027252493296877/10000000000000000 : ℝ)^8323 := by
      have hnat : (25277461476583032673 : ℕ)^2048*10000000000000000^8323 ≤ 10027252493296877^8323*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25277461476583032673 25000000000000000000 10027252493296877 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027252493296877/10000000000000000 : ℝ)) (X := (25277461476583032673/25000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12814188573/100000000000000000000 : ℝ) ≤ ((13089522433334955709/13090000000000000000 : ℝ)+2*(324434436503/65450000000000 : ℝ)*(23/6250 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (13089522433334955709/13090000000000000000 : ℝ)+2*(324434436503/65450000000000 : ℝ)*(23/6250 : ℝ)=(16000000001009/16000000000000 : ℝ) by norm_num, show 1+2*(12814188573/100000000000000000000 : ℝ)=(50000000012814188573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(277461476583032673/50000000000000000000 : ℝ)+(12814188573/100000000000000000000 : ℝ) ≤ ((13089522433334955709/13090000000000000000 : ℝ)+(324434436503/65450000000000 : ℝ)*((27857/100000 : ℝ)+(23/6250 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (13089522433334955709/13090000000000000000 : ℝ)+(324434436503/65450000000000 : ℝ)*((27857/100000 : ℝ)+(23/6250 : ℝ))=(10013626246963751/10000000000000000 : ℝ) by norm_num, show 1+(277461476583032673/50000000000000000000 : ℝ)+(12814188573/100000000000000000000 : ℝ)=(100554922965980253919/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(277461476583032673/50000000000000000000 : ℝ) ≤ ((13089522433334955709/13090000000000000000 : ℝ)+2*(324434436503/65450000000000 : ℝ)*(27857/100000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (13089522433334955709/13090000000000000000 : ℝ)+2*(324434436503/65450000000000 : ℝ)*(27857/100000 : ℝ)=(10027252493296877/10000000000000000 : ℝ) by norm_num, show 1+2*(277461476583032673/50000000000000000000 : ℝ)=(25277461476583032673/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13089522433334955709/13090000000000000000 : ℝ)*(X 1 0+X 2 0)+(324434436503/65450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (23/6250 : ℝ)) (hi := (27857/100000 : ℝ)) (c := (13089522433334955709/13090000000000000000 : ℝ)) (alpha := (324434436503/65450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13089522433334955709/13090000000000000000 : ℝ)*(X 0 1+X 2 1)+(324434436503/65450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (23/6250 : ℝ)) (hi := (27857/100000 : ℝ)) (c := (13089522433334955709/13090000000000000000 : ℝ)) (alpha := (324434436503/65450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13089522433334955709/13090000000000000000 : ℝ)*(X 0 2+X 1 2)+(324434436503/65450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (23/6250 : ℝ)) (hi := (27857/100000 : ℝ)) (c := (13089522433334955709/13090000000000000000 : ℝ)) (alpha := (324434436503/65450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050379949/5000000000 : ℝ)*X 0 0+(2852225909/5000000000 : ℝ)*X 0 1+(4999962153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5419725141/10000000000 : ℝ)*X 1 0+(-1240577323/5000000000 : ℝ)*X 1 1+(4999961697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2709863441/5000000000 : ℝ)*X 2 0+(4999960133/10000000000 : ℝ)*X 2 1+(-496230873/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318370133/10000000000 : ℝ)*X 0 0+(1837489353/5000000000 : ℝ)*X 0 1+(5073517203/10000000000 : ℝ)*X 0 2+(4318370133/10000000000 : ℝ)*X 1 0+(1837489353/5000000000 : ℝ)*X 1 1+(5073517203/10000000000 : ℝ)*X 1 2+(4318370133/10000000000 : ℝ)*X 2 0+(1837489353/5000000000 : ℝ)*X 2 1+(5073517203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1050790891/5000000000 : ℝ)*X 0 0+(125240539/250000000 : ℝ)*X 0 1+(1423650029/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5239206641/10000000000 : ℝ)*X 1 0+(-893257837/5000000000 : ℝ)*X 1 1+(5694600177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239206591/10000000000 : ℝ)*X 2 0+(5694600149/10000000000 : ℝ)*X 2 1+(-893257893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863999693/2000000000 : ℝ)*X 0 0+(2527171147/5000000000 : ℝ)*X 0 1+(923633729/2500000000 : ℝ)*X 0 2+(863999693/2000000000 : ℝ)*X 1 0+(2527171147/5000000000 : ℝ)*X 1 1+(923633729/2500000000 : ℝ)*X 1 2+(863999693/2000000000 : ℝ)*X 2 0+(2527171147/5000000000 : ℝ)*X 2 1+(923633729/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (244589287391627447208858333/59500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (386239541/100000000000000 : ℝ)*(base1) + (103921867/20000000000000 : ℝ)*(base19) + (129182261/12500000000000 : ℝ)*(base23) + (20320483/100000000000000 : ℝ)*(base37) + (54150233/100000000000000 : ℝ)*(upper3) + (1067250092392077/100000000000000 : ℝ)*(major0) + (1067250092392077/100000000000000 : ℝ)*(major1) + (1067250092392077/100000000000000 : ℝ)*(major2) + (1419467749463559/100000000000000 : ℝ)*(sp0) + (283893218458903/20000000000000 : ℝ)*(sp1) + (709733657905061/50000000000000 : ℝ)*(sp2) + (715031291931101/100000000000000 : ℝ)*(sp3) + (30813881/3125000000000 : ℝ)*(sp4) + (1737364359/100000000000000 : ℝ)*(sp5) + (5720253587929/800000000000 : ℝ)*(f.failure) + (141946834926821/10000000000000 : ℝ)*(f.sum) + (515721255377/595000000000000000000000000 : ℝ)*base65 + (140890886528337963/119000000000000000000000000000000 : ℝ)*base67 + (799326905062337963/119000000000000000000000000000000 : ℝ)*base69 + (790714058127337963/119000000000000000000000000000000 : ℝ)*base71 + (132953929677/148750000000000000000000000 : ℝ)*base74 + (1165719015881337963/119000000000000000000000000000000 : ℝ)*base75 + (198130963597337963/119000000000000000000000000000000 : ℝ)*base77 + (190920099692337963/119000000000000000000000000000000 : ℝ)*base79 + (4226017099107/595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (55823/8000000000000000000 : ℝ)*base90 + (55823/8000000000000000000 : ℝ)*base92 + (55823/8000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7034431103392381278054387/1375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47895441/100000000000000 : ℝ)*(base1) + (1099308953/100000000000000 : ℝ)*(base19) + (43025177/4000000000000 : ℝ)*(base23) + (23659069/20000000000000 : ℝ)*(upper3) + (24890841/20000000000000 : ℝ)*(upper5) + (548824530441661/50000000000000 : ℝ)*(major0) + (548824530441661/50000000000000 : ℝ)*(major1) + (548824530441661/50000000000000 : ℝ)*(major2) + (4846146193/100000000000000 : ℝ)*(sp1) + (4563210219/100000000000000 : ℝ)*(sp2) + (729949864214719/50000000000000 : ℝ)*(sp4) + (364973433769713/25000000000000 : ℝ)*(sp5) + (1459894041694353/100000000000000 : ℝ)*(sp6) + (22981194462673/3125000000000 : ℝ)*(sp7) + (45962391918811/6250000000000 : ℝ)*(f.failure) + (729949840266999/50000000000000 : ℝ)*(f.sum) + (10105941117/12031250000000000000000000 : ℝ)*base66 + (6702267125925173/3500000000000000000000000000000 : ℝ)*base68 + (5284928654074827/3500000000000000000000000000000 : ℝ)*base69 + (945324850574827/3500000000000000000000000000000 : ℝ)*base71 + (569958092667/192500000000000000000000000 : ℝ)*base74 + (10052238344574827/3500000000000000000000000000000 : ℝ)*base75 + (1099697824574827/3500000000000000000000000000000 : ℝ)*base77 + (25634322320074827/3500000000000000000000000000000 : ℝ)*base79 + (1857183476459/385000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (200557/62500000000000000000 : ℝ)*base90 + (200557/62500000000000000000 : ℝ)*base92 + (200557/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1131_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27857/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1397/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20487/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1131_s2_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154583143/10000000000 : ℝ)*x 0 + (5512909109/10000000000 : ℝ)*x 1 + (2578645449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154583143/10000000000 : ℝ)^2081 ≤ (2611287477519/20000000000000 : ℝ)^1569 := by
    have hnat : (2154583143 : ℕ)^2081*20000000000000^1569 ≤ 2611287477519^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154583143 10000000000 2611287477519 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512909109/10000000000 : ℝ)^2081 ≤ (9078572687351/20000000000000 : ℝ)^1569 := by
    have hnat : (5512909109 : ℕ)^2081*20000000000000^1569 ≤ 9078572687351^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512909109 10000000000 9078572687351 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578645449/5000000000 : ℝ)^2081 ≤ (41550699159517/100000000000000 : ℝ)^1569 := by
    have hnat : (2578645449 : ℕ)^2081*100000000000000^1569 ≤ 41550699159517^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578645449 5000000000 41550699159517 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154583143/10000000000 : ℝ), (5512909109/10000000000 : ℝ), (2578645449/5000000000 : ℝ)] ![(2611287477519/20000000000000 : ℝ), (9078572687351/20000000000000 : ℝ), (41550699159517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154583143/10000000000 : ℝ)|^2081 ≤ (2611287477519/20000000000000 : ℝ)^1569
        have hw : |(-2154583143/10000000000 : ℝ)|=(2154583143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512909109/10000000000 : ℝ)|^2081 ≤ (9078572687351/20000000000000 : ℝ)^1569
        have hw : |(5512909109/10000000000 : ℝ)|=(5512909109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2578645449/5000000000 : ℝ)|^2081 ≤ (41550699159517/100000000000000 : ℝ)^1569
        have hw : |(2578645449/5000000000 : ℝ)|=(2578645449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s2_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671792127/1250000000 : ℝ)*x 0 + (-467909791/2000000000 : ℝ)*x 1 + (5157292641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671792127/1250000000 : ℝ)^2081 ≤ (21942891100743/50000000000000 : ℝ)^1569 := by
    have hnat : (671792127 : ℕ)^2081*50000000000000^1569 ≤ 21942891100743^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671792127 1250000000 21942891100743 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467909791/2000000000 : ℝ)^2081 ≤ (7281749998911/50000000000000 : ℝ)^1569 := by
    have hnat : (467909791 : ℕ)^2081*50000000000000^1569 ≤ 7281749998911^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467909791 2000000000 7281749998911 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5157292641/10000000000 : ℝ)^2081 ≤ (2596919861551/6250000000000 : ℝ)^1569 := by
    have hnat : (5157292641 : ℕ)^2081*6250000000000^1569 ≤ 2596919861551^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157292641 10000000000 2596919861551 6250000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671792127/1250000000 : ℝ), (-467909791/2000000000 : ℝ), (5157292641/10000000000 : ℝ)] ![(21942891100743/50000000000000 : ℝ), (7281749998911/50000000000000 : ℝ), (2596919861551/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671792127/1250000000 : ℝ)|^2081 ≤ (21942891100743/50000000000000 : ℝ)^1569
        have hw : |(671792127/1250000000 : ℝ)|=(671792127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-467909791/2000000000 : ℝ)|^2081 ≤ (7281749998911/50000000000000 : ℝ)^1569
        have hw : |(-467909791/2000000000 : ℝ)|=(467909791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5157292641/10000000000 : ℝ)|^2081 ≤ (2596919861551/6250000000000 : ℝ)^1569
        have hw : |(5157292641/10000000000 : ℝ)|=(5157292641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s2_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2687168473/5000000000 : ℝ)*x 0 + (5157292641/10000000000 : ℝ)*x 1 + (-2339549047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687168473/5000000000 : ℝ)^2081 ≤ (5485722680419/12500000000000 : ℝ)^1569 := by
    have hnat : (2687168473 : ℕ)^2081*12500000000000^1569 ≤ 5485722680419^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687168473 5000000000 5485722680419 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5157292641/10000000000 : ℝ)^2081 ≤ (2596919861551/6250000000000 : ℝ)^1569 := by
    have hnat : (5157292641 : ℕ)^2081*6250000000000^1569 ≤ 2596919861551^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157292641 10000000000 2596919861551 6250000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2339549047/10000000000 : ℝ)^2081 ≤ (14563500757397/100000000000000 : ℝ)^1569 := by
    have hnat : (2339549047 : ℕ)^2081*100000000000000^1569 ≤ 14563500757397^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339549047 10000000000 14563500757397 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687168473/5000000000 : ℝ), (5157292641/10000000000 : ℝ), (-2339549047/10000000000 : ℝ)] ![(5485722680419/12500000000000 : ℝ), (2596919861551/6250000000000 : ℝ), (14563500757397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687168473/5000000000 : ℝ)|^2081 ≤ (5485722680419/12500000000000 : ℝ)^1569
        have hw : |(2687168473/5000000000 : ℝ)|=(2687168473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5157292641/10000000000 : ℝ)|^2081 ≤ (2596919861551/6250000000000 : ℝ)^1569
        have hw : |(5157292641/10000000000 : ℝ)|=(5157292641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2339549047/10000000000 : ℝ)|^2081 ≤ (14563500757397/100000000000000 : ℝ)^1569
        have hw : |(-2339549047/10000000000 : ℝ)|=(2339549047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s2_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (544408497/1250000000 : ℝ)*x 0 + (2008248961/5000000000 : ℝ)*x 1 + (4722460749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544408497/1250000000 : ℝ)^2081 ≤ (33206057556041/100000000000000 : ℝ)^1569 := by
    have hnat : (544408497 : ℕ)^2081*100000000000000^1569 ≤ 33206057556041^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544408497 1250000000 33206057556041 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008248961/5000000000 : ℝ)^2081 ≤ (14912281476543/50000000000000 : ℝ)^1569 := by
    have hnat : (2008248961 : ℕ)^2081*50000000000000^1569 ≤ 14912281476543^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008248961 5000000000 14912281476543 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4722460749/10000000000 : ℝ)^2081 ≤ (1478775179177/4000000000000 : ℝ)^1569 := by
    have hnat : (4722460749 : ℕ)^2081*4000000000000^1569 ≤ 1478775179177^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4722460749 10000000000 1478775179177 4000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544408497/1250000000 : ℝ), (2008248961/5000000000 : ℝ), (4722460749/10000000000 : ℝ)] ![(33206057556041/100000000000000 : ℝ), (14912281476543/50000000000000 : ℝ), (1478775179177/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544408497/1250000000 : ℝ)|^2081 ≤ (33206057556041/100000000000000 : ℝ)^1569
        have hw : |(544408497/1250000000 : ℝ)|=(544408497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008248961/5000000000 : ℝ)|^2081 ≤ (14912281476543/50000000000000 : ℝ)^1569
        have hw : |(2008248961/5000000000 : ℝ)|=(2008248961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4722460749/10000000000 : ℝ)|^2081 ≤ (1478775179177/4000000000000 : ℝ)^1569
        have hw : |(4722460749/10000000000 : ℝ)|=(4722460749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s2_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077344427/5000000000 : ℝ)*x 0 + (5159762149/10000000000 : ℝ)*x 1 + (5510412877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077344427/5000000000 : ℝ)^2081 ≤ (652864351309/5000000000000 : ℝ)^1569 := by
    have hnat : (1077344427 : ℕ)^2081*5000000000000^1569 ≤ 652864351309^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077344427 5000000000 652864351309 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5159762149/10000000000 : ℝ)^2081 ≤ (41577108445011/100000000000000 : ℝ)^1569 := by
    have hnat : (5159762149 : ℕ)^2081*100000000000000^1569 ≤ 41577108445011^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159762149 10000000000 41577108445011 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510412877/10000000000 : ℝ)^2081 ≤ (45365604510781/100000000000000 : ℝ)^1569 := by
    have hnat : (5510412877 : ℕ)^2081*100000000000000^1569 ≤ 45365604510781^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510412877 10000000000 45365604510781 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077344427/5000000000 : ℝ), (5159762149/10000000000 : ℝ), (5510412877/10000000000 : ℝ)] ![(652864351309/5000000000000 : ℝ), (41577108445011/100000000000000 : ℝ), (45365604510781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077344427/5000000000 : ℝ)|^2081 ≤ (652864351309/5000000000000 : ℝ)^1569
        have hw : |(-1077344427/5000000000 : ℝ)|=(1077344427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5159762149/10000000000 : ℝ)|^2081 ≤ (41577108445011/100000000000000 : ℝ)^1569
        have hw : |(5159762149/10000000000 : ℝ)|=(5159762149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510412877/10000000000 : ℝ)|^2081 ≤ (45365604510781/100000000000000 : ℝ)^1569
        have hw : |(5510412877/10000000000 : ℝ)|=(5510412877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s2_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642086859/5000000000 : ℝ)*x 0 + (-993213457/5000000000 : ℝ)*x 1 + (5510413461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642086859/5000000000 : ℝ)^2081 ≤ (42911952701263/100000000000000 : ℝ)^1569 := by
    have hnat : (2642086859 : ℕ)^2081*100000000000000^1569 ≤ 42911952701263^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642086859 5000000000 42911952701263 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993213457/5000000000 : ℝ)^2081 ≤ (11722436394653/100000000000000 : ℝ)^1569 := by
    have hnat : (993213457 : ℕ)^2081*100000000000000^1569 ≤ 11722436394653^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993213457 5000000000 11722436394653 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510413461/10000000000 : ℝ)^2081 ≤ (45365610887607/100000000000000 : ℝ)^1569 := by
    have hnat : (5510413461 : ℕ)^2081*100000000000000^1569 ≤ 45365610887607^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510413461 10000000000 45365610887607 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642086859/5000000000 : ℝ), (-993213457/5000000000 : ℝ), (5510413461/10000000000 : ℝ)] ![(42911952701263/100000000000000 : ℝ), (11722436394653/100000000000000 : ℝ), (45365610887607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642086859/5000000000 : ℝ)|^2081 ≤ (42911952701263/100000000000000 : ℝ)^1569
        have hw : |(2642086859/5000000000 : ℝ)|=(2642086859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993213457/5000000000 : ℝ)|^2081 ≤ (11722436394653/100000000000000 : ℝ)^1569
        have hw : |(-993213457/5000000000 : ℝ)|=(993213457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510413461/10000000000 : ℝ)|^2081 ≤ (45365610887607/100000000000000 : ℝ)^1569
        have hw : |(5510413461/10000000000 : ℝ)|=(5510413461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s2_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660521551/1250000000 : ℝ)*x 0 + (2755206657/5000000000 : ℝ)*x 1 + (-993214461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660521551/1250000000 : ℝ)^2081 ≤ (21455969295719/50000000000000 : ℝ)^1569 := by
    have hnat : (660521551 : ℕ)^2081*50000000000000^1569 ≤ 21455969295719^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660521551 1250000000 21455969295719 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755206657/5000000000 : ℝ)^2081 ≤ (45365609282481/100000000000000 : ℝ)^1569 := by
    have hnat : (2755206657 : ℕ)^2081*100000000000000^1569 ≤ 45365609282481^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755206657 5000000000 45365609282481 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (993214461/5000000000 : ℝ)^2081 ≤ (11722452111239/100000000000000 : ℝ)^1569 := by
    have hnat : (993214461 : ℕ)^2081*100000000000000^1569 ≤ 11722452111239^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993214461 5000000000 11722452111239 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660521551/1250000000 : ℝ), (2755206657/5000000000 : ℝ), (-993214461/5000000000 : ℝ)] ![(21455969295719/50000000000000 : ℝ), (45365609282481/100000000000000 : ℝ), (11722452111239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660521551/1250000000 : ℝ)|^2081 ≤ (21455969295719/50000000000000 : ℝ)^1569
        have hw : |(660521551/1250000000 : ℝ)|=(660521551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755206657/5000000000 : ℝ)|^2081 ≤ (45365609282481/100000000000000 : ℝ)^1569
        have hw : |(2755206657/5000000000 : ℝ)|=(2755206657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-993214461/5000000000 : ℝ)|^2081 ≤ (11722452111239/100000000000000 : ℝ)^1569
        have hw : |(-993214461/5000000000 : ℝ)|=(993214461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s2_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4355477253/10000000000 : ℝ)*x 0 + (2358778149/5000000000 : ℝ)*x 1 + (4021451727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355477253/10000000000 : ℝ)^2081 ≤ (16604086926181/50000000000000 : ℝ)^1569 := by
    have hnat : (4355477253 : ℕ)^2081*50000000000000^1569 ≤ 16604086926181^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355477253 10000000000 16604086926181 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2358778149/5000000000 : ℝ)^2081 ≤ (4614808148171/12500000000000 : ℝ)^1569 := by
    have hnat : (2358778149 : ℕ)^2081*12500000000000^1569 ≤ 4614808148171^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358778149 5000000000 4614808148171 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021451727/10000000000 : ℝ)^2081 ≤ (7468340236193/25000000000000 : ℝ)^1569 := by
    have hnat : (4021451727 : ℕ)^2081*25000000000000^1569 ≤ 7468340236193^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021451727 10000000000 7468340236193 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355477253/10000000000 : ℝ), (2358778149/5000000000 : ℝ), (4021451727/10000000000 : ℝ)] ![(16604086926181/50000000000000 : ℝ), (4614808148171/12500000000000 : ℝ), (7468340236193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355477253/10000000000 : ℝ)|^2081 ≤ (16604086926181/50000000000000 : ℝ)^1569
        have hw : |(4355477253/10000000000 : ℝ)|=(4355477253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2358778149/5000000000 : ℝ)|^2081 ≤ (4614808148171/12500000000000 : ℝ)^1569
        have hw : |(2358778149/5000000000 : ℝ)|=(2358778149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021451727/10000000000 : ℝ)|^2081 ≤ (7468340236193/25000000000000 : ℝ)^1569
        have hw : |(4021451727/10000000000 : ℝ)|=(4021451727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1397/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (451/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3307/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1397/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1397/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1397/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1397/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1397/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1397/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1397/25000 : ℝ) ^ (8323/2048 : ℝ) ≤ (810763223970787/100000000000000000000 : ℝ) := by
    have hpowers : (1397/25000 : ℝ)^8323 ≤ (810763223970787/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1397 : ℕ)^8323*100000000000000000000^2048 ≤ 810763223970787^2048*25000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1397 25000 810763223970787 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1397/25000 : ℝ)) (X := (810763223970787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20487/100000 : ℝ) ^ (8323/2048 : ℝ) ≤ (159174059004181001/100000000000000000000 : ℝ) := by
    have hpowers : (20487/100000 : ℝ)^8323 ≤ (159174059004181001/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20487 : ℕ)^8323*100000000000000000000^2048 ≤ 159174059004181001^2048*100000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20487 100000 159174059004181001 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20487/100000 : ℝ)) (X := (159174059004181001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000810763223970787/50000000000000000000 : ℝ) ≤ (10000039899866229/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50000810763223970787/50000000000000000000 : ℝ)^2048 ≤ (10000039899866229/10000000000000000 : ℝ)^8323 := by
      have hnat : (50000810763223970787 : ℕ)^2048*10000000000000000^8323 ≤ 10000039899866229^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000810763223970787 50000000000000000000 10000039899866229 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039899866229/10000000000000000 : ℝ)) (X := (50000810763223970787/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25039996205557037947/25000000000000000000 : ℝ) ≤ (5001967148255049/5000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (25039996205557037947/25000000000000000000 : ℝ)^2048 ≤ (5001967148255049/5000000000000000 : ℝ)^8323 := by
      have hnat : (25039996205557037947 : ℕ)^2048*5000000000000000^8323 ≤ 5001967148255049^8323*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25039996205557037947 25000000000000000000 5001967148255049 5000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001967148255049/5000000000000000 : ℝ)) (X := (25039996205557037947/25000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50159174059004181001/50000000000000000000 : ℝ) ≤ (10007828693153967/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50159174059004181001/50000000000000000000 : ℝ)^2048 ≤ (10007828693153967/10000000000000000 : ℝ)^8323 := by
      have hnat : (50159174059004181001 : ℕ)^2048*10000000000000000^8323 ≤ 10007828693153967^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50159174059004181001 50000000000000000000 10007828693153967 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007828693153967/10000000000000000 : ℝ)) (X := (50159174059004181001/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(810763223970787/100000000000000000000 : ℝ) ≤ ((148947070691215065927/148990000000000000000 : ℝ)+2*(3894396643869/1489900000000000 : ℝ)*(1397/25000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (148947070691215065927/148990000000000000000 : ℝ)+2*(3894396643869/1489900000000000 : ℝ)*(1397/25000 : ℝ)=(10000039899866229/10000000000000000 : ℝ) by norm_num, show 1+2*(810763223970787/100000000000000000000 : ℝ)=(50000810763223970787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(159174059004181001/100000000000000000000 : ℝ)+(810763223970787/100000000000000000000 : ℝ) ≤ ((148947070691215065927/148990000000000000000 : ℝ)+(3894396643869/1489900000000000 : ℝ)*((20487/100000 : ℝ)+(1397/25000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (148947070691215065927/148990000000000000000 : ℝ)+(3894396643869/1489900000000000 : ℝ)*((20487/100000 : ℝ)+(1397/25000 : ℝ))=(5001967148255049/5000000000000000 : ℝ) by norm_num, show 1+(159174059004181001/100000000000000000000 : ℝ)+(810763223970787/100000000000000000000 : ℝ)=(25039996205557037947/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(159174059004181001/100000000000000000000 : ℝ) ≤ ((148947070691215065927/148990000000000000000 : ℝ)+2*(3894396643869/1489900000000000 : ℝ)*(20487/100000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (148947070691215065927/148990000000000000000 : ℝ)+2*(3894396643869/1489900000000000 : ℝ)*(20487/100000 : ℝ)=(10007828693153967/10000000000000000 : ℝ) by norm_num, show 1+2*(159174059004181001/100000000000000000000 : ℝ)=(50159174059004181001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (148947070691215065927/148990000000000000000 : ℝ)*(X 1 0+X 2 0)+(3894396643869/1489900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (1397/25000 : ℝ)) (hi := (20487/100000 : ℝ)) (c := (148947070691215065927/148990000000000000000 : ℝ)) (alpha := (3894396643869/1489900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (148947070691215065927/148990000000000000000 : ℝ)*(X 0 1+X 2 1)+(3894396643869/1489900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (1397/25000 : ℝ)) (hi := (20487/100000 : ℝ)) (c := (148947070691215065927/148990000000000000000 : ℝ)) (alpha := (3894396643869/1489900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (148947070691215065927/148990000000000000000 : ℝ)*(X 0 2+X 1 2)+(3894396643869/1489900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (1397/25000 : ℝ)) (hi := (20487/100000 : ℝ)) (c := (148947070691215065927/148990000000000000000 : ℝ)) (alpha := (3894396643869/1489900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154583143/10000000000 : ℝ)*X 0 0+(5512909109/10000000000 : ℝ)*X 0 1+(2578645449/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671792127/1250000000 : ℝ)*X 1 0+(-467909791/2000000000 : ℝ)*X 1 1+(5157292641/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687168473/5000000000 : ℝ)*X 2 0+(5157292641/10000000000 : ℝ)*X 2 1+(-2339549047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544408497/1250000000 : ℝ)*X 0 0+(2008248961/5000000000 : ℝ)*X 0 1+(4722460749/10000000000 : ℝ)*X 0 2+(544408497/1250000000 : ℝ)*X 1 0+(2008248961/5000000000 : ℝ)*X 1 1+(4722460749/10000000000 : ℝ)*X 1 2+(544408497/1250000000 : ℝ)*X 2 0+(2008248961/5000000000 : ℝ)*X 2 1+(4722460749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1077344427/5000000000 : ℝ)*X 0 0+(5159762149/10000000000 : ℝ)*X 0 1+(5510412877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642086859/5000000000 : ℝ)*X 1 0+(-993213457/5000000000 : ℝ)*X 1 1+(5510413461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660521551/1250000000 : ℝ)*X 2 0+(2755206657/5000000000 : ℝ)*X 2 1+(-993214461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355477253/10000000000 : ℝ)*X 0 0+(2358778149/5000000000 : ℝ)*X 0 1+(4021451727/10000000000 : ℝ)*X 0 2+(4355477253/10000000000 : ℝ)*X 1 0+(2358778149/5000000000 : ℝ)*X 1 1+(4021451727/10000000000 : ℝ)*X 1 2+(4355477253/10000000000 : ℝ)*X 2 0+(2358778149/5000000000 : ℝ)*X 2 1+(4021451727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36879312292729680055985920971/3724750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57046647/5000000000000 : ℝ)*(base19) + (810484509/100000000000000 : ℝ)*(base23) + (157513661/50000000000000 : ℝ)*(upper3) + (78954893/50000000000000 : ℝ)*(upper4) + (24689389/100000000000000 : ℝ)*(upper5) + (1057142163179009/50000000000000 : ℝ)*(major0) + (1057142163179009/50000000000000 : ℝ)*(major1) + (1057142163179009/50000000000000 : ℝ)*(major2) + (1406014227607983/50000000000000 : ℝ)*(sp0) + (1406023960001533/50000000000000 : ℝ)*(sp1) + (1406024125225749/50000000000000 : ℝ)*(sp2) + (708255417774613/50000000000000 : ℝ)*(sp3) + (515143001/2500000000000 : ℝ)*(sp4) + (8426192429/100000000000000 : ℝ)*(sp7) + (177064907717707/12500000000000 : ℝ)*(f.failure) + (1406024530468003/50000000000000 : ℝ)*(f.sum) + (91252721981783/74495000000000000000000000000 : ℝ)*base66 + (74581008134053626343/7449500000000000000000000000000000 : ℝ)*base67 + (164751250977873657/7449500000000000000000000000000000 : ℝ)*base70 + (37740111520954126343/7449500000000000000000000000000000 : ℝ)*base71 + (170026556192281/37247500000000000000000000000 : ℝ)*base73 + (10039538404301126343/7449500000000000000000000000000000 : ℝ)*base75 + (19524936410580126343/7449500000000000000000000000000000 : ℝ)*base77 + (94942987084764373657/7449500000000000000000000000000000 : ℝ)*base80 + (26730660844103/74495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (741491/125000000000000000000 : ℝ)*base89 + (741491/125000000000000000000 : ℝ)*base91 + (741491/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3399347580981149699029685463/931187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29117911/6250000000000 : ℝ)*(base19) + (12506023/12500000000000 : ℝ)*(base23) + (57815469/20000000000000 : ℝ)*(upper2) + (104184141/100000000000000 : ℝ)*(upper3) + (30639491/100000000000000 : ℝ)*(upper5) + (536050612258477/25000000000000 : ℝ)*(major0) + (536050612258477/25000000000000 : ℝ)*(major1) + (536050612258477/25000000000000 : ℝ)*(major2) + (2188896853/50000000000000 : ℝ)*(sp0) + (1206716463/10000000000000 : ℝ)*(sp1) + (2851836719681173/100000000000000 : ℝ)*(sp4) + (356478570552959/12500000000000 : ℝ)*(sp5) + (570368199485339/20000000000000 : ℝ)*(sp6) + (89785229931743/6250000000000 : ℝ)*(sp7) + (89785229931743/6250000000000 : ℝ)*(f.failure) + (2851841097474879/100000000000000 : ℝ)*(f.sum) + (37291192191621/2327968750000000000000000000 : ℝ)*base65 + (8409366553865336821/3724750000000000000000000000000000 : ℝ)*base68 + (16109515733867163179/3724750000000000000000000000000000 : ℝ)*base69 + (31486427399730913179/3724750000000000000000000000000000 : ℝ)*base71 + (81874192606559/37247500000000000000000000000 : ℝ)*base74 + (39869010953920413179/3724750000000000000000000000000000 : ℝ)*base75 + (16039013893076913179/3724750000000000000000000000000000 : ℝ)*base77 + (25324098144484413179/3724750000000000000000000000000000 : ℝ)*base79 + (169868957750991/37247500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (543641/62500000000000000000 : ℝ)*base90 + (543641/62500000000000000000 : ℝ)*base92 + (543641/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1131_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1397/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3307/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1131_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3307/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1131_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1131_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1131_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3307/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

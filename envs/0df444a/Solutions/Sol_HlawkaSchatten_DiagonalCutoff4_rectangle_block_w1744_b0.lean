-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1744_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:14:13.443809+00:00
-- url     : https://prove2.me/submissions/f93bdc91-f380-4506-922c-578cf11a3c49

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
theorem support_rectangle_w1744_s0_0 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-301620567/2500000000 : ℝ)*x 0 + (5649330817/10000000000 : ℝ)*x 1 + (4968484289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (301620567/2500000000 : ℝ)^5679 ≤ (3788308044681/50000000000000 : ℝ)^4655 := by
    have hnat : (301620567 : ℕ)^5679*50000000000000^4655 ≤ 3788308044681^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301620567 2500000000 3788308044681 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5649330817/10000000000 : ℝ)^5679 ≤ (199297415939/400000000000 : ℝ)^4655 := by
    have hnat : (5649330817 : ℕ)^5679*400000000000^4655 ≤ 199297415939^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5649330817 10000000000 199297415939 400000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4968484289/10000000000 : ℝ)^5679 ≤ (42599029914517/100000000000000 : ℝ)^4655 := by
    have hnat : (4968484289 : ℕ)^5679*100000000000000^4655 ≤ 42599029914517^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4968484289 10000000000 42599029914517 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-301620567/2500000000 : ℝ), (5649330817/10000000000 : ℝ), (4968484289/10000000000 : ℝ)] ![(3788308044681/50000000000000 : ℝ), (199297415939/400000000000 : ℝ), (42599029914517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-301620567/2500000000 : ℝ)|^5679 ≤ (3788308044681/50000000000000 : ℝ)^4655
        have hw : |(-301620567/2500000000 : ℝ)|=(301620567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5649330817/10000000000 : ℝ)|^5679 ≤ (199297415939/400000000000 : ℝ)^4655
        have hw : |(5649330817/10000000000 : ℝ)|=(5649330817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4968484289/10000000000 : ℝ)|^5679 ≤ (42599029914517/100000000000000 : ℝ)^4655
        have hw : |(4968484289/10000000000 : ℝ)|=(4968484289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s0_1 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378921329/10000000000 : ℝ)*x 0 + (-786418993/5000000000 : ℝ)*x 1 + (4968484539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378921329/10000000000 : ℝ)^5679 ≤ (5866295464233/12500000000000 : ℝ)^4655 := by
    have hnat : (5378921329 : ℕ)^5679*12500000000000^4655 ≤ 5866295464233^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378921329 10000000000 5866295464233 12500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (786418993/5000000000 : ℝ)^5679 ≤ (654412733839/6250000000000 : ℝ)^4655 := by
    have hnat : (786418993 : ℕ)^5679*6250000000000^4655 ≤ 654412733839^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786418993 5000000000 654412733839 6250000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4968484539/10000000000 : ℝ)^5679 ≤ (21299516264747/50000000000000 : ℝ)^4655 := by
    have hnat : (4968484539 : ℕ)^5679*50000000000000^4655 ≤ 21299516264747^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4968484539 10000000000 21299516264747 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378921329/10000000000 : ℝ), (-786418993/5000000000 : ℝ), (4968484539/10000000000 : ℝ)] ![(5866295464233/12500000000000 : ℝ), (654412733839/6250000000000 : ℝ), (21299516264747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378921329/10000000000 : ℝ)|^5679 ≤ (5866295464233/12500000000000 : ℝ)^4655
        have hw : |(5378921329/10000000000 : ℝ)|=(5378921329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-786418993/5000000000 : ℝ)|^5679 ≤ (654412733839/6250000000000 : ℝ)^4655
        have hw : |(-786418993/5000000000 : ℝ)|=(786418993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4968484539/10000000000 : ℝ)|^5679 ≤ (21299516264747/50000000000000 : ℝ)^4655
        have hw : |(4968484539/10000000000 : ℝ)|=(4968484539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s0_2 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075784433/2000000000 : ℝ)*x 0 + (4968484051/10000000000 : ℝ)*x 1 + (-1572837519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075784433/2000000000 : ℝ)^5679 ≤ (11732593153093/25000000000000 : ℝ)^4655 := by
    have hnat : (1075784433 : ℕ)^5679*25000000000000^4655 ≤ 11732593153093^4655*2000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075784433 2000000000 11732593153093 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4968484051/10000000000 : ℝ)^5679 ≤ (21299513712529/50000000000000 : ℝ)^4655 := by
    have hnat : (4968484051 : ℕ)^5679*50000000000000^4655 ≤ 21299513712529^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4968484051 10000000000 21299513712529 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572837519/10000000000 : ℝ)^5679 ≤ (10470599948651/100000000000000 : ℝ)^4655 := by
    have hnat : (1572837519 : ℕ)^5679*100000000000000^4655 ≤ 10470599948651^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572837519 10000000000 10470599948651 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075784433/2000000000 : ℝ), (4968484051/10000000000 : ℝ), (-1572837519/10000000000 : ℝ)] ![(11732593153093/25000000000000 : ℝ), (21299513712529/50000000000000 : ℝ), (10470599948651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075784433/2000000000 : ℝ)|^5679 ≤ (11732593153093/25000000000000 : ℝ)^4655
        have hw : |(1075784433/2000000000 : ℝ)|=(1075784433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4968484051/10000000000 : ℝ)|^5679 ≤ (21299513712529/50000000000000 : ℝ)^4655
        have hw : |(4968484051/10000000000 : ℝ)|=(4968484051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1572837519/10000000000 : ℝ)|^5679 ≤ (10470599948651/100000000000000 : ℝ)^4655
        have hw : |(-1572837519/10000000000 : ℝ)|=(1572837519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s0_3 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (996620643/2500000000 : ℝ)*x 0 + (744617423/2500000000 : ℝ)*x 1 + (5160735099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996620643/2500000000 : ℝ)^5679 ≤ (16281642917083/50000000000000 : ℝ)^4655 := by
    have hnat : (996620643 : ℕ)^5679*50000000000000^4655 ≤ 16281642917083^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996620643 2500000000 16281642917083 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744617423/2500000000 : ℝ)^5679 ≤ (1140914212221/5000000000000 : ℝ)^4655 := by
    have hnat : (744617423 : ℕ)^5679*5000000000000^4655 ≤ 1140914212221^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744617423 2500000000 1140914212221 5000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5160735099/10000000000 : ℝ)^5679 ≤ (44618429906379/100000000000000 : ℝ)^4655 := by
    have hnat : (5160735099 : ℕ)^5679*100000000000000^4655 ≤ 44618429906379^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160735099 10000000000 44618429906379 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(996620643/2500000000 : ℝ), (744617423/2500000000 : ℝ), (5160735099/10000000000 : ℝ)] ![(16281642917083/50000000000000 : ℝ), (1140914212221/5000000000000 : ℝ), (44618429906379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(996620643/2500000000 : ℝ)|^5679 ≤ (16281642917083/50000000000000 : ℝ)^4655
        have hw : |(996620643/2500000000 : ℝ)|=(996620643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744617423/2500000000 : ℝ)|^5679 ≤ (1140914212221/5000000000000 : ℝ)^4655
        have hw : |(744617423/2500000000 : ℝ)|=(744617423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5160735099/10000000000 : ℝ)|^5679 ≤ (44618429906379/100000000000000 : ℝ)^4655
        have hw : |(5160735099/10000000000 : ℝ)|=(5160735099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s0_4 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4718663/39062500 : ℝ)*x 0 + (1246499149/2500000000 : ℝ)*x 1 + (5631228347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4718663/39062500 : ℝ)^5679 ≤ (7588074925501/100000000000000 : ℝ)^4655 := by
    have hnat : (4718663 : ℕ)^5679*100000000000000^4655 ≤ 7588074925501^4655*39062500^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4718663 39062500 7588074925501 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246499149/2500000000 : ℝ)^5679 ≤ (5347784753537/12500000000000 : ℝ)^4655 := by
    have hnat : (1246499149 : ℕ)^5679*12500000000000^4655 ≤ 5347784753537^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246499149 2500000000 5347784753537 12500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5631228347/10000000000 : ℝ)^5679 ≤ (49629647027721/100000000000000 : ℝ)^4655 := by
    have hnat : (5631228347 : ℕ)^5679*100000000000000^4655 ≤ 49629647027721^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5631228347 10000000000 49629647027721 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4718663/39062500 : ℝ), (1246499149/2500000000 : ℝ), (5631228347/10000000000 : ℝ)] ![(7588074925501/100000000000000 : ℝ), (5347784753537/12500000000000 : ℝ), (49629647027721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4718663/39062500 : ℝ)|^5679 ≤ (7588074925501/100000000000000 : ℝ)^4655
        have hw : |(-4718663/39062500 : ℝ)|=(4718663/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1246499149/2500000000 : ℝ)|^5679 ≤ (5347784753537/12500000000000 : ℝ)^4655
        have hw : |(1246499149/2500000000 : ℝ)|=(1246499149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5631228347/10000000000 : ℝ)|^5679 ≤ (49629647027721/100000000000000 : ℝ)^4655
        have hw : |(5631228347/10000000000 : ℝ)|=(5631228347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s0_5 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259837927/500000000 : ℝ)*x 0 + (-182018961/2000000000 : ℝ)*x 1 + (2815614899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259837927/500000000 : ℝ)^5679 ≤ (22499341517723/50000000000000 : ℝ)^4655 := by
    have hnat : (259837927 : ℕ)^5679*50000000000000^4655 ≤ 22499341517723^4655*500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259837927 500000000 22499341517723 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182018961/2000000000 : ℝ)^5679 ≤ (1342913578111/25000000000000 : ℝ)^4655 := by
    have hnat : (182018961 : ℕ)^5679*25000000000000^4655 ≤ 1342913578111^4655*2000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182018961 2000000000 1342913578111 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2815614899/5000000000 : ℝ)^5679 ≤ (12407415657227/25000000000000 : ℝ)^4655 := by
    have hnat : (2815614899 : ℕ)^5679*25000000000000^4655 ≤ 12407415657227^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2815614899 5000000000 12407415657227 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259837927/500000000 : ℝ), (-182018961/2000000000 : ℝ), (2815614899/5000000000 : ℝ)] ![(22499341517723/50000000000000 : ℝ), (1342913578111/25000000000000 : ℝ), (12407415657227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259837927/500000000 : ℝ)|^5679 ≤ (22499341517723/50000000000000 : ℝ)^4655
        have hw : |(259837927/500000000 : ℝ)|=(259837927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182018961/2000000000 : ℝ)|^5679 ≤ (1342913578111/25000000000000 : ℝ)^4655
        have hw : |(-182018961/2000000000 : ℝ)|=(182018961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2815614899/5000000000 : ℝ)|^5679 ≤ (12407415657227/25000000000000 : ℝ)^4655
        have hw : |(2815614899/5000000000 : ℝ)|=(2815614899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s0_6 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598380309/5000000000 : ℝ)*x 0 + (563122749/1000000000 : ℝ)*x 1 + (-227523801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598380309/5000000000 : ℝ)^5679 ≤ (44998704986987/100000000000000 : ℝ)^4655 := by
    have hnat : (2598380309 : ℕ)^5679*100000000000000^4655 ≤ 44998704986987^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598380309 5000000000 44998704986987 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563122749/1000000000 : ℝ)^5679 ≤ (12407409453309/25000000000000 : ℝ)^4655 := by
    have hnat : (563122749 : ℕ)^5679*25000000000000^4655 ≤ 12407409453309^4655*1000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563122749 1000000000 12407409453309 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227523801/2500000000 : ℝ)^5679 ≤ (1342914296379/25000000000000 : ℝ)^4655 := by
    have hnat : (227523801 : ℕ)^5679*25000000000000^4655 ≤ 1342914296379^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227523801 2500000000 1342914296379 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598380309/5000000000 : ℝ), (563122749/1000000000 : ℝ), (-227523801/2500000000 : ℝ)] ![(44998704986987/100000000000000 : ℝ), (12407409453309/25000000000000 : ℝ), (1342914296379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598380309/5000000000 : ℝ)|^5679 ≤ (44998704986987/100000000000000 : ℝ)^4655
        have hw : |(2598380309/5000000000 : ℝ)|=(2598380309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563122749/1000000000 : ℝ)|^5679 ≤ (12407409453309/25000000000000 : ℝ)^4655
        have hw : |(563122749/1000000000 : ℝ)|=(563122749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-227523801/2500000000 : ℝ)|^5679 ≤ (1342914296379/25000000000000 : ℝ)^4655
        have hw : |(-227523801/2500000000 : ℝ)|=(227523801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s0_7 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (997820927/2500000000 : ℝ)*x 0 + (2552302237/5000000000 : ℝ)*x 1 + (1518247643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997820927/2500000000 : ℝ)^5679 ≤ (32611136947923/100000000000000 : ℝ)^4655 := by
    have hnat : (997820927 : ℕ)^5679*100000000000000^4655 ≤ 32611136947923^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997820927 2500000000 32611136947923 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2552302237/5000000000 : ℝ)^5679 ≤ (176108380393/400000000000 : ℝ)^4655 := by
    have hnat : (2552302237 : ℕ)^5679*400000000000^4655 ≤ 176108380393^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552302237 5000000000 176108380393 400000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518247643/5000000000 : ℝ)^5679 ≤ (584044198363/2500000000000 : ℝ)^4655 := by
    have hnat : (1518247643 : ℕ)^5679*2500000000000^4655 ≤ 584044198363^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518247643 5000000000 584044198363 2500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(997820927/2500000000 : ℝ), (2552302237/5000000000 : ℝ), (1518247643/5000000000 : ℝ)] ![(32611136947923/100000000000000 : ℝ), (176108380393/400000000000 : ℝ), (584044198363/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(997820927/2500000000 : ℝ)|^5679 ≤ (32611136947923/100000000000000 : ℝ)^4655
        have hw : |(997820927/2500000000 : ℝ)|=(997820927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2552302237/5000000000 : ℝ)|^5679 ≤ (176108380393/400000000000 : ℝ)^4655
        have hw : |(2552302237/5000000000 : ℝ)|=(2552302237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1518247643/5000000000 : ℝ)|^5679 ≤ (584044198363/2500000000000 : ℝ)^4655
        have hw : |(1518247643/5000000000 : ℝ)|=(1518247643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1744_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (105130561/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3237/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21169/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5663/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5663 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5663*1^1024 ≤ 0^1024*1^5663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5663/1024 : ℝ) ≤ (157479109022212139/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5663 ≤ (157479109022212139/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5663*25000000000000000000^1024 ≤ 157479109022212139^1024*5^5663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 157479109022212139 25000000000000000000 5663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (157479109022212139/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5663 := by
      have hnat : (1 : ℕ)^1024*1^5663 ≤ 1^5663*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25157479109022212139/25000000000000000000 : ℝ) ≤ (5005680527355353/5000000000000000 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (25157479109022212139/25000000000000000000 : ℝ)^1024 ≤ (5005680527355353/5000000000000000 : ℝ)^5663 := by
      have hnat : (25157479109022212139 : ℕ)^1024*5000000000000000^5663 ≤ 5005680527355353^5663*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25157479109022212139 25000000000000000000 5005680527355353 5000000000000000 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005680527355353/5000000000000000 : ℝ)) (X := (25157479109022212139/25000000000000000000 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12657479109022212139/12500000000000000000 : ℝ) ≤ (2505680527355353/2500000000000000 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (12657479109022212139/12500000000000000000 : ℝ)^1024 ≤ (2505680527355353/2500000000000000 : ℝ)^5663 := by
      have hnat : (12657479109022212139 : ℕ)^1024*2500000000000000^5663 ≤ 2505680527355353^5663*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12657479109022212139 12500000000000000000 2505680527355353 2500000000000000 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505680527355353/2500000000000000 : ℝ)) (X := (12657479109022212139/12500000000000000000 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5680527355353/2000000000000000 : ℝ)*(0 : ℝ))^(5663/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5680527355353/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(157479109022212139/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5680527355353/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5663/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5680527355353/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5005680527355353/5000000000000000 : ℝ) by norm_num, show 1+(157479109022212139/25000000000000000000 : ℝ)+(0 : ℝ)=(25157479109022212139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(157479109022212139/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5680527355353/2000000000000000 : ℝ)*(2/5 : ℝ))^(5663/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5680527355353/2000000000000000 : ℝ)*(2/5 : ℝ)=(2505680527355353/2500000000000000 : ℝ) by norm_num, show 1+2*(157479109022212139/25000000000000000000 : ℝ)=(12657479109022212139/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5680527355353/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5680527355353/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5680527355353/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5680527355353/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5680527355353/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5680527355353/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-301620567/2500000000 : ℝ)*X 0 0+(5649330817/10000000000 : ℝ)*X 0 1+(4968484289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378921329/10000000000 : ℝ)*X 1 0+(-786418993/5000000000 : ℝ)*X 1 1+(4968484539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1075784433/2000000000 : ℝ)*X 2 0+(4968484051/10000000000 : ℝ)*X 2 1+(-1572837519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((996620643/2500000000 : ℝ)*X 0 0+(744617423/2500000000 : ℝ)*X 0 1+(5160735099/10000000000 : ℝ)*X 0 2+(996620643/2500000000 : ℝ)*X 1 0+(744617423/2500000000 : ℝ)*X 1 1+(5160735099/10000000000 : ℝ)*X 1 2+(996620643/2500000000 : ℝ)*X 2 0+(744617423/2500000000 : ℝ)*X 2 1+(5160735099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4718663/39062500 : ℝ)*X 0 0+(1246499149/2500000000 : ℝ)*X 0 1+(5631228347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((259837927/500000000 : ℝ)*X 1 0+(-182018961/2000000000 : ℝ)*X 1 1+(2815614899/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2598380309/5000000000 : ℝ)*X 2 0+(563122749/1000000000 : ℝ)*X 2 1+(-227523801/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((997820927/2500000000 : ℝ)*X 0 0+(2552302237/5000000000 : ℝ)*X 0 1+(1518247643/5000000000 : ℝ)*X 0 2+(997820927/2500000000 : ℝ)*X 1 0+(2552302237/5000000000 : ℝ)*X 1 1+(1518247643/5000000000 : ℝ)*X 1 2+(997820927/2500000000 : ℝ)*X 2 0+(2552302237/5000000000 : ℝ)*X 2 1+(1518247643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60299198638919507656329/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414179461/50000000000000 : ℝ)*(base19) + (101783329/10000000000000 : ℝ)*(base23) + (6399327/20000000000000 : ℝ)*(upper3) + (20872259/100000000000000 : ℝ)*(upper4) + (62332517/25000000000000 : ℝ)*(upper5) + (120438256006531/12500000000000 : ℝ)*(major0) + (120438256006531/12500000000000 : ℝ)*(major1) + (120438256006531/12500000000000 : ℝ)*(major2) + (183595370959359/12500000000000 : ℝ)*(sp0) + (367192124857089/25000000000000 : ℝ)*(sp1) + (367192077488497/25000000000000 : ℝ)*(sp2) + (57280155337429/12500000000000 : ℝ)*(sp3) + (3180056203/50000000000000 : ℝ)*(sp4) + (1364819921/100000000000000 : ℝ)*(sp7) + (458242607519353/100000000000000 : ℝ)*(f.failure) + (734384663893639/50000000000000 : ℝ)*(f.sum) + (1163760539557/12500000000000000000000000000 : ℝ)*base66 + (21342521639557/25000000000000000000000000000 : ℝ)*base68 + (63338149210443/25000000000000000000000000000 : ℝ)*base69 + (73627243410443/25000000000000000000000000000 : ℝ)*base71 + (40594105214557/12500000000000000000000000000 : ℝ)*base74 + (64374924360443/25000000000000000000000000000 : ℝ)*base75 + (128938771010443/25000000000000000000000000000 : ℝ)*base77 + (23598853660443/25000000000000000000000000000 : ℝ)*base79 + (6579979214557/12500000000000000000000000000 : ℝ)*base82 + (752967/5000000000000000000000 : ℝ)*base90 + (752967/5000000000000000000000 : ℝ)*base92 + (752967/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92665478296089895148457/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24782017/5000000000000 : ℝ)*(base19) + (1137980519/100000000000000 : ℝ)*(base23) + (103635483/12500000000000 : ℝ)*(base32) + (83150449/50000000000000 : ℝ)*(base37) + (27664763/10000000000000 : ℝ)*(upper3) + (254170146258673/25000000000000 : ℝ)*(major0) + (254170146258673/25000000000000 : ℝ)*(major1) + (254170146258673/25000000000000 : ℝ)*(major2) + (2486118609/100000000000000 : ℝ)*(sp1) + (3131419703/100000000000000 : ℝ)*(sp2) + (309965661300109/20000000000000 : ℝ)*(sp4) + (1549825324741597/100000000000000 : ℝ)*(sp5) + (387456009275081/25000000000000 : ℝ)*(sp6) + (241765686984093/50000000000000 : ℝ)*(sp7) + (120883092338237/25000000000000 : ℝ)*(f.failure) + (309965661300109/20000000000000 : ℝ)*(f.sum) + (37862168973431/25000000000000000000000000000 : ℝ)*base66 + (106626319973431/50000000000000000000000000000 : ℝ)*base68 + (198951886323431/50000000000000000000000000000 : ℝ)*base70 + (333506542223431/50000000000000000000000000000 : ℝ)*base72 + (13557151601569/25000000000000000000000000000 : ℝ)*base73 + (460864113423431/50000000000000000000000000000 : ℝ)*base76 + (492794416523431/50000000000000000000000000000 : ℝ)*base78 + (291487259623431/50000000000000000000000000000 : ℝ)*base80 + (43793076848431/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7560957/1250000000000000000000 : ℝ)*base89 + (7560957/1250000000000000000000 : ℝ)*base91 + (7560957/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1744_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (105130561/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3237/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21169/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1744_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1744_s1_0 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-31377279/250000000 : ℝ)*x 0 + (688699491/1250000000 : ℝ)*x 1 + (317238501/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31377279/250000000 : ℝ)^5679 ≤ (1590132040217/20000000000000 : ℝ)^4655 := by
    have hnat : (31377279 : ℕ)^5679*20000000000000^4655 ≤ 1590132040217^4655*250000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31377279 250000000 1590132040217 20000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688699491/1250000000 : ℝ)^5679 ≤ (302031105637/625000000000 : ℝ)^4655 := by
    have hnat : (688699491 : ℕ)^5679*625000000000^4655 ≤ 302031105637^4655*1250000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688699491 1250000000 302031105637 625000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317238501/625000000 : ℝ)^5679 ≤ (43724362878083/100000000000000 : ℝ)^4655 := by
    have hnat : (317238501 : ℕ)^5679*100000000000000^4655 ≤ 43724362878083^4655*625000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317238501 625000000 43724362878083 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31377279/250000000 : ℝ), (688699491/1250000000 : ℝ), (317238501/625000000 : ℝ)] ![(1590132040217/20000000000000 : ℝ), (302031105637/625000000000 : ℝ), (43724362878083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31377279/250000000 : ℝ)|^5679 ≤ (1590132040217/20000000000000 : ℝ)^4655
        have hw : |(-31377279/250000000 : ℝ)|=(31377279/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688699491/1250000000 : ℝ)|^5679 ≤ (302031105637/625000000000 : ℝ)^4655
        have hw : |(688699491/1250000000 : ℝ)|=(688699491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317238501/625000000 : ℝ)|^5679 ≤ (43724362878083/100000000000000 : ℝ)^4655
        have hw : |(317238501/625000000 : ℝ)|=(317238501/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s1_1 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667712751/1250000000 : ℝ)*x 0 + (-1482439731/10000000000 : ℝ)*x 1 + (2537907953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667712751/1250000000 : ℝ)^5679 ≤ (2908406112607/6250000000000 : ℝ)^4655 := by
    have hnat : (667712751 : ℕ)^5679*6250000000000^4655 ≤ 2908406112607^4655*1250000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667712751 1250000000 2908406112607 6250000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1482439731/10000000000 : ℝ)^5679 ≤ (9741140456991/100000000000000 : ℝ)^4655 := by
    have hnat : (1482439731 : ℕ)^5679*100000000000000^4655 ≤ 9741140456991^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482439731 10000000000 9741140456991 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537907953/5000000000 : ℝ)^5679 ≤ (43724361722071/100000000000000 : ℝ)^4655 := by
    have hnat : (2537907953 : ℕ)^5679*100000000000000^4655 ≤ 43724361722071^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537907953 5000000000 43724361722071 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667712751/1250000000 : ℝ), (-1482439731/10000000000 : ℝ), (2537907953/5000000000 : ℝ)] ![(2908406112607/6250000000000 : ℝ), (9741140456991/100000000000000 : ℝ), (43724361722071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667712751/1250000000 : ℝ)|^5679 ≤ (2908406112607/6250000000000 : ℝ)^4655
        have hw : |(667712751/1250000000 : ℝ)|=(667712751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1482439731/10000000000 : ℝ)|^5679 ≤ (9741140456991/100000000000000 : ℝ)^4655
        have hw : |(-1482439731/10000000000 : ℝ)|=(1482439731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537907953/5000000000 : ℝ)|^5679 ≤ (43724361722071/100000000000000 : ℝ)^4655
        have hw : |(2537907953/5000000000 : ℝ)|=(2537907953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s1_2 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213668063/400000000 : ℝ)*x 0 + (5075816209/10000000000 : ℝ)*x 1 + (-370609977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213668063/400000000 : ℝ)^5679 ≤ (46534493199831/100000000000000 : ℝ)^4655 := by
    have hnat : (213668063 : ℕ)^5679*100000000000000^4655 ≤ 46534493199831^4655*400000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213668063 400000000 46534493199831 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075816209/10000000000 : ℝ)^5679 ≤ (43724364906359/100000000000000 : ℝ)^4655 := by
    have hnat : (5075816209 : ℕ)^5679*100000000000000^4655 ≤ 43724364906359^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075816209 10000000000 43724364906359 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370609977/2500000000 : ℝ)^5679 ≤ (1217642734489/12500000000000 : ℝ)^4655 := by
    have hnat : (370609977 : ℕ)^5679*12500000000000^4655 ≤ 1217642734489^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370609977 2500000000 1217642734489 12500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213668063/400000000 : ℝ), (5075816209/10000000000 : ℝ), (-370609977/2500000000 : ℝ)] ![(46534493199831/100000000000000 : ℝ), (43724364906359/100000000000000 : ℝ), (1217642734489/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213668063/400000000 : ℝ)|^5679 ≤ (46534493199831/100000000000000 : ℝ)^4655
        have hw : |(213668063/400000000 : ℝ)|=(213668063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075816209/10000000000 : ℝ)|^5679 ≤ (43724364906359/100000000000000 : ℝ)^4655
        have hw : |(5075816209/10000000000 : ℝ)|=(5075816209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-370609977/2500000000 : ℝ)|^5679 ≤ (1217642734489/12500000000000 : ℝ)^4655
        have hw : |(-370609977/2500000000 : ℝ)|=(370609977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s1_3 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4032488679/10000000000 : ℝ)*x 0 + (842707813/2500000000 : ℝ)*x 1 + (2380595631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4032488679/10000000000 : ℝ)^5679 ≤ (1651116543311/5000000000000 : ℝ)^4655 := by
    have hnat : (4032488679 : ℕ)^5679*5000000000000^4655 ≤ 1651116543311^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032488679 10000000000 1651116543311 5000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842707813/2500000000 : ℝ)^5679 ≤ (26536845724067/100000000000000 : ℝ)^4655 := by
    have hnat : (842707813 : ℕ)^5679*100000000000000^4655 ≤ 26536845724067^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842707813 2500000000 26536845724067 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2380595631/5000000000 : ℝ)^5679 ≤ (40440823391729/100000000000000 : ℝ)^4655 := by
    have hnat : (2380595631 : ℕ)^5679*100000000000000^4655 ≤ 40440823391729^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380595631 5000000000 40440823391729 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4032488679/10000000000 : ℝ), (842707813/2500000000 : ℝ), (2380595631/5000000000 : ℝ)] ![(1651116543311/5000000000000 : ℝ), (26536845724067/100000000000000 : ℝ), (40440823391729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4032488679/10000000000 : ℝ)|^5679 ≤ (1651116543311/5000000000000 : ℝ)^4655
        have hw : |(4032488679/10000000000 : ℝ)|=(4032488679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(842707813/2500000000 : ℝ)|^5679 ≤ (26536845724067/100000000000000 : ℝ)^4655
        have hw : |(842707813/2500000000 : ℝ)|=(842707813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2380595631/5000000000 : ℝ)|^5679 ≤ (40440823391729/100000000000000 : ℝ)^4655
        have hw : |(2380595631/5000000000 : ℝ)|=(2380595631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s1_4 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-313868819/2500000000 : ℝ)*x 0 + (5082930027/10000000000 : ℝ)*x 1 + (85973899/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (313868819/2500000000 : ℝ)^5679 ≤ (1590725767651/20000000000000 : ℝ)^4655 := by
    have hnat : (313868819 : ℕ)^5679*20000000000000^4655 ≤ 1590725767651^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313868819 2500000000 1590725767651 20000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082930027/10000000000 : ℝ)^5679 ≤ (2737446061763/6250000000000 : ℝ)^4655 := by
    have hnat : (5082930027 : ℕ)^5679*6250000000000^4655 ≤ 2737446061763^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082930027 10000000000 2737446061763 6250000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85973899/156250000 : ℝ)^5679 ≤ (4824723415399/10000000000000 : ℝ)^4655 := by
    have hnat : (85973899 : ℕ)^5679*10000000000000^4655 ≤ 4824723415399^4655*156250000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85973899 156250000 4824723415399 10000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-313868819/2500000000 : ℝ), (5082930027/10000000000 : ℝ), (85973899/156250000 : ℝ)] ![(1590725767651/20000000000000 : ℝ), (2737446061763/6250000000000 : ℝ), (4824723415399/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-313868819/2500000000 : ℝ)|^5679 ≤ (1590725767651/20000000000000 : ℝ)^4655
        have hw : |(-313868819/2500000000 : ℝ)|=(313868819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082930027/10000000000 : ℝ)|^5679 ≤ (2737446061763/6250000000000 : ℝ)^4655
        have hw : |(5082930027/10000000000 : ℝ)|=(5082930027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85973899/156250000 : ℝ)|^5679 ≤ (4824723415399/10000000000000 : ℝ)^4655
        have hw : |(85973899/156250000 : ℝ)|=(85973899/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s1_5 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306629141/2500000000 : ℝ)*x 0 + (-211185189/2000000000 : ℝ)*x 1 + (5502329849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306629141/2500000000 : ℝ)^5679 ≤ (5664154752983/12500000000000 : ℝ)^4655 := by
    have hnat : (1306629141 : ℕ)^5679*12500000000000^4655 ≤ 5664154752983^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306629141 2500000000 5664154752983 12500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211185189/2000000000 : ℝ)^5679 ≤ (128790489147/2000000000000 : ℝ)^4655 := by
    have hnat : (211185189 : ℕ)^5679*2000000000000^4655 ≤ 128790489147^4655*2000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211185189 2000000000 128790489147 2000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5502329849/10000000000 : ℝ)^5679 ≤ (24123618751137/50000000000000 : ℝ)^4655 := by
    have hnat : (5502329849 : ℕ)^5679*50000000000000^4655 ≤ 24123618751137^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502329849 10000000000 24123618751137 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306629141/2500000000 : ℝ), (-211185189/2000000000 : ℝ), (5502329849/10000000000 : ℝ)] ![(5664154752983/12500000000000 : ℝ), (128790489147/2000000000000 : ℝ), (24123618751137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306629141/2500000000 : ℝ)|^5679 ≤ (5664154752983/12500000000000 : ℝ)^4655
        have hw : |(1306629141/2500000000 : ℝ)|=(1306629141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211185189/2000000000 : ℝ)|^5679 ≤ (128790489147/2000000000000 : ℝ)^4655
        have hw : |(-211185189/2000000000 : ℝ)|=(211185189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5502329849/10000000000 : ℝ)|^5679 ≤ (24123618751137/50000000000000 : ℝ)^4655
        have hw : |(5502329849/10000000000 : ℝ)|=(5502329849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s1_6 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326657273/625000000 : ℝ)*x 0 + (5502329967/10000000000 : ℝ)*x 1 + (-527963027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326657273/625000000 : ℝ)^5679 ≤ (1132830898769/2500000000000 : ℝ)^4655 := by
    have hnat : (326657273 : ℕ)^5679*2500000000000^4655 ≤ 1132830898769^4655*625000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326657273 625000000 1132830898769 2500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502329967/10000000000 : ℝ)^5679 ≤ (48247238764567/100000000000000 : ℝ)^4655 := by
    have hnat : (5502329967 : ℕ)^5679*100000000000000^4655 ≤ 48247238764567^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502329967 10000000000 48247238764567 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527963027/5000000000 : ℝ)^5679 ≤ (6439525268309/100000000000000 : ℝ)^4655 := by
    have hnat : (527963027 : ℕ)^5679*100000000000000^4655 ≤ 6439525268309^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527963027 5000000000 6439525268309 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326657273/625000000 : ℝ), (5502329967/10000000000 : ℝ), (-527963027/5000000000 : ℝ)] ![(1132830898769/2500000000000 : ℝ), (48247238764567/100000000000000 : ℝ), (6439525268309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326657273/625000000 : ℝ)|^5679 ≤ (1132830898769/2500000000000 : ℝ)^4655
        have hw : |(326657273/625000000 : ℝ)|=(326657273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502329967/10000000000 : ℝ)|^5679 ≤ (48247238764567/100000000000000 : ℝ)^4655
        have hw : |(5502329967/10000000000 : ℝ)|=(5502329967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527963027/5000000000 : ℝ)|^5679 ≤ (6439525268309/100000000000000 : ℝ)^4655
        have hw : |(-527963027/5000000000 : ℝ)|=(527963027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s1_7 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2016860019/5000000000 : ℝ)*x 0 + (1184597643/2500000000 : ℝ)*x 1 + (424264997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016860019/5000000000 : ℝ)^5679 ≤ (660692663161/2000000000000 : ℝ)^4655 := by
    have hnat : (2016860019 : ℕ)^5679*2000000000000^4655 ≤ 660692663161^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016860019 5000000000 660692663161 2000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1184597643/2500000000 : ℝ)^5679 ≤ (20102340098099/50000000000000 : ℝ)^4655 := by
    have hnat : (1184597643 : ℕ)^5679*50000000000000^4655 ≤ 20102340098099^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184597643 2500000000 20102340098099 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424264997/1250000000 : ℝ)^5679 ≤ (6690171659661/25000000000000 : ℝ)^4655 := by
    have hnat : (424264997 : ℕ)^5679*25000000000000^4655 ≤ 6690171659661^4655*1250000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424264997 1250000000 6690171659661 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2016860019/5000000000 : ℝ), (1184597643/2500000000 : ℝ), (424264997/1250000000 : ℝ)] ![(660692663161/2000000000000 : ℝ), (20102340098099/50000000000000 : ℝ), (6690171659661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2016860019/5000000000 : ℝ)|^5679 ≤ (660692663161/2000000000000 : ℝ)^4655
        have hw : |(2016860019/5000000000 : ℝ)|=(2016860019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1184597643/2500000000 : ℝ)|^5679 ≤ (20102340098099/50000000000000 : ℝ)^4655
        have hw : |(1184597643/2500000000 : ℝ)|=(1184597643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424264997/1250000000 : ℝ)|^5679 ≤ (6690171659661/25000000000000 : ℝ)^4655
        have hw : |(424264997/1250000000 : ℝ)|=(424264997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1744_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (105130561/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3237/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8883/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3637/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3237/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3237/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3237/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3237/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3237/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3237/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3237/50000 : ℝ) ^ (5663/1024 : ℝ) ≤ (26635443576281/100000000000000000000 : ℝ) := by
    have hpowers : (3237/50000 : ℝ)^5663 ≤ (26635443576281/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3237 : ℕ)^5663*100000000000000000000^1024 ≤ 26635443576281^1024*50000^5663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3237 50000 26635443576281 100000000000000000000 5663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3237/50000 : ℝ)) (X := (26635443576281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21169/100000 : ℝ) ^ (5663/1024 : ℝ) ≤ (9330577443339449/50000000000000000000 : ℝ) := by
    have hpowers : (21169/100000 : ℝ)^5663 ≤ (9330577443339449/50000000000000000000 : ℝ)^1024 := by
      have hnat : (21169 : ℕ)^5663*50000000000000000000^1024 ≤ 9330577443339449^1024*100000^5663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21169 100000 9330577443339449 50000000000000000000 5663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21169/100000 : ℝ)) (X := (9330577443339449/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000026635443576281/50000000000000000000 : ℝ) ≤ (10000000963259343/10000000000000000 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (50000026635443576281/50000000000000000000 : ℝ)^1024 ≤ (10000000963259343/10000000000000000 : ℝ)^5663 := by
      have hnat : (50000026635443576281 : ℕ)^1024*10000000000000000^5663 ≤ 10000000963259343^5663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000026635443576281 50000000000000000000 10000000963259343 10000000000000000 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000963259343/10000000000000000 : ℝ)) (X := (50000026635443576281/50000000000000000000 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018687790330255179/100000000000000000000 : ℝ) ≤ (400013515686183/400000000000000 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (100018687790330255179/100000000000000000000 : ℝ)^1024 ≤ (400013515686183/400000000000000 : ℝ)^5663 := by
      have hnat : (100018687790330255179 : ℕ)^1024*400000000000000^5663 ≤ 400013515686183^5663*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018687790330255179 100000000000000000000 400013515686183 400000000000000 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400013515686183/400000000000000 : ℝ)) (X := (100018687790330255179/100000000000000000000 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009330577443339449/25000000000000000000 : ℝ) ≤ (10000674821049807/10000000000000000 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (25009330577443339449/25000000000000000000 : ℝ)^1024 ≤ (10000674821049807/10000000000000000 : ℝ)^5663 := by
      have hnat : (25009330577443339449 : ℕ)^1024*10000000000000000^5663 ≤ 10000674821049807^5663*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009330577443339449 25000000000000000000 10000674821049807 10000000000000000 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674821049807/10000000000000000 : ℝ)) (X := (25009330577443339449/25000000000000000000 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26635443576281/100000000000000000000 : ℝ) ≤ ((146945651599760581449/146950000000000000000 : ℝ)+2*(1316128497/5740234375000 : ℝ)*(3237/50000 : ℝ))^(5663/1024 : ℝ) := by
    rw [show (146945651599760581449/146950000000000000000 : ℝ)+2*(1316128497/5740234375000 : ℝ)*(3237/50000 : ℝ)=(10000000963259343/10000000000000000 : ℝ) by norm_num, show 1+2*(26635443576281/100000000000000000000 : ℝ)=(50000026635443576281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9330577443339449/50000000000000000000 : ℝ)+(26635443576281/100000000000000000000 : ℝ) ≤ ((146945651599760581449/146950000000000000000 : ℝ)+(1316128497/5740234375000 : ℝ)*((21169/100000 : ℝ)+(3237/50000 : ℝ)))^(5663/1024 : ℝ) := by
    rw [show (146945651599760581449/146950000000000000000 : ℝ)+(1316128497/5740234375000 : ℝ)*((21169/100000 : ℝ)+(3237/50000 : ℝ))=(400013515686183/400000000000000 : ℝ) by norm_num, show 1+(9330577443339449/50000000000000000000 : ℝ)+(26635443576281/100000000000000000000 : ℝ)=(100018687790330255179/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9330577443339449/50000000000000000000 : ℝ) ≤ ((146945651599760581449/146950000000000000000 : ℝ)+2*(1316128497/5740234375000 : ℝ)*(21169/100000 : ℝ))^(5663/1024 : ℝ) := by
    rw [show (146945651599760581449/146950000000000000000 : ℝ)+2*(1316128497/5740234375000 : ℝ)*(21169/100000 : ℝ)=(10000674821049807/10000000000000000 : ℝ) by norm_num, show 1+2*(9330577443339449/50000000000000000000 : ℝ)=(25009330577443339449/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (146945651599760581449/146950000000000000000 : ℝ)*(X 1 0+X 2 0)+(1316128497/5740234375000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (3237/50000 : ℝ)) (hi := (21169/100000 : ℝ)) (c := (146945651599760581449/146950000000000000000 : ℝ)) (alpha := (1316128497/5740234375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (146945651599760581449/146950000000000000000 : ℝ)*(X 0 1+X 2 1)+(1316128497/5740234375000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (3237/50000 : ℝ)) (hi := (21169/100000 : ℝ)) (c := (146945651599760581449/146950000000000000000 : ℝ)) (alpha := (1316128497/5740234375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (146945651599760581449/146950000000000000000 : ℝ)*(X 0 2+X 1 2)+(1316128497/5740234375000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (3237/50000 : ℝ)) (hi := (21169/100000 : ℝ)) (c := (146945651599760581449/146950000000000000000 : ℝ)) (alpha := (1316128497/5740234375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-31377279/250000000 : ℝ)*X 0 0+(688699491/1250000000 : ℝ)*X 0 1+(317238501/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((667712751/1250000000 : ℝ)*X 1 0+(-1482439731/10000000000 : ℝ)*X 1 1+(2537907953/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213668063/400000000 : ℝ)*X 2 0+(5075816209/10000000000 : ℝ)*X 2 1+(-370609977/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4032488679/10000000000 : ℝ)*X 0 0+(842707813/2500000000 : ℝ)*X 0 1+(2380595631/5000000000 : ℝ)*X 0 2+(4032488679/10000000000 : ℝ)*X 1 0+(842707813/2500000000 : ℝ)*X 1 1+(2380595631/5000000000 : ℝ)*X 1 2+(4032488679/10000000000 : ℝ)*X 2 0+(842707813/2500000000 : ℝ)*X 2 1+(2380595631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-313868819/2500000000 : ℝ)*X 0 0+(5082930027/10000000000 : ℝ)*X 0 1+(85973899/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1306629141/2500000000 : ℝ)*X 1 0+(-211185189/2000000000 : ℝ)*X 1 1+(5502329849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((326657273/625000000 : ℝ)*X 2 0+(5502329967/10000000000 : ℝ)*X 2 1+(-527963027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2016860019/5000000000 : ℝ)*X 0 0+(1184597643/2500000000 : ℝ)*X 0 1+(424264997/1250000000 : ℝ)*X 0 2+(2016860019/5000000000 : ℝ)*X 1 0+(1184597643/2500000000 : ℝ)*X 1 1+(424264997/1250000000 : ℝ)*X 1 2+(2016860019/5000000000 : ℝ)*X 2 0+(1184597643/2500000000 : ℝ)*X 2 1+(424264997/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89100129897094180496583626997/7347500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183176689/10000000000000 : ℝ)*(base19) + (1477106999/100000000000000 : ℝ)*(base23) + (44813719/50000000000000 : ℝ)*(lower2) + (72535457/20000000000000 : ℝ)*(upper3) + (118652141/100000000000000 : ℝ)*(upper5) + (1512294986699951/100000000000000 : ℝ)*(major0) + (1512294986699951/100000000000000 : ℝ)*(major1) + (1512294986699951/100000000000000 : ℝ)*(major2) + (1152665693554023/50000000000000 : ℝ)*(sp0) + (288167700699541/12500000000000 : ℝ)*(sp1) + (115267098012811/5000000000000 : ℝ)*(sp2) + (89905192109349/12500000000000 : ℝ)*(sp3) + (6025127587/50000000000000 : ℝ)*(sp4) + (2297471087/50000000000000 : ℝ)*(sp7) + (359623065908483/50000000000000 : ℝ)*(f.failure) + (2305343437363219/100000000000000 : ℝ)*(f.sum) + (4704052349367/18368750000000000000000000000 : ℝ)*base66 + (88848900286286991001/14695000000000000000000000000000000 : ℝ)*base68 + (51959892338136991001/14695000000000000000000000000000000 : ℝ)*base70 + (106004455773043008999/14695000000000000000000000000000000 : ℝ)*base71 + (16460945460423/4592187500000000000000000000 : ℝ)*base74 + (32811019438103008999/14695000000000000000000000000000000 : ℝ)*base75 + (18352273804776991001/14695000000000000000000000000000000 : ℝ)*base78 + (35869363500116991001/14695000000000000000000000000000000 : ℝ)*base80 + (8855636248427/4592187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (17448963/2500000000000000000000 : ℝ)*base89 + (17448963/2500000000000000000000 : ℝ)*base91 + (17448963/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82597347263428372647631500531/7347500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1492165103/100000000000000 : ℝ)*(base19) + (1640598433/100000000000000 : ℝ)*(base23) + (298933017/100000000000000 : ℝ)*(upper3) + (100688169/100000000000000 : ℝ)*(lower4) + (88009769/50000000000000 : ℝ)*(upper5) + (1564128349178109/100000000000000 : ℝ)*(major0) + (1564128349178109/100000000000000 : ℝ)*(major1) + (1564128349178109/100000000000000 : ℝ)*(major2) + (10476188409/100000000000000 : ℝ)*(sp1) + (6263590267/50000000000000 : ℝ)*(sp2) + (2384358291371759/100000000000000 : ℝ)*(sp4) + (2384346323018247/100000000000000 : ℝ)*(sp5) + (298043015449099/12500000000000 : ℝ)*(sp6) + (148779606453171/20000000000000 : ℝ)*(sp7) + (148779606453171/20000000000000 : ℝ)*(f.failure) + (2384358291371759/100000000000000 : ℝ)*(f.sum) + (51450857867719/36737500000000000000000000000 : ℝ)*base65 + (43797398346396099941/14695000000000000000000000000000000 : ℝ)*base67 + (31520214440451099941/14695000000000000000000000000000000 : ℝ)*base69 + (65326388669081099941/14695000000000000000000000000000000 : ℝ)*base71 + (28010542004031/36737500000000000000000000000 : ℝ)*base74 + (128612806347516099941/14695000000000000000000000000000000 : ℝ)*base75 + (92209540316511099941/14695000000000000000000000000000000 : ℝ)*base77 + (46260780314381099941/14695000000000000000000000000000000 : ℝ)*base79 + (17488859919857/4592187500000000000000000000 : ℝ)*base82 + (2541069/1000000000000000000000 : ℝ)*base90 + (2541069/1000000000000000000000 : ℝ)*base92 + (2541069/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1744_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (105130561/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3237/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8883/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3637/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1744_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1744_s2_0 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1256423823/10000000000 : ℝ)*x 0 + (5505331267/10000000000 : ℝ)*x 1 + (2539588783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1256423823/10000000000 : ℝ)^5679 ≤ (199024013283/2500000000000 : ℝ)^4655 := by
    have hnat : (1256423823 : ℕ)^5679*2500000000000^4655 ≤ 199024013283^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256423823 10000000000 199024013283 2500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505331267/10000000000 : ℝ)^5679 ≤ (48279346780879/100000000000000 : ℝ)^4655 := by
    have hnat : (5505331267 : ℕ)^5679*100000000000000^4655 ≤ 48279346780879^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505331267 10000000000 48279346780879 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539588783/5000000000 : ℝ)^5679 ≤ (10939923165991/25000000000000 : ℝ)^4655 := by
    have hnat : (2539588783 : ℕ)^5679*25000000000000^4655 ≤ 10939923165991^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539588783 5000000000 10939923165991 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1256423823/10000000000 : ℝ), (5505331267/10000000000 : ℝ), (2539588783/5000000000 : ℝ)] ![(199024013283/2500000000000 : ℝ), (48279346780879/100000000000000 : ℝ), (10939923165991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1256423823/10000000000 : ℝ)|^5679 ≤ (199024013283/2500000000000 : ℝ)^4655
        have hw : |(-1256423823/10000000000 : ℝ)|=(1256423823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505331267/10000000000 : ℝ)|^5679 ≤ (48279346780879/100000000000000 : ℝ)^4655
        have hw : |(5505331267/10000000000 : ℝ)|=(5505331267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539588783/5000000000 : ℝ)|^5679 ≤ (10939923165991/25000000000000 : ℝ)^4655
        have hw : |(2539588783/5000000000 : ℝ)|=(2539588783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s2_1 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340524159/10000000000 : ℝ)*x 0 + (-46237301/312500000 : ℝ)*x 1 + (5079177353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340524159/10000000000 : ℝ)^5679 ≤ (465219800411/1000000000000 : ℝ)^4655 := by
    have hnat : (5340524159 : ℕ)^5679*1000000000000^4655 ≤ 465219800411^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340524159 10000000000 465219800411 1000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46237301/312500000 : ℝ)^5679 ≤ (2429582379251/25000000000000 : ℝ)^4655 := by
    have hnat : (46237301 : ℕ)^5679*25000000000000^4655 ≤ 2429582379251^4655*312500000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46237301 312500000 2429582379251 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5079177353/10000000000 : ℝ)^5679 ≤ (21879845212589/50000000000000 : ℝ)^4655 := by
    have hnat : (5079177353 : ℕ)^5679*50000000000000^4655 ≤ 21879845212589^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079177353 10000000000 21879845212589 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340524159/10000000000 : ℝ), (-46237301/312500000 : ℝ), (5079177353/10000000000 : ℝ)] ![(465219800411/1000000000000 : ℝ), (2429582379251/25000000000000 : ℝ), (21879845212589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340524159/10000000000 : ℝ)|^5679 ≤ (465219800411/1000000000000 : ℝ)^4655
        have hw : |(5340524159/10000000000 : ℝ)|=(5340524159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46237301/312500000 : ℝ)|^5679 ≤ (2429582379251/25000000000000 : ℝ)^4655
        have hw : |(-46237301/312500000 : ℝ)|=(46237301/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5079177353/10000000000 : ℝ)|^5679 ≤ (21879845212589/50000000000000 : ℝ)^4655
        have hw : |(5079177353/10000000000 : ℝ)|=(5079177353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s2_2 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333782739/625000000 : ℝ)*x 0 + (5079177659/10000000000 : ℝ)*x 1 + (-59183747/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333782739/625000000 : ℝ)^5679 ≤ (1860879059237/4000000000000 : ℝ)^4655 := by
    have hnat : (333782739 : ℕ)^5679*4000000000000^4655 ≤ 1860879059237^4655*625000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333782739 625000000 1860879059237 4000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079177659/10000000000 : ℝ)^5679 ≤ (21879846820731/50000000000000 : ℝ)^4655 := by
    have hnat : (5079177659 : ℕ)^5679*50000000000000^4655 ≤ 21879846820731^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079177659 10000000000 21879846820731 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59183747/400000000 : ℝ)^5679 ≤ (151848904087/1562500000000 : ℝ)^4655 := by
    have hnat : (59183747 : ℕ)^5679*1562500000000^4655 ≤ 151848904087^4655*400000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59183747 400000000 151848904087 1562500000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333782739/625000000 : ℝ), (5079177659/10000000000 : ℝ), (-59183747/400000000 : ℝ)] ![(1860879059237/4000000000000 : ℝ), (21879846820731/50000000000000 : ℝ), (151848904087/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333782739/625000000 : ℝ)|^5679 ≤ (1860879059237/4000000000000 : ℝ)^4655
        have hw : |(333782739/625000000 : ℝ)|=(333782739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079177659/10000000000 : ℝ)|^5679 ≤ (21879846820731/50000000000000 : ℝ)^4655
        have hw : |(5079177659/10000000000 : ℝ)|=(5079177659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59183747/400000000 : ℝ)|^5679 ≤ (151848904087/1562500000000 : ℝ)^4655
        have hw : |(-59183747/400000000 : ℝ)|=(59183747/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s2_3 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2016788277/5000000000 : ℝ)*x 0 + (1691484233/5000000000 : ℝ)*x 1 + (2374442551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016788277/5000000000 : ℝ)^5679 ≤ (825829989801/2500000000000 : ℝ)^4655 := by
    have hnat : (2016788277 : ℕ)^5679*2500000000000^4655 ≤ 825829989801^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016788277 5000000000 825829989801 2500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1691484233/5000000000 : ℝ)^5679 ≤ (2665346095621/10000000000000 : ℝ)^4655 := by
    have hnat : (1691484233 : ℕ)^5679*10000000000000^4655 ≤ 2665346095621^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691484233 5000000000 2665346095621 10000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2374442551/5000000000 : ℝ)^5679 ≤ (40313339434119/100000000000000 : ℝ)^4655 := by
    have hnat : (2374442551 : ℕ)^5679*100000000000000^4655 ≤ 40313339434119^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374442551 5000000000 40313339434119 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2016788277/5000000000 : ℝ), (1691484233/5000000000 : ℝ), (2374442551/5000000000 : ℝ)] ![(825829989801/2500000000000 : ℝ), (2665346095621/10000000000000 : ℝ), (40313339434119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2016788277/5000000000 : ℝ)|^5679 ≤ (825829989801/2500000000000 : ℝ)^4655
        have hw : |(2016788277/5000000000 : ℝ)|=(2016788277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1691484233/5000000000 : ℝ)|^5679 ≤ (2665346095621/10000000000000 : ℝ)^4655
        have hw : |(1691484233/5000000000 : ℝ)|=(1691484233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2374442551/5000000000 : ℝ)|^5679 ≤ (40313339434119/100000000000000 : ℝ)^4655
        have hw : |(2374442551/5000000000 : ℝ)|=(2374442551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s2_4 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-628394019/5000000000 : ℝ)*x 0 + (254302169/500000000 : ℝ)*x 1 + (5498320919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (628394019/5000000000 : ℝ)^5679 ≤ (398188800799/5000000000000 : ℝ)^4655 := by
    have hnat : (628394019 : ℕ)^5679*5000000000000^4655 ≤ 398188800799^4655*5000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628394019 5000000000 398188800799 5000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254302169/500000000 : ℝ)^5679 ≤ (5478983516887/12500000000000 : ℝ)^4655 := by
    have hnat : (254302169 : ℕ)^5679*12500000000000^4655 ≤ 5478983516887^4655*500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254302169 500000000 5478983516887 12500000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498320919/10000000000 : ℝ)^5679 ≤ (24102177916851/50000000000000 : ℝ)^4655 := by
    have hnat : (5498320919 : ℕ)^5679*50000000000000^4655 ≤ 24102177916851^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498320919 10000000000 24102177916851 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-628394019/5000000000 : ℝ), (254302169/500000000 : ℝ), (5498320919/10000000000 : ℝ)] ![(398188800799/5000000000000 : ℝ), (5478983516887/12500000000000 : ℝ), (24102177916851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-628394019/5000000000 : ℝ)|^5679 ≤ (398188800799/5000000000000 : ℝ)^4655
        have hw : |(-628394019/5000000000 : ℝ)|=(628394019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254302169/500000000 : ℝ)|^5679 ≤ (5478983516887/12500000000000 : ℝ)^4655
        have hw : |(254302169/500000000 : ℝ)|=(254302169/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498320919/10000000000 : ℝ)|^5679 ≤ (24102177916851/50000000000000 : ℝ)^4655
        have hw : |(5498320919/10000000000 : ℝ)|=(5498320919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s2_5 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227386779/10000000000 : ℝ)*x 0 + (-1060450477/10000000000 : ℝ)*x 1 + (1374580203/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227386779/10000000000 : ℝ)^5679 ≤ (45322442508297/100000000000000 : ℝ)^4655 := by
    have hnat : (5227386779 : ℕ)^5679*100000000000000^4655 ≤ 45322442508297^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227386779 10000000000 45322442508297 100000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060450477/10000000000 : ℝ)^5679 ≤ (1294640558081/20000000000000 : ℝ)^4655 := by
    have hnat : (1060450477 : ℕ)^5679*20000000000000^4655 ≤ 1294640558081^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060450477 10000000000 1294640558081 20000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374580203/2500000000 : ℝ)^5679 ≤ (9640870937853/20000000000000 : ℝ)^4655 := by
    have hnat : (1374580203 : ℕ)^5679*20000000000000^4655 ≤ 9640870937853^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374580203 2500000000 9640870937853 20000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227386779/10000000000 : ℝ), (-1060450477/10000000000 : ℝ), (1374580203/2500000000 : ℝ)] ![(45322442508297/100000000000000 : ℝ), (1294640558081/20000000000000 : ℝ), (9640870937853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227386779/10000000000 : ℝ)|^5679 ≤ (45322442508297/100000000000000 : ℝ)^4655
        have hw : |(5227386779/10000000000 : ℝ)|=(5227386779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060450477/10000000000 : ℝ)|^5679 ≤ (1294640558081/20000000000000 : ℝ)^4655
        have hw : |(-1060450477/10000000000 : ℝ)|=(1060450477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1374580203/2500000000 : ℝ)|^5679 ≤ (9640870937853/20000000000000 : ℝ)^4655
        have hw : |(1374580203/2500000000 : ℝ)|=(1374580203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s2_6 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045477363/2000000000 : ℝ)*x 0 + (343645047/625000000 : ℝ)*x 1 + (-1060450513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045477363/2000000000 : ℝ)^5679 ≤ (9064488577817/20000000000000 : ℝ)^4655 := by
    have hnat : (1045477363 : ℕ)^5679*20000000000000^4655 ≤ 9064488577817^4655*2000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045477363 2000000000 9064488577817 20000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343645047/625000000 : ℝ)^5679 ≤ (12051088511881/25000000000000 : ℝ)^4655 := by
    have hnat : (343645047 : ℕ)^5679*25000000000000^4655 ≤ 12051088511881^4655*625000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343645047 625000000 12051088511881 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060450513/10000000000 : ℝ)^5679 ≤ (101143797789/1562500000000 : ℝ)^4655 := by
    have hnat : (1060450513 : ℕ)^5679*1562500000000^4655 ≤ 101143797789^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060450513 10000000000 101143797789 1562500000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045477363/2000000000 : ℝ), (343645047/625000000 : ℝ), (-1060450513/10000000000 : ℝ)] ![(9064488577817/20000000000000 : ℝ), (12051088511881/25000000000000 : ℝ), (101143797789/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045477363/2000000000 : ℝ)|^5679 ≤ (9064488577817/20000000000000 : ℝ)^4655
        have hw : |(1045477363/2000000000 : ℝ)|=(1045477363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343645047/625000000 : ℝ)|^5679 ≤ (12051088511881/25000000000000 : ℝ)^4655
        have hw : |(343645047/625000000 : ℝ)|=(343645047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1060450513/10000000000 : ℝ)|^5679 ≤ (101143797789/1562500000000 : ℝ)^4655
        have hw : |(-1060450513/10000000000 : ℝ)|=(1060450513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1744_s2_7 (p : ℝ) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1008685837/2500000000 : ℝ)*x 0 + (4726878749/10000000000 : ℝ)*x 1 + (212839881/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008685837/2500000000 : ℝ)^5679 ≤ (1652242874869/5000000000000 : ℝ)^4655 := by
    have hnat : (1008685837 : ℕ)^5679*5000000000000^4655 ≤ 1652242874869^4655*2500000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008685837 2500000000 1652242874869 5000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4726878749/10000000000 : ℝ)^5679 ≤ (20042774444993/50000000000000 : ℝ)^4655 := by
    have hnat : (4726878749 : ℕ)^5679*50000000000000^4655 ≤ 20042774444993^4655*10000000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4726878749 10000000000 20042774444993 50000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212839881/625000000 : ℝ)^5679 ≤ (6717398401253/25000000000000 : ℝ)^4655 := by
    have hnat : (212839881 : ℕ)^5679*25000000000000^4655 ≤ 6717398401253^4655*625000000^5679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212839881 625000000 6717398401253 25000000000000 5679 4655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5679/1024 : ℝ)) 5679 4655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1008685837/2500000000 : ℝ), (4726878749/10000000000 : ℝ), (212839881/625000000 : ℝ)] ![(1652242874869/5000000000000 : ℝ), (20042774444993/50000000000000 : ℝ), (6717398401253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1008685837/2500000000 : ℝ)|^5679 ≤ (1652242874869/5000000000000 : ℝ)^4655
        have hw : |(1008685837/2500000000 : ℝ)|=(1008685837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4726878749/10000000000 : ℝ)|^5679 ≤ (20042774444993/50000000000000 : ℝ)^4655
        have hw : |(4726878749/10000000000 : ℝ)|=(4726878749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212839881/625000000 : ℝ)|^5679 ≤ (6717398401253/25000000000000 : ℝ)^4655
        have hw : |(212839881/625000000 : ℝ)|=(212839881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1744_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (105130561/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3637/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4479/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9047/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3637/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8883/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3637/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8883/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3637/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8883/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3637/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8883/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3637/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8883/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3637/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8883/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8883/100000 : ℝ) ^ (5663/1024 : ℝ) ≤ (153196000838877/100000000000000000000 : ℝ) := by
    have hpowers : (8883/100000 : ℝ)^5663 ≤ (153196000838877/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8883 : ℕ)^5663*100000000000000000000^1024 ≤ 153196000838877^1024*100000^5663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8883 100000 153196000838877 100000000000000000000 5663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8883/100000 : ℝ)) (X := (153196000838877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3637/20000 : ℝ) ^ (5663/1024 : ℝ) ≤ (8054009854760681/100000000000000000000 : ℝ) := by
    have hpowers : (3637/20000 : ℝ)^5663 ≤ (8054009854760681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3637 : ℕ)^5663*100000000000000000000^1024 ≤ 8054009854760681^1024*20000^5663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3637 20000 8054009854760681 100000000000000000000 5663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3637/20000 : ℝ)) (X := (8054009854760681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000153196000838877/50000000000000000000 : ℝ) ≤ (2500001385065407/2500000000000000 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (50000153196000838877/50000000000000000000 : ℝ)^1024 ≤ (2500001385065407/2500000000000000 : ℝ)^5663 := by
      have hnat : (50000153196000838877 : ℕ)^1024*2500000000000000^5663 ≤ 2500001385065407^5663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000153196000838877 50000000000000000000 2500001385065407 2500000000000000 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001385065407/2500000000000000 : ℝ)) (X := (50000153196000838877/50000000000000000000 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004103602927799779/50000000000000000000 : ℝ) ≤ (10000148400075883/10000000000000000 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (50004103602927799779/50000000000000000000 : ℝ)^1024 ≤ (10000148400075883/10000000000000000 : ℝ)^5663 := by
      have hnat : (50004103602927799779 : ℕ)^1024*10000000000000000^5663 ≤ 10000148400075883^5663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004103602927799779 50000000000000000000 10000148400075883 10000000000000000 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000148400075883/10000000000000000 : ℝ)) (X := (50004103602927799779/50000000000000000000 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008054009854760681/50000000000000000000 : ℝ) ≤ (5000145629945069/5000000000000000 : ℝ) ^ (5663/1024 : ℝ) := by
    have hpowers : (50008054009854760681/50000000000000000000 : ℝ)^1024 ≤ (5000145629945069/5000000000000000 : ℝ)^5663 := by
      have hnat : (50008054009854760681 : ℕ)^1024*5000000000000000^5663 ≤ 5000145629945069^5663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008054009854760681 50000000000000000000 5000145629945069 5000000000000000 1024 5663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000145629945069/5000000000000000 : ℝ)) (X := (50008054009854760681/50000000000000000000 : ℝ)) (by norm_num) 5663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(153196000838877/100000000000000000000 : ℝ) ≤ ((46508756744026804663/46510000000000000000 : ℝ)+2*(28571962851/186040000000000 : ℝ)*(8883/100000 : ℝ))^(5663/1024 : ℝ) := by
    rw [show (46508756744026804663/46510000000000000000 : ℝ)+2*(28571962851/186040000000000 : ℝ)*(8883/100000 : ℝ)=(2500001385065407/2500000000000000 : ℝ) by norm_num, show 1+2*(153196000838877/100000000000000000000 : ℝ)=(50000153196000838877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8054009854760681/100000000000000000000 : ℝ)+(153196000838877/100000000000000000000 : ℝ) ≤ ((46508756744026804663/46510000000000000000 : ℝ)+(28571962851/186040000000000 : ℝ)*((3637/20000 : ℝ)+(8883/100000 : ℝ)))^(5663/1024 : ℝ) := by
    rw [show (46508756744026804663/46510000000000000000 : ℝ)+(28571962851/186040000000000 : ℝ)*((3637/20000 : ℝ)+(8883/100000 : ℝ))=(10000148400075883/10000000000000000 : ℝ) by norm_num, show 1+(8054009854760681/100000000000000000000 : ℝ)+(153196000838877/100000000000000000000 : ℝ)=(50004103602927799779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8054009854760681/100000000000000000000 : ℝ) ≤ ((46508756744026804663/46510000000000000000 : ℝ)+2*(28571962851/186040000000000 : ℝ)*(3637/20000 : ℝ))^(5663/1024 : ℝ) := by
    rw [show (46508756744026804663/46510000000000000000 : ℝ)+2*(28571962851/186040000000000 : ℝ)*(3637/20000 : ℝ)=(5000145629945069/5000000000000000 : ℝ) by norm_num, show 1+2*(8054009854760681/100000000000000000000 : ℝ)=(50008054009854760681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46508756744026804663/46510000000000000000 : ℝ)*(X 1 0+X 2 0)+(28571962851/186040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (8883/100000 : ℝ)) (hi := (3637/20000 : ℝ)) (c := (46508756744026804663/46510000000000000000 : ℝ)) (alpha := (28571962851/186040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46508756744026804663/46510000000000000000 : ℝ)*(X 0 1+X 2 1)+(28571962851/186040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (8883/100000 : ℝ)) (hi := (3637/20000 : ℝ)) (c := (46508756744026804663/46510000000000000000 : ℝ)) (alpha := (28571962851/186040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46508756744026804663/46510000000000000000 : ℝ)*(X 0 2+X 1 2)+(28571962851/186040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5663/1024 : ℝ)) (lo := (8883/100000 : ℝ)) (hi := (3637/20000 : ℝ)) (c := (46508756744026804663/46510000000000000000 : ℝ)) (alpha := (28571962851/186040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1256423823/10000000000 : ℝ)*X 0 0+(5505331267/10000000000 : ℝ)*X 0 1+(2539588783/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5340524159/10000000000 : ℝ)*X 1 0+(-46237301/312500000 : ℝ)*X 1 1+(5079177353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((333782739/625000000 : ℝ)*X 2 0+(5079177659/10000000000 : ℝ)*X 2 1+(-59183747/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2016788277/5000000000 : ℝ)*X 0 0+(1691484233/5000000000 : ℝ)*X 0 1+(2374442551/5000000000 : ℝ)*X 0 2+(2016788277/5000000000 : ℝ)*X 1 0+(1691484233/5000000000 : ℝ)*X 1 1+(2374442551/5000000000 : ℝ)*X 1 2+(2016788277/5000000000 : ℝ)*X 2 0+(1691484233/5000000000 : ℝ)*X 2 1+(2374442551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-628394019/5000000000 : ℝ)*X 0 0+(254302169/500000000 : ℝ)*X 0 1+(5498320919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5227386779/10000000000 : ℝ)*X 1 0+(-1060450477/10000000000 : ℝ)*X 1 1+(1374580203/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1045477363/2000000000 : ℝ)*X 2 0+(343645047/625000000 : ℝ)*X 2 1+(-1060450513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1008685837/2500000000 : ℝ)*X 0 0+(4726878749/10000000000 : ℝ)*X 0 1+(212839881/625000000 : ℝ)*X 0 2+(1008685837/2500000000 : ℝ)*X 1 0+(4726878749/10000000000 : ℝ)*X 1 1+(212839881/625000000 : ℝ)*X 1 2+(1008685837/2500000000 : ℝ)*X 2 0+(4726878749/10000000000 : ℝ)*X 2 1+(212839881/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1744_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5088246381322316797320246723/1162750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (783968613/100000000000000 : ℝ)*(base19) + (553684533/100000000000000 : ℝ)*(base23) + (44373293/100000000000000 : ℝ)*(lower2) + (34081571/25000000000000 : ℝ)*(upper3) + (18212261/50000000000000 : ℝ)*(upper5) + (769673539453069/50000000000000 : ℝ)*(major0) + (769673539453069/50000000000000 : ℝ)*(major1) + (769673539453069/50000000000000 : ℝ)*(major2) + (14666107315703/625000000000 : ℝ)*(sp0) + (469316229100417/20000000000000 : ℝ)*(sp1) + (469316275157233/20000000000000 : ℝ)*(sp2) + (183027589874101/25000000000000 : ℝ)*(sp3) + (2379479109/50000000000000 : ℝ)*(sp4) + (861488499/50000000000000 : ℝ)*(sp7) + (732112082473401/100000000000000 : ℝ)*(f.failure) + (1173290964735349/50000000000000 : ℝ)*(f.sum) + (26533412425477/4651000000000000000000000000 : ℝ)*base66 + (32290094663684389253/2325500000000000000000000000000000 : ℝ)*base68 + (5295584323220389253/2325500000000000000000000000000000 : ℝ)*base70 + (23269647295043889253/2325500000000000000000000000000000 : ℝ)*base72 + (34353953813227/4651000000000000000000000000 : ℝ)*base74 + (28854980606186889253/2325500000000000000000000000000000 : ℝ)*base76 + (27420021666391389253/2325500000000000000000000000000000 : ℝ)*base78 + (22792935761926889253/2325500000000000000000000000000000 : ℝ)*base80 + (728751019107/1162750000000000000000000000 : ℝ)*base81 + (14707961/5000000000000000000000 : ℝ)*base89 + (14707961/5000000000000000000000 : ℝ)*base91 + (14707961/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3318993626486319801565328121/1162750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (193218813/50000000000000 : ℝ)*(base19) + (16167639/4000000000000 : ℝ)*(base23) + (12221/195312500000 : ℝ)*(upper2) + (38911833/100000000000000 : ℝ)*(upper3) + (9103711/12500000000000 : ℝ)*(upper5) + (795575193912663/50000000000000 : ℝ)*(major0) + (795575193912663/50000000000000 : ℝ)*(major1) + (795575193912663/50000000000000 : ℝ)*(major2) + (2602846131/100000000000000 : ℝ)*(sp1) + (524566361/25000000000000 : ℝ)*(sp2) + (606387747756521/25000000000000 : ℝ)*(sp4) + (2425548001742327/100000000000000 : ℝ)*(sp5) + (37899195133901/1562500000000 : ℝ)*(sp6) + (189187422369187/25000000000000 : ℝ)*(sp7) + (189187422369187/25000000000000 : ℝ)*(f.failure) + (606387747756521/25000000000000 : ℝ)*(f.sum) + (486023622301/4651000000000000000000000000 : ℝ)*base65 + (6007481344849602431/2325500000000000000000000000000000 : ℝ)*base68 + (18763757724665602431/2325500000000000000000000000000000 : ℝ)*base70 + (16982663930246602431/2325500000000000000000000000000000 : ℝ)*base72 + (13794487797541/2325500000000000000000000000 : ℝ)*base73 + (22932052692026102431/2325500000000000000000000000000000 : ℝ)*base76 + (13891712708023602431/2325500000000000000000000000000000 : ℝ)*base78 + (6588528458651602431/2325500000000000000000000000000000 : ℝ)*base80 + (15227840831337/4651000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3423907/1250000000000000000000 : ℝ)*base89 + (3423907/1250000000000000000000 : ℝ)*base91 + (3423907/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1744_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (105130561/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3637/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4479/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1744_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1744_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (105130561/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4479/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9047/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1744_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1744_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1744_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5663/1024 : ℝ) ≤ p) (hpb : p ≤ (5679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (105130561/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4479/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9047/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1744_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

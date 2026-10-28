-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1115_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:07:15.962274+00:00
-- url     : https://prove2.me/submissions/65a420e6-c909-4126-86a8-116369877a57

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
theorem support_rectangle_w1115_s9_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334052373/625000000 : ℝ)*x 0 + (8424549/16000000 : ℝ)*x 1 + (-280607579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334052373/625000000 : ℝ)^2077 ≤ (5442977774769/12500000000000 : ℝ)^1565 := by
    have hnat : (334052373 : ℕ)^2077*12500000000000^1565 ≤ 5442977774769^1565*625000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334052373 625000000 5442977774769 12500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8424549/16000000 : ℝ)^2077 ≤ (42686406041513/100000000000000 : ℝ)^1565 := by
    have hnat : (8424549 : ℕ)^2077*100000000000000^1565 ≤ 42686406041513^1565*16000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8424549 16000000 42686406041513 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280607579/1250000000 : ℝ)^2077 ≤ (6884885874139/50000000000000 : ℝ)^1565 := by
    have hnat : (280607579 : ℕ)^2077*50000000000000^1565 ≤ 6884885874139^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280607579 1250000000 6884885874139 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334052373/625000000 : ℝ), (8424549/16000000 : ℝ), (-280607579/1250000000 : ℝ)] ![(5442977774769/12500000000000 : ℝ), (42686406041513/100000000000000 : ℝ), (6884885874139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334052373/625000000 : ℝ)|^2077 ≤ (5442977774769/12500000000000 : ℝ)^1565
        have hw : |(334052373/625000000 : ℝ)|=(334052373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8424549/16000000 : ℝ)|^2077 ≤ (42686406041513/100000000000000 : ℝ)^1565
        have hw : |(8424549/16000000 : ℝ)|=(8424549/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280607579/1250000000 : ℝ)|^2077 ≤ (6884885874139/50000000000000 : ℝ)^1565
        have hw : |(-280607579/1250000000 : ℝ)|=(280607579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s9_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4368493317/10000000000 : ℝ)*x 0 + (4243561503/10000000000 : ℝ)*x 1 + (4497109457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368493317/10000000000 : ℝ)^2077 ≤ (33316841879749/100000000000000 : ℝ)^1565 := by
    have hnat : (4368493317 : ℕ)^2077*100000000000000^1565 ≤ 33316841879749^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368493317 10000000000 33316841879749 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243561503/10000000000 : ℝ)^2077 ≤ (16029135509243/50000000000000 : ℝ)^1565 := by
    have hnat : (4243561503 : ℕ)^2077*50000000000000^1565 ≤ 16029135509243^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243561503 10000000000 16029135509243 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497109457/10000000000 : ℝ)^2077 ≤ (17312443546069/50000000000000 : ℝ)^1565 := by
    have hnat : (4497109457 : ℕ)^2077*50000000000000^1565 ≤ 17312443546069^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497109457 10000000000 17312443546069 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368493317/10000000000 : ℝ), (4243561503/10000000000 : ℝ), (4497109457/10000000000 : ℝ)] ![(33316841879749/100000000000000 : ℝ), (16029135509243/50000000000000 : ℝ), (17312443546069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368493317/10000000000 : ℝ)|^2077 ≤ (33316841879749/100000000000000 : ℝ)^1565
        have hw : |(4368493317/10000000000 : ℝ)|=(4368493317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243561503/10000000000 : ℝ)|^2077 ≤ (16029135509243/50000000000000 : ℝ)^1565
        have hw : |(4243561503/10000000000 : ℝ)|=(4243561503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497109457/10000000000 : ℝ)|^2077 ≤ (17312443546069/50000000000000 : ℝ)^1565
        have hw : |(4497109457/10000000000 : ℝ)|=(4497109457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s9_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-435974539/2000000000 : ℝ)*x 0 + (164552043/312500000 : ℝ)*x 1 + (674142889/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435974539/2000000000 : ℝ)^2077 ≤ (6621624475797/50000000000000 : ℝ)^1565 := by
    have hnat : (435974539 : ℕ)^2077*50000000000000^1565 ≤ 6621624475797^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435974539 2000000000 6621624475797 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164552043/312500000 : ℝ)^2077 ≤ (42689873279797/100000000000000 : ℝ)^1565 := by
    have hnat : (164552043 : ℕ)^2077*100000000000000^1565 ≤ 42689873279797^1565*312500000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164552043 312500000 42689873279797 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674142889/1250000000 : ℝ)^2077 ≤ (22033438877913/50000000000000 : ℝ)^1565 := by
    have hnat : (674142889 : ℕ)^2077*50000000000000^1565 ≤ 22033438877913^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674142889 1250000000 22033438877913 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435974539/2000000000 : ℝ), (164552043/312500000 : ℝ), (674142889/1250000000 : ℝ)] ![(6621624475797/50000000000000 : ℝ), (42689873279797/100000000000000 : ℝ), (22033438877913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435974539/2000000000 : ℝ)|^2077 ≤ (6621624475797/50000000000000 : ℝ)^1565
        have hw : |(-435974539/2000000000 : ℝ)|=(435974539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164552043/312500000 : ℝ)|^2077 ≤ (42689873279797/100000000000000 : ℝ)^1565
        have hw : |(164552043/312500000 : ℝ)|=(164552043/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674142889/1250000000 : ℝ)|^2077 ≤ (22033438877913/50000000000000 : ℝ)^1565
        have hw : |(674142889/1250000000 : ℝ)|=(674142889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s9_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328110779/2500000000 : ℝ)*x 0 + (-2117060881/10000000000 : ℝ)*x 1 + (5393143027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328110779/2500000000 : ℝ)^2077 ≤ (21596955121707/50000000000000 : ℝ)^1565 := by
    have hnat : (1328110779 : ℕ)^2077*50000000000000^1565 ≤ 21596955121707^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328110779 2500000000 21596955121707 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117060881/10000000000 : ℝ)^2077 ≤ (3184803225919/25000000000000 : ℝ)^1565 := by
    have hnat : (2117060881 : ℕ)^2077*25000000000000^1565 ≤ 3184803225919^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117060881 10000000000 3184803225919 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393143027/10000000000 : ℝ)^2077 ≤ (44066876834079/100000000000000 : ℝ)^1565 := by
    have hnat : (5393143027 : ℕ)^2077*100000000000000^1565 ≤ 44066876834079^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393143027 10000000000 44066876834079 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328110779/2500000000 : ℝ), (-2117060881/10000000000 : ℝ), (5393143027/10000000000 : ℝ)] ![(21596955121707/50000000000000 : ℝ), (3184803225919/25000000000000 : ℝ), (44066876834079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328110779/2500000000 : ℝ)|^2077 ≤ (21596955121707/50000000000000 : ℝ)^1565
        have hw : |(1328110779/2500000000 : ℝ)|=(1328110779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117060881/10000000000 : ℝ)|^2077 ≤ (3184803225919/25000000000000 : ℝ)^1565
        have hw : |(-2117060881/10000000000 : ℝ)|=(2117060881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393143027/10000000000 : ℝ)|^2077 ≤ (44066876834079/100000000000000 : ℝ)^1565
        have hw : |(5393143027/10000000000 : ℝ)|=(5393143027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s9_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656222209/5000000000 : ℝ)*x 0 + (2696571761/5000000000 : ℝ)*x 1 + (-2117058451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656222209/5000000000 : ℝ)^2077 ≤ (4319392429293/10000000000000 : ℝ)^1565 := by
    have hnat : (2656222209 : ℕ)^2077*10000000000000^1565 ≤ 4319392429293^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656222209 5000000000 4319392429293 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696571761/5000000000 : ℝ)^2077 ≤ (5508360275237/12500000000000 : ℝ)^1565 := by
    have hnat : (2696571761 : ℕ)^2077*12500000000000^1565 ≤ 5508360275237^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696571761 5000000000 5508360275237 12500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117058451/10000000000 : ℝ)^2077 ≤ (2547838699521/20000000000000 : ℝ)^1565 := by
    have hnat : (2117058451 : ℕ)^2077*20000000000000^1565 ≤ 2547838699521^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117058451 10000000000 2547838699521 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656222209/5000000000 : ℝ), (2696571761/5000000000 : ℝ), (-2117058451/10000000000 : ℝ)] ![(4319392429293/10000000000000 : ℝ), (5508360275237/12500000000000 : ℝ), (2547838699521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656222209/5000000000 : ℝ)|^2077 ≤ (4319392429293/10000000000000 : ℝ)^1565
        have hw : |(2656222209/5000000000 : ℝ)|=(2656222209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696571761/5000000000 : ℝ)|^2077 ≤ (5508360275237/12500000000000 : ℝ)^1565
        have hw : |(2696571761/5000000000 : ℝ)|=(2696571761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117058451/10000000000 : ℝ)|^2077 ≤ (2547838699521/20000000000000 : ℝ)^1565
        have hw : |(-2117058451/10000000000 : ℝ)|=(2117058451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s9_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4368504379/10000000000 : ℝ)*x 0 + (2248236459/5000000000 : ℝ)*x 1 + (4244199043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368504379/10000000000 : ℝ)^2077 ≤ (33316953846259/100000000000000 : ℝ)^1565 := by
    have hnat : (4368504379 : ℕ)^2077*100000000000000^1565 ≤ 33316953846259^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368504379 10000000000 33316953846259 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248236459/5000000000 : ℝ)^2077 ≤ (865459573001/2500000000000 : ℝ)^1565 := by
    have hnat : (2248236459 : ℕ)^2077*2500000000000^1565 ≤ 865459573001^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248236459 5000000000 865459573001 2500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244199043/10000000000 : ℝ)^2077 ≤ (3206466321121/10000000000000 : ℝ)^1565 := by
    have hnat : (4244199043 : ℕ)^2077*10000000000000^1565 ≤ 3206466321121^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244199043 10000000000 3206466321121 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368504379/10000000000 : ℝ), (2248236459/5000000000 : ℝ), (4244199043/10000000000 : ℝ)] ![(33316953846259/100000000000000 : ℝ), (865459573001/2500000000000 : ℝ), (3206466321121/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368504379/10000000000 : ℝ)|^2077 ≤ (33316953846259/100000000000000 : ℝ)^1565
        have hw : |(4368504379/10000000000 : ℝ)|=(4368504379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248236459/5000000000 : ℝ)|^2077 ≤ (865459573001/2500000000000 : ℝ)^1565
        have hw : |(2248236459/5000000000 : ℝ)|=(2248236459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244199043/10000000000 : ℝ)|^2077 ≤ (3206466321121/10000000000000 : ℝ)^1565
        have hw : |(4244199043/10000000000 : ℝ)|=(4244199043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s9_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-94585099/10000000000 : ℝ)*x 0 + (2882222643/5000000000 : ℝ)*x 1 + (3039556283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94585099/10000000000 : ℝ)^2077 ≤ (205873225623/100000000000000 : ℝ)^1565 := by
    have hnat : (94585099 : ℕ)^2077*100000000000000^1565 ≤ 205873225623^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94585099 10000000000 205873225623 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2882222643/5000000000 : ℝ)^2077 ≤ (48137970625151/100000000000000 : ℝ)^1565 := by
    have hnat : (2882222643 : ℕ)^2077*100000000000000^1565 ≤ 48137970625151^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2882222643 5000000000 48137970625151 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3039556283/5000000000 : ℝ)^2077 ≤ (322850975833/625000000000 : ℝ)^1565 := by
    have hnat : (3039556283 : ℕ)^2077*625000000000^1565 ≤ 322850975833^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3039556283 5000000000 322850975833 625000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94585099/10000000000 : ℝ), (2882222643/5000000000 : ℝ), (3039556283/5000000000 : ℝ)] ![(205873225623/100000000000000 : ℝ), (48137970625151/100000000000000 : ℝ), (322850975833/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94585099/10000000000 : ℝ)|^2077 ≤ (205873225623/100000000000000 : ℝ)^1565
        have hw : |(-94585099/10000000000 : ℝ)|=(94585099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2882222643/5000000000 : ℝ)|^2077 ≤ (48137970625151/100000000000000 : ℝ)^1565
        have hw : |(2882222643/5000000000 : ℝ)|=(2882222643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3039556283/5000000000 : ℝ)|^2077 ≤ (322850975833/625000000000 : ℝ)^1565
        have hw : |(3039556283/5000000000 : ℝ)|=(3039556283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5659/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (877/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5659/50000 : ℝ) ^ (8307/2048 : ℝ) ≤ (14519301001064511/100000000000000000000 : ℝ) := by
    have hpowers : (5659/50000 : ℝ)^8307 ≤ (14519301001064511/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5659 : ℕ)^8307*100000000000000000000^2048 ≤ 14519301001064511^2048*50000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5659 50000 14519301001064511 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5659/50000 : ℝ)) (X := (14519301001064511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14033/100000 : ℝ) ^ (8307/2048 : ℝ) ≤ (8682656353450299/25000000000000000000 : ℝ) := by
    have hpowers : (14033/100000 : ℝ)^8307 ≤ (8682656353450299/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14033 : ℕ)^8307*25000000000000000000^2048 ≤ 8682656353450299^2048*100000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14033 100000 8682656353450299 25000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14033/100000 : ℝ)) (X := (8682656353450299/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014519301001064511/50000000000000000000 : ℝ) ≤ (2500178959167069/2500000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50014519301001064511/50000000000000000000 : ℝ)^2048 ≤ (2500178959167069/2500000000000000 : ℝ)^8307 := by
      have hnat : (50014519301001064511 : ℕ)^2048*2500000000000000^8307 ≤ 2500178959167069^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014519301001064511 50000000000000000000 2500178959167069 2500000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500178959167069/2500000000000000 : ℝ)) (X := (50014519301001064511/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049249926414865707/100000000000000000000 : ℝ) ≤ (10001213977855507/10000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (100049249926414865707/100000000000000000000 : ℝ)^2048 ≤ (10001213977855507/10000000000000000 : ℝ)^8307 := by
      have hnat : (100049249926414865707 : ℕ)^2048*10000000000000000^8307 ≤ 10001213977855507^8307*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049249926414865707 100000000000000000000 10001213977855507 10000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001213977855507/10000000000000000 : ℝ)) (X := (100049249926414865707/100000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508682656353450299/12500000000000000000 : ℝ) ≤ (5000856059521369/5000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (12508682656353450299/12500000000000000000 : ℝ)^2048 ≤ (5000856059521369/5000000000000000 : ℝ)^8307 := by
      have hnat : (12508682656353450299 : ℕ)^2048*5000000000000000^8307 ≤ 5000856059521369^8307*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508682656353450299 12500000000000000000 5000856059521369 5000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000856059521369/5000000000000000 : ℝ)) (X := (12508682656353450299/12500000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14519301001064511/100000000000000000000 : ℝ) ≤ ((3392583446580026053/3393750000000000000 : ℝ)+2*(498141187231/271500000000000 : ℝ)*(5659/50000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (3392583446580026053/3393750000000000000 : ℝ)+2*(498141187231/271500000000000 : ℝ)*(5659/50000 : ℝ)=(2500178959167069/2500000000000000 : ℝ) by norm_num, show 1+2*(14519301001064511/100000000000000000000 : ℝ)=(50014519301001064511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8682656353450299/25000000000000000000 : ℝ)+(14519301001064511/100000000000000000000 : ℝ) ≤ ((3392583446580026053/3393750000000000000 : ℝ)+(498141187231/271500000000000 : ℝ)*((14033/100000 : ℝ)+(5659/50000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (3392583446580026053/3393750000000000000 : ℝ)+(498141187231/271500000000000 : ℝ)*((14033/100000 : ℝ)+(5659/50000 : ℝ))=(10001213977855507/10000000000000000 : ℝ) by norm_num, show 1+(8682656353450299/25000000000000000000 : ℝ)+(14519301001064511/100000000000000000000 : ℝ)=(100049249926414865707/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8682656353450299/25000000000000000000 : ℝ) ≤ ((3392583446580026053/3393750000000000000 : ℝ)+2*(498141187231/271500000000000 : ℝ)*(14033/100000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (3392583446580026053/3393750000000000000 : ℝ)+2*(498141187231/271500000000000 : ℝ)*(14033/100000 : ℝ)=(5000856059521369/5000000000000000 : ℝ) by norm_num, show 1+2*(8682656353450299/25000000000000000000 : ℝ)=(12508682656353450299/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3392583446580026053/3393750000000000000 : ℝ)*(X 1 0+X 2 0)+(498141187231/271500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (3392583446580026053/3393750000000000000 : ℝ)) (alpha := (498141187231/271500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3392583446580026053/3393750000000000000 : ℝ)*(X 0 1+X 2 1)+(498141187231/271500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (3392583446580026053/3393750000000000000 : ℝ)) (alpha := (498141187231/271500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3392583446580026053/3393750000000000000 : ℝ)*(X 0 2+X 1 2)+(498141187231/271500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (3392583446580026053/3393750000000000000 : ℝ)) (alpha := (498141187231/271500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((334052373/625000000 : ℝ)*X 2 0+(8424549/16000000 : ℝ)*X 2 1+(-280607579/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4368493317/10000000000 : ℝ)*X 0 0+(4243561503/10000000000 : ℝ)*X 0 1+(4497109457/10000000000 : ℝ)*X 0 2+(4368493317/10000000000 : ℝ)*X 1 0+(4243561503/10000000000 : ℝ)*X 1 1+(4497109457/10000000000 : ℝ)*X 1 2+(4368493317/10000000000 : ℝ)*X 2 0+(4243561503/10000000000 : ℝ)*X 2 1+(4497109457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-435974539/2000000000 : ℝ)*X 0 0+(164552043/312500000 : ℝ)*X 0 1+(674142889/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1328110779/2500000000 : ℝ)*X 1 0+(-2117060881/10000000000 : ℝ)*X 1 1+(5393143027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2656222209/5000000000 : ℝ)*X 2 0+(2696571761/5000000000 : ℝ)*X 2 1+(-2117058451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4368504379/10000000000 : ℝ)*X 0 0+(2248236459/5000000000 : ℝ)*X 0 1+(4244199043/10000000000 : ℝ)*X 0 2+(4368504379/10000000000 : ℝ)*X 1 0+(2248236459/5000000000 : ℝ)*X 1 1+(4244199043/10000000000 : ℝ)*X 1 2+(4368504379/10000000000 : ℝ)*X 2 0+(2248236459/5000000000 : ℝ)*X 2 1+(4244199043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-94585099/10000000000 : ℝ)*X 0 0+(2882222643/5000000000 : ℝ)*X 0 1+(3039556283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s9_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21414415528232186183403619/14140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (948464481/50000000000000 : ℝ)*(lower2) + (112238831/20000000000000 : ℝ)*(lower3) + (4602411/800000000000 : ℝ)*(lower4) + (95355291/20000000000000 : ℝ)*(lower5) + (369018200668181/6250000000000 : ℝ)*(major0) + (369018200668181/6250000000000 : ℝ)*(major1) + (369018200668181/6250000000000 : ℝ)*(major2) + (46346440473/50000000000000 : ℝ)*(sp0) + (22753010533/100000000000000 : ℝ)*(sp1) + (1568911670768559/20000000000000 : ℝ)*(sp2) + (392228278142117/5000000000000 : ℝ)*(sp3) + (7844472869961393/100000000000000 : ℝ)*(sp4) + (1981997027524627/50000000000000 : ℝ)*(sp5) + (901124943/12500000000000 : ℝ)*(sp6) + (1982008404029893/50000000000000 : ℝ)*(f.failure) + (392228278142117/5000000000000 : ℝ)*(f.sum) + (23831547594763/6787500000000000000000000000 : ℝ)*base65 + (118087838324228687/14140625000000000000000000000000 : ℝ)*base67 + (136044542428271313/14140625000000000000000000000000 : ℝ)*base70 + (611308123664208813/14140625000000000000000000000000 : ℝ)*base72 + (37551237174349/13575000000000000000000000000 : ℝ)*base74 + (156797539124833813/14140625000000000000000000000000 : ℝ)*base76 + (60906645673740063/14140625000000000000000000000000 : ℝ)*base78 + (25398877882958813/14140625000000000000000000000000 : ℝ)*base80 + (13161529167031/3393750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5978153/5000000000000000000000 : ℝ)*base90 + (5978153/5000000000000000000000 : ℝ)*base92 + (5978153/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1115_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (877/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1115_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1115_s10_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089936229/5000000000 : ℝ)*x 0 + (5393459437/10000000000 : ℝ)*x 1 + (5265346737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089936229/5000000000 : ℝ)^2077 ≤ (1655405880089/12500000000000 : ℝ)^1565 := by
    have hnat : (1089936229 : ℕ)^2077*12500000000000^1565 ≤ 1655405880089^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089936229 5000000000 1655405880089 12500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393459437/10000000000 : ℝ)^2077 ≤ (44070308040587/100000000000000 : ℝ)^1565 := by
    have hnat : (5393459437 : ℕ)^2077*100000000000000^1565 ≤ 44070308040587^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393459437 10000000000 44070308040587 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265346737/10000000000 : ℝ)^2077 ≤ (42686444904203/100000000000000 : ℝ)^1565 := by
    have hnat : (5265346737 : ℕ)^2077*100000000000000^1565 ≤ 42686444904203^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265346737 10000000000 42686444904203 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089936229/5000000000 : ℝ), (5393459437/10000000000 : ℝ), (5265346737/10000000000 : ℝ)] ![(1655405880089/12500000000000 : ℝ), (44070308040587/100000000000000 : ℝ), (42686444904203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089936229/5000000000 : ℝ)|^2077 ≤ (1655405880089/12500000000000 : ℝ)^1565
        have hw : |(-1089936229/5000000000 : ℝ)|=(1089936229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393459437/10000000000 : ℝ)|^2077 ≤ (44070308040587/100000000000000 : ℝ)^1565
        have hw : |(5393459437/10000000000 : ℝ)|=(5393459437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265346737/10000000000 : ℝ)|^2077 ≤ (42686444904203/100000000000000 : ℝ)^1565
        have hw : |(5265346737/10000000000 : ℝ)|=(5265346737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s10_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66810443/125000000 : ℝ)*x 0 + (-561214703/2500000000 : ℝ)*x 1 + (2632673521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66810443/125000000 : ℝ)^2077 ≤ (43543794864907/100000000000000 : ℝ)^1565 := by
    have hnat : (66810443 : ℕ)^2077*100000000000000^1565 ≤ 43543794864907^1565*125000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66810443 125000000 43543794864907 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561214703/2500000000 : ℝ)^2077 ≤ (13769756932283/100000000000000 : ℝ)^1565 := by
    have hnat : (561214703 : ℕ)^2077*100000000000000^1565 ≤ 13769756932283^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561214703 2500000000 13769756932283 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632673521/5000000000 : ℝ)^2077 ≤ (21343224092899/50000000000000 : ℝ)^1565 := by
    have hnat : (2632673521 : ℕ)^2077*50000000000000^1565 ≤ 21343224092899^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632673521 5000000000 21343224092899 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66810443/125000000 : ℝ), (-561214703/2500000000 : ℝ), (2632673521/5000000000 : ℝ)] ![(43543794864907/100000000000000 : ℝ), (13769756932283/100000000000000 : ℝ), (21343224092899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66810443/125000000 : ℝ)|^2077 ≤ (43543794864907/100000000000000 : ℝ)^1565
        have hw : |(66810443/125000000 : ℝ)|=(66810443/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561214703/2500000000 : ℝ)|^2077 ≤ (13769756932283/100000000000000 : ℝ)^1565
        have hw : |(-561214703/2500000000 : ℝ)|=(561214703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632673521/5000000000 : ℝ)|^2077 ≤ (21343224092899/50000000000000 : ℝ)^1565
        have hw : |(2632673521/5000000000 : ℝ)|=(2632673521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s10_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334052221/625000000 : ℝ)*x 0 + (5265346919/10000000000 : ℝ)*x 1 + (-1122429423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334052221/625000000 : ℝ)^2077 ≤ (21771897951439/50000000000000 : ℝ)^1565 := by
    have hnat : (334052221 : ℕ)^2077*50000000000000^1565 ≤ 21771897951439^1565*625000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334052221 625000000 21771897951439 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265346919/10000000000 : ℝ)^2077 ≤ (26679029289/62500000000 : ℝ)^1565 := by
    have hnat : (5265346919 : ℕ)^2077*62500000000^1565 ≤ 26679029289^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265346919 10000000000 26679029289 62500000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122429423/5000000000 : ℝ)^2077 ≤ (2753951441813/20000000000000 : ℝ)^1565 := by
    have hnat : (1122429423 : ℕ)^2077*20000000000000^1565 ≤ 2753951441813^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122429423 5000000000 2753951441813 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334052221/625000000 : ℝ), (5265346919/10000000000 : ℝ), (-1122429423/5000000000 : ℝ)] ![(21771897951439/50000000000000 : ℝ), (26679029289/62500000000 : ℝ), (2753951441813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334052221/625000000 : ℝ)|^2077 ≤ (21771897951439/50000000000000 : ℝ)^1565
        have hw : |(334052221/625000000 : ℝ)|=(334052221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265346919/10000000000 : ℝ)|^2077 ≤ (26679029289/62500000000 : ℝ)^1565
        have hw : |(5265346919/10000000000 : ℝ)|=(5265346919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122429423/5000000000 : ℝ)|^2077 ≤ (2753951441813/20000000000000 : ℝ)^1565
        have hw : |(-1122429423/5000000000 : ℝ)|=(1122429423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s10_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (873698771/2000000000 : ℝ)*x 0 + (4243572147/10000000000 : ℝ)*x 1 + (4497098479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873698771/2000000000 : ℝ)^2077 ≤ (16658423662617/50000000000000 : ℝ)^1565 := by
    have hnat : (873698771 : ℕ)^2077*50000000000000^1565 ≤ 16658423662617^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873698771 2000000000 16658423662617 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243572147/10000000000 : ℝ)^2077 ≤ (32058377736269/100000000000000 : ℝ)^1565 := by
    have hnat : (4243572147 : ℕ)^2077*100000000000000^1565 ≤ 32058377736269^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243572147 10000000000 32058377736269 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497098479/10000000000 : ℝ)^2077 ≤ (16906628377/48828125000 : ℝ)^1565 := by
    have hnat : (4497098479 : ℕ)^2077*48828125000^1565 ≤ 16906628377^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497098479 10000000000 16906628377 48828125000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873698771/2000000000 : ℝ), (4243572147/10000000000 : ℝ), (4497098479/10000000000 : ℝ)] ![(16658423662617/50000000000000 : ℝ), (32058377736269/100000000000000 : ℝ), (16906628377/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873698771/2000000000 : ℝ)|^2077 ≤ (16658423662617/50000000000000 : ℝ)^1565
        have hw : |(873698771/2000000000 : ℝ)|=(873698771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243572147/10000000000 : ℝ)|^2077 ≤ (32058377736269/100000000000000 : ℝ)^1565
        have hw : |(4243572147/10000000000 : ℝ)|=(4243572147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497098479/10000000000 : ℝ)|^2077 ≤ (16906628377/48828125000 : ℝ)^1565
        have hw : |(4497098479/10000000000 : ℝ)|=(4497098479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s10_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089938351/5000000000 : ℝ)*x 0 + (1053133457/2000000000 : ℝ)*x 1 + (2696569119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089938351/5000000000 : ℝ)^2077 ≤ (662164062961/5000000000000 : ℝ)^1565 := by
    have hnat : (1089938351 : ℕ)^2077*5000000000000^1565 ≤ 662164062961^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089938351 5000000000 662164062961 5000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053133457/2000000000 : ℝ)^2077 ≤ (42689893819763/100000000000000 : ℝ)^1565 := by
    have hnat : (1053133457 : ℕ)^2077*100000000000000^1565 ≤ 42689893819763^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053133457 2000000000 42689893819763 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696569119/5000000000 : ℝ)^2077 ≤ (8813364980363/20000000000000 : ℝ)^1565 := by
    have hnat : (2696569119 : ℕ)^2077*20000000000000^1565 ≤ 8813364980363^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696569119 5000000000 8813364980363 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089938351/5000000000 : ℝ), (1053133457/2000000000 : ℝ), (2696569119/5000000000 : ℝ)] ![(662164062961/5000000000000 : ℝ), (42689893819763/100000000000000 : ℝ), (8813364980363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089938351/5000000000 : ℝ)|^2077 ≤ (662164062961/5000000000000 : ℝ)^1565
        have hw : |(-1089938351/5000000000 : ℝ)|=(1089938351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053133457/2000000000 : ℝ)|^2077 ≤ (42689893819763/100000000000000 : ℝ)^1565
        have hw : |(1053133457/2000000000 : ℝ)|=(1053133457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696569119/5000000000 : ℝ)|^2077 ≤ (8813364980363/20000000000000 : ℝ)^1565
        have hw : |(2696569119/5000000000 : ℝ)|=(2696569119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s10_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (664055507/1250000000 : ℝ)*x 0 + (-2117069439/10000000000 : ℝ)*x 1 + (5393135789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664055507/1250000000 : ℝ)^2077 ≤ (4319392038669/10000000000000 : ℝ)^1565 := by
    have hnat : (664055507 : ℕ)^2077*10000000000000^1565 ≤ 4319392038669^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664055507 1250000000 4319392038669 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117069439/10000000000 : ℝ)^2077 ≤ (12739281248239/100000000000000 : ℝ)^1565 := by
    have hnat : (2117069439 : ℕ)^2077*100000000000000^1565 ≤ 12739281248239^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117069439 10000000000 12739281248239 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393135789/10000000000 : ℝ)^2077 ≤ (22033399172343/50000000000000 : ℝ)^1565 := by
    have hnat : (5393135789 : ℕ)^2077*50000000000000^1565 ≤ 22033399172343^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393135789 10000000000 22033399172343 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664055507/1250000000 : ℝ), (-2117069439/10000000000 : ℝ), (5393135789/10000000000 : ℝ)] ![(4319392038669/10000000000000 : ℝ), (12739281248239/100000000000000 : ℝ), (22033399172343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664055507/1250000000 : ℝ)|^2077 ≤ (4319392038669/10000000000000 : ℝ)^1565
        have hw : |(664055507/1250000000 : ℝ)|=(664055507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117069439/10000000000 : ℝ)|^2077 ≤ (12739281248239/100000000000000 : ℝ)^1565
        have hw : |(-2117069439/10000000000 : ℝ)|=(2117069439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393135789/10000000000 : ℝ)|^2077 ≤ (22033399172343/50000000000000 : ℝ)^1565
        have hw : |(5393135789/10000000000 : ℝ)|=(5393135789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s10_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328110593/2500000000 : ℝ)*x 0 + (1348284343/2500000000 : ℝ)*x 1 + (-1058534783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328110593/2500000000 : ℝ)^2077 ≤ (43193902215119/100000000000000 : ℝ)^1565 := by
    have hnat : (1328110593 : ℕ)^2077*100000000000000^1565 ≤ 43193902215119^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328110593 2500000000 43193902215119 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348284343/2500000000 : ℝ)^2077 ≤ (44066815510849/100000000000000 : ℝ)^1565 := by
    have hnat : (1348284343 : ℕ)^2077*100000000000000^1565 ≤ 44066815510849^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348284343 2500000000 44066815510849 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058534783/5000000000 : ℝ)^2077 ≤ (12739282262467/100000000000000 : ℝ)^1565 := by
    have hnat : (1058534783 : ℕ)^2077*100000000000000^1565 ≤ 12739282262467^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058534783 5000000000 12739282262467 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328110593/2500000000 : ℝ), (1348284343/2500000000 : ℝ), (-1058534783/5000000000 : ℝ)] ![(43193902215119/100000000000000 : ℝ), (44066815510849/100000000000000 : ℝ), (12739282262467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328110593/2500000000 : ℝ)|^2077 ≤ (43193902215119/100000000000000 : ℝ)^1565
        have hw : |(1328110593/2500000000 : ℝ)|=(1328110593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348284343/2500000000 : ℝ)|^2077 ≤ (44066815510849/100000000000000 : ℝ)^1565
        have hw : |(1348284343/2500000000 : ℝ)|=(1348284343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058534783/5000000000 : ℝ)|^2077 ≤ (12739282262467/100000000000000 : ℝ)^1565
        have hw : |(-1058534783/5000000000 : ℝ)|=(1058534783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s10_7 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-5673049/2000000000 : ℝ)*x 0 + (5929811821/10000000000 : ℝ)*x 1 + (5929799329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5673049/2000000000 : ℝ)^2077 ≤ (5204259999/12500000000000 : ℝ)^1565 := by
    have hnat : (5673049 : ℕ)^2077*12500000000000^1565 ≤ 5204259999^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673049 2000000000 5204259999 12500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5929811821/10000000000 : ℝ)^2077 ≤ (4997925282171/10000000000000 : ℝ)^1565 := by
    have hnat : (5929811821 : ℕ)^2077*10000000000000^1565 ≤ 4997925282171^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5929811821 10000000000 4997925282171 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5929799329/10000000000 : ℝ)^2077 ≤ (49979113087473/100000000000000 : ℝ)^1565 := by
    have hnat : (5929799329 : ℕ)^2077*100000000000000^1565 ≤ 49979113087473^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5929799329 10000000000 49979113087473 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5673049/2000000000 : ℝ), (5929811821/10000000000 : ℝ), (5929799329/10000000000 : ℝ)] ![(5204259999/12500000000000 : ℝ), (4997925282171/10000000000000 : ℝ), (49979113087473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5673049/2000000000 : ℝ)|^2077 ≤ (5204259999/12500000000000 : ℝ)^1565
        have hw : |(-5673049/2000000000 : ℝ)|=(5673049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5929811821/10000000000 : ℝ)|^2077 ≤ (4997925282171/10000000000000 : ℝ)^1565
        have hw : |(5929811821/10000000000 : ℝ)|=(5929811821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5929799329/10000000000 : ℝ)|^2077 ≤ (49979113087473/100000000000000 : ℝ)^1565
        have hw : |(5929799329/10000000000 : ℝ)|=(5929799329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11319/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (877/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5659/50000 : ℝ) ^ (8307/2048 : ℝ) ≤ (14519301001064511/100000000000000000000 : ℝ) := by
    have hpowers : (5659/50000 : ℝ)^8307 ≤ (14519301001064511/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5659 : ℕ)^8307*100000000000000000000^2048 ≤ 14519301001064511^2048*50000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5659 50000 14519301001064511 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5659/50000 : ℝ)) (X := (14519301001064511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (877/6250 : ℝ) ^ (8307/2048 : ℝ) ≤ (694411756664019/2000000000000000000 : ℝ) := by
    have hpowers : (877/6250 : ℝ)^8307 ≤ (694411756664019/2000000000000000000 : ℝ)^2048 := by
      have hnat : (877 : ℕ)^8307*2000000000000000000^2048 ≤ 694411756664019^2048*6250^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        877 6250 694411756664019 2000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (877/6250 : ℝ)) (X := (694411756664019/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014519301001064511/50000000000000000000 : ℝ) ≤ (2500178959167069/2500000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50014519301001064511/50000000000000000000 : ℝ)^2048 ≤ (2500178959167069/2500000000000000 : ℝ)^8307 := by
      have hnat : (50014519301001064511 : ℕ)^2048*2500000000000000^8307 ≤ 2500178959167069^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014519301001064511 50000000000000000000 2500178959167069 2500000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500178959167069/2500000000000000 : ℝ)) (X := (50014519301001064511/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049239888834265461/100000000000000000000 : ℝ) ≤ (2000242746096343/2000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (100049239888834265461/100000000000000000000 : ℝ)^2048 ≤ (2000242746096343/2000000000000000 : ℝ)^8307 := by
      have hnat : (100049239888834265461 : ℕ)^2048*2000000000000000^8307 ≤ 2000242746096343^8307*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049239888834265461 100000000000000000000 2000242746096343 2000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000242746096343/2000000000000000 : ℝ)) (X := (100049239888834265461/100000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000694411756664019/1000000000000000000 : ℝ) ≤ (5000855812147577/5000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (1000694411756664019/1000000000000000000 : ℝ)^2048 ≤ (5000855812147577/5000000000000000 : ℝ)^8307 := by
      have hnat : (1000694411756664019 : ℕ)^2048*5000000000000000^8307 ≤ 5000855812147577^8307*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000694411756664019 1000000000000000000 5000855812147577 5000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000855812147577/5000000000000000 : ℝ)) (X := (1000694411756664019/1000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14519301001064511/100000000000000000000 : ℝ) ≤ ((1356533622817834793/1357000000000000000 : ℝ)+2*(497893813439/271400000000000 : ℝ)*(5659/50000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (1356533622817834793/1357000000000000000 : ℝ)+2*(497893813439/271400000000000 : ℝ)*(5659/50000 : ℝ)=(2500178959167069/2500000000000000 : ℝ) by norm_num, show 1+2*(14519301001064511/100000000000000000000 : ℝ)=(50014519301001064511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(694411756664019/2000000000000000000 : ℝ)+(14519301001064511/100000000000000000000 : ℝ) ≤ ((1356533622817834793/1357000000000000000 : ℝ)+(497893813439/271400000000000 : ℝ)*((877/6250 : ℝ)+(5659/50000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (1356533622817834793/1357000000000000000 : ℝ)+(497893813439/271400000000000 : ℝ)*((877/6250 : ℝ)+(5659/50000 : ℝ))=(2000242746096343/2000000000000000 : ℝ) by norm_num, show 1+(694411756664019/2000000000000000000 : ℝ)+(14519301001064511/100000000000000000000 : ℝ)=(100049239888834265461/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(694411756664019/2000000000000000000 : ℝ) ≤ ((1356533622817834793/1357000000000000000 : ℝ)+2*(497893813439/271400000000000 : ℝ)*(877/6250 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (1356533622817834793/1357000000000000000 : ℝ)+2*(497893813439/271400000000000 : ℝ)*(877/6250 : ℝ)=(5000855812147577/5000000000000000 : ℝ) by norm_num, show 1+2*(694411756664019/2000000000000000000 : ℝ)=(1000694411756664019/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1356533622817834793/1357000000000000000 : ℝ)*(X 1 0+X 2 0)+(497893813439/271400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (1356533622817834793/1357000000000000000 : ℝ)) (alpha := (497893813439/271400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1356533622817834793/1357000000000000000 : ℝ)*(X 0 1+X 2 1)+(497893813439/271400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (1356533622817834793/1357000000000000000 : ℝ)) (alpha := (497893813439/271400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1356533622817834793/1357000000000000000 : ℝ)*(X 0 2+X 1 2)+(497893813439/271400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (1356533622817834793/1357000000000000000 : ℝ)) (alpha := (497893813439/271400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1089936229/5000000000 : ℝ)*X 0 0+(5393459437/10000000000 : ℝ)*X 0 1+(5265346737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s10_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66810443/125000000 : ℝ)*X 1 0+(-561214703/2500000000 : ℝ)*X 1 1+(2632673521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s10_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334052221/625000000 : ℝ)*X 2 0+(5265346919/10000000000 : ℝ)*X 2 1+(-1122429423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s10_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873698771/2000000000 : ℝ)*X 0 0+(4243572147/10000000000 : ℝ)*X 0 1+(4497098479/10000000000 : ℝ)*X 0 2+(873698771/2000000000 : ℝ)*X 1 0+(4243572147/10000000000 : ℝ)*X 1 1+(4497098479/10000000000 : ℝ)*X 1 2+(873698771/2000000000 : ℝ)*X 2 0+(4243572147/10000000000 : ℝ)*X 2 1+(4497098479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s10_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1089938351/5000000000 : ℝ)*X 0 0+(1053133457/2000000000 : ℝ)*X 0 1+(2696569119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s10_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664055507/1250000000 : ℝ)*X 1 0+(-2117069439/10000000000 : ℝ)*X 1 1+(5393135789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s10_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328110593/2500000000 : ℝ)*X 2 0+(1348284343/2500000000 : ℝ)*X 2 1+(-1058534783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s10_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-5673049/2000000000 : ℝ)*X 0 0+(5929811821/10000000000 : ℝ)*X 0 1+(5929799329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s10_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33106180905001459154091/13570000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45238317/10000000000000 : ℝ)*(lower2) + (11305039/3125000000000 : ℝ)*(lower4) + (266216039/100000000000000 : ℝ)*(lower5) + (5875007658110687/100000000000000 : ℝ)*(major0) + (5875007658110687/100000000000000 : ℝ)*(major1) + (5875007658110687/100000000000000 : ℝ)*(major2) + (1561128973756009/20000000000000 : ℝ)*(sp0) + (1561128628328001/20000000000000 : ℝ)*(sp1) + (1951411996343067/25000000000000 : ℝ)*(sp2) + (394435644740253/10000000000000 : ℝ)*(sp3) + (9071343467/100000000000000 : ℝ)*(sp4) + (3129171369/20000000000000 : ℝ)*(sp5) + (10802124581/100000000000000 : ℝ)*(sp6) + (605921667/12500000000000 : ℝ)*(sp7) + (394435644740253/10000000000000 : ℝ)*(f.failure) + (7805658787496849/100000000000000 : ℝ)*(f.sum) + (25550463654573/13570000000000000000000000000 : ℝ)*base65 + (996175008108497791/135700000000000000000000000000000 : ℝ)*base67 + (638880968195802209/135700000000000000000000000000000 : ℝ)*base70 + (1164460087932302209/135700000000000000000000000000000 : ℝ)*base72 + (68153894312557/13570000000000000000000000000 : ℝ)*base74 + (1649818157837802209/135700000000000000000000000000000 : ℝ)*base76 + (1246993877085697791/135700000000000000000000000000000 : ℝ)*base77 + (1132300182262897791/135700000000000000000000000000000 : ℝ)*base79 + (10085712915873/13570000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (2096287/1000000000000000000000 : ℝ)*base89 + (2096287/1000000000000000000000 : ℝ)*base91 + (2096287/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1115_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (877/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1115_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1115_box_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052087157/10000000000 : ℝ)*x 0 + (2688343859/5000000000 : ℝ)*x 1 + (537668771/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052087157/10000000000 : ℝ)^2077 ≤ (763934584473/6250000000000 : ℝ)^1565 := by
    have hnat : (2052087157 : ℕ)^2077*6250000000000^1565 ≤ 763934584473^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052087157 10000000000 763934584473 6250000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688343859/5000000000 : ℝ)^2077 ≤ (43888523361257/100000000000000 : ℝ)^1565 := by
    have hnat : (2688343859 : ℕ)^2077*100000000000000^1565 ≤ 43888523361257^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688343859 5000000000 43888523361257 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537668771/1000000000 : ℝ)^2077 ≤ (43888523274591/100000000000000 : ℝ)^1565 := by
    have hnat : (537668771 : ℕ)^2077*100000000000000^1565 ≤ 43888523274591^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537668771 1000000000 43888523274591 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052087157/10000000000 : ℝ), (2688343859/5000000000 : ℝ), (537668771/1000000000 : ℝ)] ![(763934584473/6250000000000 : ℝ), (43888523361257/100000000000000 : ℝ), (43888523274591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052087157/10000000000 : ℝ)|^2077 ≤ (763934584473/6250000000000 : ℝ)^1565
        have hw : |(-2052087157/10000000000 : ℝ)|=(2052087157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688343859/5000000000 : ℝ)|^2077 ≤ (43888523361257/100000000000000 : ℝ)^1565
        have hw : |(2688343859/5000000000 : ℝ)|=(2688343859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537668771/1000000000 : ℝ)|^2077 ≤ (43888523274591/100000000000000 : ℝ)^1565
        have hw : |(537668771/1000000000 : ℝ)|=(537668771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5295727323/10000000000 : ℝ)*x 0 + (-216181493/1000000000 : ℝ)*x 1 + (1344171891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295727323/10000000000 : ℝ)^2077 ≤ (43013627723977/100000000000000 : ℝ)^1565 := by
    have hnat : (5295727323 : ℕ)^2077*100000000000000^1565 ≤ 43013627723977^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295727323 10000000000 43013627723977 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216181493/1000000000 : ℝ)^2077 ≤ (523914022827/4000000000000 : ℝ)^1565 := by
    have hnat : (216181493 : ℕ)^2077*4000000000000^1565 ≤ 523914022827^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216181493 1000000000 523914022827 4000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344171891/2500000000 : ℝ)^2077 ≤ (43888521692939/100000000000000 : ℝ)^1565 := by
    have hnat : (1344171891 : ℕ)^2077*100000000000000^1565 ≤ 43888521692939^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344171891 2500000000 43888521692939 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295727323/10000000000 : ℝ), (-216181493/1000000000 : ℝ), (1344171891/2500000000 : ℝ)] ![(43013627723977/100000000000000 : ℝ), (523914022827/4000000000000 : ℝ), (43888521692939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295727323/10000000000 : ℝ)|^2077 ≤ (43013627723977/100000000000000 : ℝ)^1565
        have hw : |(5295727323/10000000000 : ℝ)|=(5295727323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216181493/1000000000 : ℝ)|^2077 ≤ (523914022827/4000000000000 : ℝ)^1565
        have hw : |(-216181493/1000000000 : ℝ)|=(216181493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344171891/2500000000 : ℝ)|^2077 ≤ (43888521692939/100000000000000 : ℝ)^1565
        have hw : |(1344171891/2500000000 : ℝ)|=(1344171891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647863599/5000000000 : ℝ)*x 0 + (2688343819/5000000000 : ℝ)*x 1 + (-2161814997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647863599/5000000000 : ℝ)^2077 ≤ (43013626376527/100000000000000 : ℝ)^1565 := by
    have hnat : (2647863599 : ℕ)^2077*100000000000000^1565 ≤ 43013626376527^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647863599 5000000000 43013626376527 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688343819/5000000000 : ℝ)^2077 ≤ (21944261247299/50000000000000 : ℝ)^1565 := by
    have hnat : (2688343819 : ℕ)^2077*50000000000000^1565 ≤ 21944261247299^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688343819 5000000000 21944261247299 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161814997/10000000000 : ℝ)^2077 ≤ (6548925554707/50000000000000 : ℝ)^1565 := by
    have hnat : (2161814997 : ℕ)^2077*50000000000000^1565 ≤ 6548925554707^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161814997 10000000000 6548925554707 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647863599/5000000000 : ℝ), (2688343819/5000000000 : ℝ), (-2161814997/10000000000 : ℝ)] ![(43013626376527/100000000000000 : ℝ), (21944261247299/50000000000000 : ℝ), (6548925554707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647863599/5000000000 : ℝ)|^2077 ≤ (43013626376527/100000000000000 : ℝ)^1565
        have hw : |(2647863599/5000000000 : ℝ)|=(2647863599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688343819/5000000000 : ℝ)|^2077 ≤ (21944261247299/50000000000000 : ℝ)^1565
        have hw : |(2688343819/5000000000 : ℝ)|=(2688343819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2161814997/10000000000 : ℝ)|^2077 ≤ (6548925554707/50000000000000 : ℝ)^1565
        have hw : |(-2161814997/10000000000 : ℝ)|=(2161814997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4476321037/10000000000 : ℝ)*x 0 + (4316706201/10000000000 : ℝ)*x 1 + (4316706287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476321037/10000000000 : ℝ)^2077 ≤ (34412626347617/100000000000000 : ℝ)^1565 := by
    have hnat : (4476321037 : ℕ)^2077*100000000000000^1565 ≤ 34412626347617^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476321037 10000000000 34412626347617 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316706201/10000000000 : ℝ)^2077 ≤ (32793686386351/100000000000000 : ℝ)^1565 := by
    have hnat : (4316706201 : ℕ)^2077*100000000000000^1565 ≤ 32793686386351^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316706201 10000000000 32793686386351 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316706287/10000000000 : ℝ)^2077 ≤ (3279368725343/10000000000000 : ℝ)^1565 := by
    have hnat : (4316706287 : ℕ)^2077*10000000000000^1565 ≤ 3279368725343^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316706287 10000000000 3279368725343 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476321037/10000000000 : ℝ), (4316706201/10000000000 : ℝ), (4316706287/10000000000 : ℝ)] ![(34412626347617/100000000000000 : ℝ), (32793686386351/100000000000000 : ℝ), (3279368725343/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476321037/10000000000 : ℝ)|^2077 ≤ (34412626347617/100000000000000 : ℝ)^1565
        have hw : |(4476321037/10000000000 : ℝ)|=(4476321037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316706201/10000000000 : ℝ)|^2077 ≤ (32793686386351/100000000000000 : ℝ)^1565
        have hw : |(4316706201/10000000000 : ℝ)|=(4316706201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316706287/10000000000 : ℝ)|^2077 ≤ (3279368725343/10000000000000 : ℝ)^1565
        have hw : |(4316706287/10000000000 : ℝ)|=(4316706287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2309034783/10000000000 : ℝ)*x 0 + (264039531/500000000 : ℝ)*x 1 + (1056158127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2309034783/10000000000 : ℝ)^2077 ≤ (3573654761547/25000000000000 : ℝ)^1565 := by
    have hnat : (2309034783 : ℕ)^2077*25000000000000^1565 ≤ 3573654761547^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309034783 10000000000 3573654761547 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264039531/500000000 : ℝ)^2077 ≤ (21426345193467/50000000000000 : ℝ)^1565 := by
    have hnat : (264039531 : ℕ)^2077*50000000000000^1565 ≤ 21426345193467^1565*500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264039531 500000000 21426345193467 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056158127/2000000000 : ℝ)^2077 ≤ (21426345274239/50000000000000 : ℝ)^1565 := by
    have hnat : (1056158127 : ℕ)^2077*50000000000000^1565 ≤ 21426345274239^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056158127 2000000000 21426345274239 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2309034783/10000000000 : ℝ), (264039531/500000000 : ℝ), (1056158127/2000000000 : ℝ)] ![(3573654761547/25000000000000 : ℝ), (21426345193467/50000000000000 : ℝ), (21426345274239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2309034783/10000000000 : ℝ)|^2077 ≤ (3573654761547/25000000000000 : ℝ)^1565
        have hw : |(-2309034783/10000000000 : ℝ)|=(2309034783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264039531/500000000 : ℝ)|^2077 ≤ (21426345193467/50000000000000 : ℝ)^1565
        have hw : |(264039531/500000000 : ℝ)|=(264039531/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056158127/2000000000 : ℝ)|^2077 ≤ (21426345274239/50000000000000 : ℝ)^1565
        have hw : |(1056158127/2000000000 : ℝ)|=(1056158127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5363519739/10000000000 : ℝ)*x 0 + (-2199456553/10000000000 : ℝ)*x 1 + (5280790599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363519739/10000000000 : ℝ)^2077 ≤ (43745928682391/100000000000000 : ℝ)^1565 := by
    have hnat : (5363519739 : ℕ)^2077*100000000000000^1565 ≤ 43745928682391^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363519739 10000000000 43745928682391 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199456553/10000000000 : ℝ)^2077 ≤ (13401381146757/100000000000000 : ℝ)^1565 := by
    have hnat : (2199456553 : ℕ)^2077*100000000000000^1565 ≤ 13401381146757^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199456553 10000000000 13401381146757 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280790599/10000000000 : ℝ)^2077 ≤ (42852690160771/100000000000000 : ℝ)^1565 := by
    have hnat : (5280790599 : ℕ)^2077*100000000000000^1565 ≤ 42852690160771^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280790599 10000000000 42852690160771 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363519739/10000000000 : ℝ), (-2199456553/10000000000 : ℝ), (5280790599/10000000000 : ℝ)] ![(43745928682391/100000000000000 : ℝ), (13401381146757/100000000000000 : ℝ), (42852690160771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363519739/10000000000 : ℝ)|^2077 ≤ (43745928682391/100000000000000 : ℝ)^1565
        have hw : |(5363519739/10000000000 : ℝ)|=(5363519739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2199456553/10000000000 : ℝ)|^2077 ≤ (13401381146757/100000000000000 : ℝ)^1565
        have hw : |(-2199456553/10000000000 : ℝ)|=(2199456553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280790599/10000000000 : ℝ)|^2077 ≤ (42852690160771/100000000000000 : ℝ)^1565
        have hw : |(5280790599/10000000000 : ℝ)|=(5280790599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268175981/500000000 : ℝ)*x 0 + (660098829/1250000000 : ℝ)*x 1 + (-549864167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268175981/500000000 : ℝ)^2077 ≤ (43745927394269/100000000000000 : ℝ)^1565 := by
    have hnat : (268175981 : ℕ)^2077*100000000000000^1565 ≤ 43745927394269^1565*500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268175981 500000000 43745927394269 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660098829/1250000000 : ℝ)^2077 ≤ (42852690516169/100000000000000 : ℝ)^1565 := by
    have hnat : (660098829 : ℕ)^2077*100000000000000^1565 ≤ 42852690516169^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660098829 1250000000 42852690516169 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549864167/2500000000 : ℝ)^2077 ≤ (2680276415339/20000000000000 : ℝ)^1565 := by
    have hnat : (549864167 : ℕ)^2077*20000000000000^1565 ≤ 2680276415339^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549864167 2500000000 2680276415339 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268175981/500000000 : ℝ), (660098829/1250000000 : ℝ), (-549864167/2500000000 : ℝ)] ![(43745927394269/100000000000000 : ℝ), (42852690516169/100000000000000 : ℝ), (2680276415339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268175981/500000000 : ℝ)|^2077 ≤ (43745927394269/100000000000000 : ℝ)^1565
        have hw : |(268175981/500000000 : ℝ)|=(268175981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660098829/1250000000 : ℝ)|^2077 ≤ (42852690516169/100000000000000 : ℝ)^1565
        have hw : |(660098829/1250000000 : ℝ)|=(660098829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-549864167/2500000000 : ℝ)|^2077 ≤ (2680276415339/20000000000000 : ℝ)^1565
        have hw : |(-549864167/2500000000 : ℝ)|=(549864167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_7 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1065079011/2500000000 : ℝ)*x 0 + (884937549/2000000000 : ℝ)*x 1 + (2212343819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065079011/2500000000 : ℝ)^2077 ≤ (2014147625471/6250000000000 : ℝ)^1565 := by
    have hnat : (1065079011 : ℕ)^2077*6250000000000^1565 ≤ 2014147625471^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065079011 2500000000 2014147625471 6250000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884937549/2000000000 : ℝ)^2077 ≤ (33886819531073/100000000000000 : ℝ)^1565 := by
    have hnat : (884937549 : ℕ)^2077*100000000000000^1565 ≤ 33886819531073^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884937549 2000000000 33886819531073 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212343819/5000000000 : ℝ)^2077 ≤ (33886818443511/100000000000000 : ℝ)^1565 := by
    have hnat : (2212343819 : ℕ)^2077*100000000000000^1565 ≤ 33886818443511^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212343819 5000000000 33886818443511 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065079011/2500000000 : ℝ), (884937549/2000000000 : ℝ), (2212343819/5000000000 : ℝ)] ![(2014147625471/6250000000000 : ℝ), (33886819531073/100000000000000 : ℝ), (33886818443511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065079011/2500000000 : ℝ)|^2077 ≤ (2014147625471/6250000000000 : ℝ)^1565
        have hw : |(1065079011/2500000000 : ℝ)|=(1065079011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884937549/2000000000 : ℝ)|^2077 ≤ (33886819531073/100000000000000 : ℝ)^1565
        have hw : |(884937549/2000000000 : ℝ)|=(884937549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212343819/5000000000 : ℝ)|^2077 ≤ (33886818443511/100000000000000 : ℝ)^1565
        have hw : |(2212343819/5000000000 : ℝ)|=(2212343819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_8 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1127667581/5000000000 : ℝ)*x 0 + (521562343/1000000000 : ℝ)*x 1 + (538629299/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127667581/5000000000 : ℝ)^2077 ≤ (6927553164897/50000000000000 : ℝ)^1565 := by
    have hnat : (1127667581 : ℕ)^2077*50000000000000^1565 ≤ 6927553164897^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127667581 5000000000 6927553164897 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521562343/1000000000 : ℝ)^2077 ≤ (8430456739151/20000000000000 : ℝ)^1565 := by
    have hnat : (521562343 : ℕ)^2077*20000000000000^1565 ≤ 8430456739151^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521562343 1000000000 8430456739151 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538629299/1000000000 : ℝ)^2077 ≤ (1374769061283/3125000000000 : ℝ)^1565 := by
    have hnat : (538629299 : ℕ)^2077*3125000000000^1565 ≤ 1374769061283^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538629299 1000000000 1374769061283 3125000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1127667581/5000000000 : ℝ), (521562343/1000000000 : ℝ), (538629299/1000000000 : ℝ)] ![(6927553164897/50000000000000 : ℝ), (8430456739151/20000000000000 : ℝ), (1374769061283/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1127667581/5000000000 : ℝ)|^2077 ≤ (6927553164897/50000000000000 : ℝ)^1565
        have hw : |(-1127667581/5000000000 : ℝ)|=(1127667581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521562343/1000000000 : ℝ)|^2077 ≤ (8430456739151/20000000000000 : ℝ)^1565
        have hw : |(521562343/1000000000 : ℝ)|=(521562343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538629299/1000000000 : ℝ)|^2077 ≤ (1374769061283/3125000000000 : ℝ)^1565
        have hw : |(538629299/1000000000 : ℝ)|=(538629299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_9 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288933697/10000000000 : ℝ)*x 0 + (-215797389/1000000000 : ℝ)*x 1 + (2693146739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288933697/10000000000 : ℝ)^2077 ≤ (42940410530937/100000000000000 : ℝ)^1565 := by
    have hnat : (5288933697 : ℕ)^2077*100000000000000^1565 ≤ 42940410530937^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288933697 10000000000 42940410530937 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215797389/1000000000 : ℝ)^2077 ≤ (204171471913/1562500000000 : ℝ)^1565 := by
    have hnat : (215797389 : ℕ)^2077*1562500000000^1565 ≤ 204171471913^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215797389 1000000000 204171471913 1562500000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693146739/5000000000 : ℝ)^2077 ≤ (8798523050153/20000000000000 : ℝ)^1565 := by
    have hnat : (2693146739 : ℕ)^2077*20000000000000^1565 ≤ 8798523050153^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693146739 5000000000 8798523050153 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288933697/10000000000 : ℝ), (-215797389/1000000000 : ℝ), (2693146739/5000000000 : ℝ)] ![(42940410530937/100000000000000 : ℝ), (204171471913/1562500000000 : ℝ), (8798523050153/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288933697/10000000000 : ℝ)|^2077 ≤ (42940410530937/100000000000000 : ℝ)^1565
        have hw : |(5288933697/10000000000 : ℝ)|=(5288933697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215797389/1000000000 : ℝ)|^2077 ≤ (204171471913/1562500000000 : ℝ)^1565
        have hw : |(-215797389/1000000000 : ℝ)|=(215797389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693146739/5000000000 : ℝ)|^2077 ≤ (8798523050153/20000000000000 : ℝ)^1565
        have hw : |(2693146739/5000000000 : ℝ)|=(2693146739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_10 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288933471/10000000000 : ℝ)*x 0 + (538629253/1000000000 : ℝ)*x 1 + (-2157975471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288933471/10000000000 : ℝ)^2077 ≤ (4294040809577/10000000000000 : ℝ)^1565 := by
    have hnat : (5288933471 : ℕ)^2077*10000000000000^1565 ≤ 4294040809577^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288933471 10000000000 4294040809577 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538629253/1000000000 : ℝ)^2077 ≤ (5499075621857/12500000000000 : ℝ)^1565 := by
    have hnat : (538629253 : ℕ)^2077*12500000000000^1565 ≤ 5499075621857^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538629253 1000000000 5499075621857 12500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157975471/10000000000 : ℝ)^2077 ≤ (13066986907673/100000000000000 : ℝ)^1565 := by
    have hnat : (2157975471 : ℕ)^2077*100000000000000^1565 ≤ 13066986907673^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157975471 10000000000 13066986907673 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288933471/10000000000 : ℝ), (538629253/1000000000 : ℝ), (-2157975471/10000000000 : ℝ)] ![(4294040809577/10000000000000 : ℝ), (5499075621857/12500000000000 : ℝ), (13066986907673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288933471/10000000000 : ℝ)|^2077 ≤ (4294040809577/10000000000000 : ℝ)^1565
        have hw : |(5288933471/10000000000 : ℝ)|=(5288933471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538629253/1000000000 : ℝ)|^2077 ≤ (5499075621857/12500000000000 : ℝ)^1565
        have hw : |(538629253/1000000000 : ℝ)|=(538629253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2157975471/10000000000 : ℝ)|^2077 ≤ (13066986907673/100000000000000 : ℝ)^1565
        have hw : |(-2157975471/10000000000 : ℝ)|=(2157975471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_11 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2248841979/5000000000 : ℝ)*x 0 + (86117687/200000000 : ℝ)*x 1 + (4305884201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2248841979/5000000000 : ℝ)^2077 ≤ (3463075761693/10000000000000 : ℝ)^1565 := by
    have hnat : (2248841979 : ℕ)^2077*10000000000000^1565 ≤ 3463075761693^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248841979 5000000000 3463075761693 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86117687/200000000 : ℝ)^2077 ≤ (8171155483821/25000000000000 : ℝ)^1565 := by
    have hnat : (86117687 : ℕ)^2077*25000000000000^1565 ≤ 8171155483821^1565*200000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86117687 200000000 8171155483821 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4305884201/10000000000 : ℝ)^2077 ≤ (16342310217127/50000000000000 : ℝ)^1565 := by
    have hnat : (4305884201 : ℕ)^2077*50000000000000^1565 ≤ 16342310217127^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305884201 10000000000 16342310217127 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2248841979/5000000000 : ℝ), (86117687/200000000 : ℝ), (4305884201/10000000000 : ℝ)] ![(3463075761693/10000000000000 : ℝ), (8171155483821/25000000000000 : ℝ), (16342310217127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2248841979/5000000000 : ℝ)|^2077 ≤ (3463075761693/10000000000000 : ℝ)^1565
        have hw : |(2248841979/5000000000 : ℝ)|=(2248841979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86117687/200000000 : ℝ)|^2077 ≤ (8171155483821/25000000000000 : ℝ)^1565
        have hw : |(86117687/200000000 : ℝ)|=(86117687/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4305884201/10000000000 : ℝ)|^2077 ≤ (16342310217127/50000000000000 : ℝ)^1565
        have hw : |(4305884201/10000000000 : ℝ)|=(4305884201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_12 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053061719/5000000000 : ℝ)*x 0 + (5440557153/10000000000 : ℝ)*x 1 + (263638269/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053061719/5000000000 : ℝ)^2077 ≤ (12651939964601/100000000000000 : ℝ)^1565 := by
    have hnat : (1053061719 : ℕ)^2077*100000000000000^1565 ≤ 12651939964601^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053061719 5000000000 12651939964601 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440557153/10000000000 : ℝ)^2077 ≤ (4458177711197/10000000000000 : ℝ)^1565 := by
    have hnat : (5440557153 : ℕ)^2077*10000000000000^1565 ≤ 4458177711197^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440557153 10000000000 4458177711197 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263638269/500000000 : ℝ)^2077 ≤ (42766282911457/100000000000000 : ℝ)^1565 := by
    have hnat : (263638269 : ℕ)^2077*100000000000000^1565 ≤ 42766282911457^1565*500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263638269 500000000 42766282911457 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053061719/5000000000 : ℝ), (5440557153/10000000000 : ℝ), (263638269/500000000 : ℝ)] ![(12651939964601/100000000000000 : ℝ), (4458177711197/10000000000000 : ℝ), (42766282911457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053061719/5000000000 : ℝ)|^2077 ≤ (12651939964601/100000000000000 : ℝ)^1565
        have hw : |(-1053061719/5000000000 : ℝ)|=(1053061719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440557153/10000000000 : ℝ)|^2077 ≤ (4458177711197/10000000000000 : ℝ)^1565
        have hw : |(5440557153/10000000000 : ℝ)|=(5440557153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263638269/500000000 : ℝ)|^2077 ≤ (42766282911457/100000000000000 : ℝ)^1565
        have hw : |(263638269/500000000 : ℝ)|=(263638269/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_13 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1342297731/2500000000 : ℝ)*x 0 + (-2202548797/10000000000 : ℝ)*x 1 + (5272765163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342297731/2500000000 : ℝ)^2077 ≤ (21903663665939/50000000000000 : ℝ)^1565 := by
    have hnat : (1342297731 : ℕ)^2077*50000000000000^1565 ≤ 21903663665939^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342297731 2500000000 21903663665939 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202548797/10000000000 : ℝ)^2077 ≤ (6713196040557/50000000000000 : ℝ)^1565 := by
    have hnat : (2202548797 : ℕ)^2077*50000000000000^1565 ≤ 6713196040557^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202548797 10000000000 6713196040557 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272765163/10000000000 : ℝ)^2077 ≤ (42766280575607/100000000000000 : ℝ)^1565 := by
    have hnat : (5272765163 : ℕ)^2077*100000000000000^1565 ≤ 42766280575607^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272765163 10000000000 42766280575607 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342297731/2500000000 : ℝ), (-2202548797/10000000000 : ℝ), (5272765163/10000000000 : ℝ)] ![(21903663665939/50000000000000 : ℝ), (6713196040557/50000000000000 : ℝ), (42766280575607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342297731/2500000000 : ℝ)|^2077 ≤ (21903663665939/50000000000000 : ℝ)^1565
        have hw : |(1342297731/2500000000 : ℝ)|=(1342297731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2202548797/10000000000 : ℝ)|^2077 ≤ (6713196040557/50000000000000 : ℝ)^1565
        have hw : |(-2202548797/10000000000 : ℝ)|=(2202548797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272765163/10000000000 : ℝ)|^2077 ≤ (42766280575607/100000000000000 : ℝ)^1565
        have hw : |(5272765163/10000000000 : ℝ)|=(5272765163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_14 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369190771/10000000000 : ℝ)*x 0 + (1054553093/2000000000 : ℝ)*x 1 + (-2202548599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369190771/10000000000 : ℝ)^2077 ≤ (43807325675149/100000000000000 : ℝ)^1565 := by
    have hnat : (5369190771 : ℕ)^2077*100000000000000^1565 ≤ 43807325675149^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369190771 10000000000 43807325675149 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054553093/2000000000 : ℝ)^2077 ≤ (42766283826421/100000000000000 : ℝ)^1565 := by
    have hnat : (1054553093 : ℕ)^2077*100000000000000^1565 ≤ 42766283826421^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054553093 2000000000 42766283826421 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202548599/10000000000 : ℝ)^2077 ≤ (13426390479267/100000000000000 : ℝ)^1565 := by
    have hnat : (2202548599 : ℕ)^2077*100000000000000^1565 ≤ 13426390479267^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202548599 10000000000 13426390479267 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369190771/10000000000 : ℝ), (1054553093/2000000000 : ℝ), (-2202548599/10000000000 : ℝ)] ![(43807325675149/100000000000000 : ℝ), (42766283826421/100000000000000 : ℝ), (13426390479267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369190771/10000000000 : ℝ)|^2077 ≤ (43807325675149/100000000000000 : ℝ)^1565
        have hw : |(5369190771/10000000000 : ℝ)|=(5369190771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054553093/2000000000 : ℝ)|^2077 ≤ (42766283826421/100000000000000 : ℝ)^1565
        have hw : |(1054553093/2000000000 : ℝ)|=(1054553093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202548599/10000000000 : ℝ)|^2077 ≤ (13426390479267/100000000000000 : ℝ)^1565
        have hw : |(-2202548599/10000000000 : ℝ)|=(2202548599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_box_15 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2121004167/5000000000 : ℝ)*x 0 + (4433719851/10000000000 : ℝ)*x 1 + (1108429787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121004167/5000000000 : ℝ)^2077 ≤ (6408539946657/20000000000000 : ℝ)^1565 := by
    have hnat : (2121004167 : ℕ)^2077*20000000000000^1565 ≤ 6408539946657^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121004167 5000000000 6408539946657 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433719851/10000000000 : ℝ)^2077 ≤ (33978653697513/100000000000000 : ℝ)^1565 := by
    have hnat : (4433719851 : ℕ)^2077*100000000000000^1565 ≤ 33978653697513^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433719851 10000000000 33978653697513 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108429787/2500000000 : ℝ)^2077 ≤ (33978646547359/100000000000000 : ℝ)^1565 := by
    have hnat : (1108429787 : ℕ)^2077*100000000000000^1565 ≤ 33978646547359^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108429787 2500000000 33978646547359 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121004167/5000000000 : ℝ), (4433719851/10000000000 : ℝ), (1108429787/2500000000 : ℝ)] ![(6408539946657/20000000000000 : ℝ), (33978653697513/100000000000000 : ℝ), (33978646547359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121004167/5000000000 : ℝ)|^2077 ≤ (6408539946657/20000000000000 : ℝ)^1565
        have hw : |(2121004167/5000000000 : ℝ)|=(2121004167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4433719851/10000000000 : ℝ)|^2077 ≤ (33978653697513/100000000000000 : ℝ)^1565
        have hw : |(4433719851/10000000000 : ℝ)|=(4433719851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108429787/2500000000 : ℝ)|^2077 ≤ (33978646547359/100000000000000 : ℝ)^1565
        have hw : |(1108429787/2500000000 : ℝ)|=(1108429787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15557/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29639/50000 : ℝ) ∧ (3189/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10383/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11319/100000 : ℝ) ^ (8307/2048 : ℝ) ≤ (2904901028071433/20000000000000000000 : ℝ) := by
    have hpowers : (11319/100000 : ℝ)^8307 ≤ (2904901028071433/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11319 : ℕ)^8307*20000000000000000000^2048 ≤ 2904901028071433^2048*100000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11319 100000 2904901028071433 20000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11319/100000 : ℝ)) (X := (2904901028071433/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (877/6250 : ℝ) ^ (8307/2048 : ℝ) ≤ (694411756664019/2000000000000000000 : ℝ) := by
    have hpowers : (877/6250 : ℝ)^8307 ≤ (694411756664019/2000000000000000000 : ℝ)^2048 := by
      have hnat : (877 : ℕ)^8307*2000000000000000000^2048 ≤ 694411756664019^2048*6250^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        877 6250 694411756664019 2000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (877/6250 : ℝ)) (X := (694411756664019/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002904901028071433/10000000000000000000 : ℝ) ≤ (5000358046608431/5000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (10002904901028071433/10000000000000000000 : ℝ)^2048 ≤ (5000358046608431/5000000000000000 : ℝ)^8307 := by
      have hnat : (10002904901028071433 : ℕ)^2048*5000000000000000^8307 ≤ 5000358046608431^8307*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002904901028071433 10000000000000000000 5000358046608431 5000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000358046608431/5000000000000000 : ℝ)) (X := (10002904901028071433/10000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009849018594711623/20000000000000000000 : ℝ) ≤ (2000242771747299/2000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (20009849018594711623/20000000000000000000 : ℝ)^2048 ≤ (2000242771747299/2000000000000000 : ℝ)^8307 := by
      have hnat : (20009849018594711623 : ℕ)^2048*2000000000000000^8307 ≤ 2000242771747299^8307*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009849018594711623 20000000000000000000 2000242771747299 2000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000242771747299/2000000000000000 : ℝ)) (X := (20009849018594711623/20000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000694411756664019/1000000000000000000 : ℝ) ≤ (78138372064501/78125000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (1000694411756664019/1000000000000000000 : ℝ)^2048 ≤ (78138372064501/78125000000000 : ℝ)^8307 := by
      have hnat : (1000694411756664019 : ℕ)^2048*78125000000000^8307 ≤ 78138372064501^8307*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000694411756664019 1000000000000000000 78138372064501 78125000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78138372064501/78125000000000 : ℝ)) (X := (1000694411756664019/1000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2904901028071433/20000000000000000000 : ℝ) ≤ ((847521073283246711/847812500000000000 : ℝ)+2*(497765519633/271300000000000 : ℝ)*(11319/100000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (847521073283246711/847812500000000000 : ℝ)+2*(497765519633/271300000000000 : ℝ)*(11319/100000 : ℝ)=(5000358046608431/5000000000000000 : ℝ) by norm_num, show 1+2*(2904901028071433/20000000000000000000 : ℝ)=(10002904901028071433/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(694411756664019/2000000000000000000 : ℝ)+(2904901028071433/20000000000000000000 : ℝ) ≤ ((847521073283246711/847812500000000000 : ℝ)+(497765519633/271300000000000 : ℝ)*((877/6250 : ℝ)+(11319/100000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (847521073283246711/847812500000000000 : ℝ)+(497765519633/271300000000000 : ℝ)*((877/6250 : ℝ)+(11319/100000 : ℝ))=(2000242771747299/2000000000000000 : ℝ) by norm_num, show 1+(694411756664019/2000000000000000000 : ℝ)+(2904901028071433/20000000000000000000 : ℝ)=(20009849018594711623/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(694411756664019/2000000000000000000 : ℝ) ≤ ((847521073283246711/847812500000000000 : ℝ)+2*(497765519633/271300000000000 : ℝ)*(877/6250 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (847521073283246711/847812500000000000 : ℝ)+2*(497765519633/271300000000000 : ℝ)*(877/6250 : ℝ)=(78138372064501/78125000000000 : ℝ) by norm_num, show 1+2*(694411756664019/2000000000000000000 : ℝ)=(1000694411756664019/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (847521073283246711/847812500000000000 : ℝ)*(X 1 0+X 2 0)+(497765519633/271300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (847521073283246711/847812500000000000 : ℝ)) (alpha := (497765519633/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (847521073283246711/847812500000000000 : ℝ)*(X 0 1+X 2 1)+(497765519633/271300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (847521073283246711/847812500000000000 : ℝ)) (alpha := (497765519633/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (847521073283246711/847812500000000000 : ℝ)*(X 0 2+X 1 2)+(497765519633/271300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (847521073283246711/847812500000000000 : ℝ)) (alpha := (497765519633/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2052087157/10000000000 : ℝ)*X 0 0+(2688343859/5000000000 : ℝ)*X 0 1+(537668771/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295727323/10000000000 : ℝ)*X 1 0+(-216181493/1000000000 : ℝ)*X 1 1+(1344171891/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647863599/5000000000 : ℝ)*X 2 0+(2688343819/5000000000 : ℝ)*X 2 1+(-2161814997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4476321037/10000000000 : ℝ)*X 0 0+(4316706201/10000000000 : ℝ)*X 0 1+(4316706287/10000000000 : ℝ)*X 0 2+(4476321037/10000000000 : ℝ)*X 1 0+(4316706201/10000000000 : ℝ)*X 1 1+(4316706287/10000000000 : ℝ)*X 1 2+(4476321037/10000000000 : ℝ)*X 2 0+(4316706201/10000000000 : ℝ)*X 2 1+(4316706287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2309034783/10000000000 : ℝ)*X 0 0+(264039531/500000000 : ℝ)*X 0 1+(1056158127/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363519739/10000000000 : ℝ)*X 1 0+(-2199456553/10000000000 : ℝ)*X 1 1+(5280790599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268175981/500000000 : ℝ)*X 2 0+(660098829/1250000000 : ℝ)*X 2 1+(-549864167/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065079011/2500000000 : ℝ)*X 0 0+(884937549/2000000000 : ℝ)*X 0 1+(2212343819/5000000000 : ℝ)*X 0 2+(1065079011/2500000000 : ℝ)*X 1 0+(884937549/2000000000 : ℝ)*X 1 1+(2212343819/5000000000 : ℝ)*X 1 2+(1065079011/2500000000 : ℝ)*X 2 0+(884937549/2000000000 : ℝ)*X 2 1+(2212343819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1127667581/5000000000 : ℝ)*X 0 0+(521562343/1000000000 : ℝ)*X 0 1+(538629299/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288933697/10000000000 : ℝ)*X 1 0+(-215797389/1000000000 : ℝ)*X 1 1+(2693146739/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288933471/10000000000 : ℝ)*X 2 0+(538629253/1000000000 : ℝ)*X 2 1+(-2157975471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2248841979/5000000000 : ℝ)*X 0 0+(86117687/200000000 : ℝ)*X 0 1+(4305884201/10000000000 : ℝ)*X 0 2+(2248841979/5000000000 : ℝ)*X 1 0+(86117687/200000000 : ℝ)*X 1 1+(4305884201/10000000000 : ℝ)*X 1 2+(2248841979/5000000000 : ℝ)*X 2 0+(86117687/200000000 : ℝ)*X 2 1+(4305884201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1053061719/5000000000 : ℝ)*X 0 0+(5440557153/10000000000 : ℝ)*X 0 1+(263638269/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1342297731/2500000000 : ℝ)*X 1 0+(-2202548797/10000000000 : ℝ)*X 1 1+(5272765163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369190771/10000000000 : ℝ)*X 2 0+(1054553093/2000000000 : ℝ)*X 2 1+(-2202548599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2121004167/5000000000 : ℝ)*X 0 0+(4433719851/10000000000 : ℝ)*X 0 1+(1108429787/2500000000 : ℝ)*X 0 2+(2121004167/5000000000 : ℝ)*X 1 0+(4433719851/10000000000 : ℝ)*X 1 1+(1108429787/2500000000 : ℝ)*X 1 2+(2121004167/5000000000 : ℝ)*X 2 0+(4433719851/10000000000 : ℝ)*X 2 1+(1108429787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15557/25000 : ℝ) ≤ (-13188906974058997509759396028197/21195312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2294479/12500000000000 : ℝ)*(lower0) + (47698661/100000000000000 : ℝ)*(upper1) + (42070301/50000000000000 : ℝ)*(lower4) + (9594069/100000000000000 : ℝ)*(lower5) + (3898228253417607/100000000000000 : ℝ)*(major0) + (3898228253417607/100000000000000 : ℝ)*(major1) + (3898228253417607/100000000000000 : ℝ)*(major2) + (52592871/20000000000000 : ℝ)*(sp2) + (71468083/50000000000000 : ℝ)*(sp3) + (2600004996664207/50000000000000 : ℝ)*(sp4) + (2599986942426877/50000000000000 : ℝ)*(sp5) + (5200009730364059/100000000000000 : ℝ)*(sp6) + (654297057972179/25000000000000 : ℝ)*(sp7) + (1805423733/5000000000000 : ℝ)*(sp13) + (1308594187412441/50000000000000 : ℝ)*(f.failure) + (2600004996664207/50000000000000 : ℝ)*(f.sum) + (22765904477771/13565000000000000000000000000 : ℝ)*base65 + (131375287014225003/5298828125000000000000000000000 : ℝ)*base68 + (217856356105040637/21195312500000000000000000000000 : ℝ)*base70 + (56075076871709363/21195312500000000000000000000000 : ℝ)*base71 + (428885617568029/13565000000000000000000000000 : ℝ)*base74 + (171199651703228137/21195312500000000000000000000000 : ℝ)*base76 + (47509440156771863/21195312500000000000000000000000 : ℝ)*base77 + (191657216587165637/21195312500000000000000000000000 : ℝ)*base80 + (19387433545991/3391250000000000000000000000 : ℝ)*base82 + (46453939/5000000000000000000000 : ℝ)*base89 + (46453939/5000000000000000000000 : ℝ)*base91 + (46453939/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29639/50000 : ℝ) ≤ (6282327513437358156842839335081/10597656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1219977/50000000000000 : ℝ)*(lower1) + (1638007/5000000000000 : ℝ)*(upper2) + (2664231/10000000000000 : ℝ)*(lower4) + (3636763/20000000000000 : ℝ)*(lower5) + (3961943512038201/100000000000000 : ℝ)*(major0) + (3961943512038201/100000000000000 : ℝ)*(major1) + (3961943512038201/100000000000000 : ℝ)*(major2) + (1311039669172967/25000000000000 : ℝ)*(sp0) + (5244109208142891/100000000000000 : ℝ)*(sp1) + (1048823652150547/20000000000000 : ℝ)*(sp2) + (2659965457981719/100000000000000 : ℝ)*(sp3) + (3265120297/6250000000000 : ℝ)*(sp9) + (43189314909/100000000000000 : ℝ)*(sp10) + (86667993/3125000000000 : ℝ)*(sp12) + (2659965457981719/100000000000000 : ℝ)*(f.failure) + (5244161450067643/100000000000000 : ℝ)*(f.sum) + (19630976689901/6782500000000000000000000000 : ℝ)*base66 + (853983580295816857/42390625000000000000000000000000 : ℝ)*base68 + (457974687169973107/42390625000000000000000000000000 : ℝ)*base70 + (59847839008822491/21195312500000000000000000000000 : ℝ)*base72 + (717124643963/3391250000000000000000000000 : ℝ)*base74 + (113894130695910607/42390625000000000000000000000000 : ℝ)*base76 + (219103625133166241/21195312500000000000000000000000 : ℝ)*base78 + (658720354316504357/42390625000000000000000000000000 : ℝ)*base80 + (32912657560749/6782500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (21379299/10000000000000000000000 : ℝ)*base90 + (21379299/10000000000000000000000 : ℝ)*base92 + (21379299/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (3189/4000 : ℝ) ≤ (33797090070045828126580810373943/42390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85847897/25000000000000 : ℝ)*(upper0) + (98135091/100000000000000 : ℝ)*(upper1) + (17918863/4000000000000 : ℝ)*(upper2) + (518750157/50000000000000 : ℝ)*(lower5) + (2215000904962759/50000000000000 : ℝ)*(major0) + (2215000904962759/50000000000000 : ℝ)*(major1) + (2215000904962759/50000000000000 : ℝ)*(major2) + (232242143691/50000000000000 : ℝ)*(sp1) + (84337182553/50000000000000 : ℝ)*(sp3) + (1171842457692183/20000000000000 : ℝ)*(sp8) + (5858753275502699/100000000000000 : ℝ)*(sp9) + (5859217759790081/100000000000000 : ℝ)*(sp10) + (1487020635086011/50000000000000 : ℝ)*(sp11) + (2735664583/50000000000000 : ℝ)*(sp12) + (2974209944537129/100000000000000 : ℝ)*(f.failure) + (5859217759790081/100000000000000 : ℝ)*(f.sum) + (4258558350497/6782500000000000000000000000 : ℝ)*base65 + (369849192067956887/21195312500000000000000000000000 : ℝ)*base67 + (111120896638581887/21195312500000000000000000000000 : ℝ)*base69 + (622585646204210649/42390625000000000000000000000000 : ℝ)*base71 + (120489004103723/6782500000000000000000000000 : ℝ)*base74 + (501664545456394387/21195312500000000000000000000000 : ℝ)*base75 + (413277078911929399/42390625000000000000000000000000 : ℝ)*base77 + (500243740805595631/10597656250000000000000000000000 : ℝ)*base79 + (88415365064349/13565000000000000000000000000 : ℝ)*base81 + (25309091/10000000000000000000000 : ℝ)*base89 + (25309091/10000000000000000000000 : ℝ)*base91 + (25309091/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-10383/12500 : ℝ) ≤ (-35210123325114676151897399862021/42390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214373313/100000000000000 : ℝ)*(lower0) + (3673277/10000000000000 : ℝ)*(lower1) + (2581877/4000000000000 : ℝ)*(lower2) + (2232418098624069/50000000000000 : ℝ)*(major0) + (2232418098624069/50000000000000 : ℝ)*(major1) + (2232418098624069/50000000000000 : ℝ)*(major2) + (7641294251/100000000000000 : ℝ)*(sp0) + (76466164159/25000000000000 : ℝ)*(sp5) + (31263872691/100000000000000 : ℝ)*(sp6) + (12368708319/50000000000000 : ℝ)*(sp7) + (1191950954166637/20000000000000 : ℝ)*(sp12) + (5959456547470801/100000000000000 : ℝ)*(sp13) + (2979865574127373/50000000000000 : ℝ)*(sp14) + (2997572281354787/100000000000000 : ℝ)*(sp15) + (1498798509385713/50000000000000 : ℝ)*(f.failure) + (1489940603031859/25000000000000 : ℝ)*(f.sum) + (81086235644191/13565000000000000000000000000 : ℝ)*base66 + (717046943635717/21195312500000000000000000000000 : ℝ)*base67 + (104576252017145533/21195312500000000000000000000000 : ℝ)*base70 + (60871730188739283/21195312500000000000000000000000 : ℝ)*base72 + (54552453922531/3391250000000000000000000000 : ℝ)*base73 + (403147008682568309/42390625000000000000000000000000 : ℝ)*base75 + (4532233908778397/331176757812500000000000000000 : ℝ)*base78 + (295611685992837941/42390625000000000000000000000000 : ℝ)*base80 + (4484506453821/3391250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (74253627/5000000000000000000000 : ℝ)*base89 + (74253627/5000000000000000000000 : ℝ)*base91 + (74253627/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1115_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29639/50000 : ℝ) else (3189/4000 : ℝ) ≤ X j i ∧ X j i ≤ (10383/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1115_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1115_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29639/50000 : ℝ) else (3189/4000 : ℝ) ≤ X j i ∧ X j i ≤ (10383/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1115_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1115_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1115_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29639/50000 : ℝ) else (3189/4000 : ℝ) ≤ X j i ∧ X j i ≤ (10383/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1115_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

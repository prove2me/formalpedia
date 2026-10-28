-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1078_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:48:21.453349+00:00
-- url     : https://prove2.me/submissions/e04bfd9c-3366-42df-a23c-336425c73da9

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
theorem support_rectangle_w1078_s3_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109664689/500000000 : ℝ)*x 0 + (2718076447/5000000000 : ℝ)*x 1 + (5225660389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109664689/500000000 : ℝ)^8271 ≤ (3328056126637/25000000000000 : ℝ)^6223 := by
    have hnat : (109664689 : ℕ)^8271*25000000000000^6223 ≤ 3328056126637^6223*500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109664689 500000000 3328056126637 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718076447/5000000000 : ℝ)^8271 ≤ (8896223593553/20000000000000 : ℝ)^6223 := by
    have hnat : (2718076447 : ℕ)^8271*20000000000000^6223 ≤ 8896223593553^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718076447 5000000000 8896223593553 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225660389/10000000000 : ℝ)^8271 ≤ (8441331501581/20000000000000 : ℝ)^6223 := by
    have hnat : (5225660389 : ℕ)^8271*20000000000000^6223 ≤ 8441331501581^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225660389 10000000000 8441331501581 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109664689/500000000 : ℝ), (2718076447/5000000000 : ℝ), (5225660389/10000000000 : ℝ)] ![(3328056126637/25000000000000 : ℝ), (8896223593553/20000000000000 : ℝ), (8441331501581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109664689/500000000 : ℝ)|^8271 ≤ (3328056126637/25000000000000 : ℝ)^6223
        have hw : |(-109664689/500000000 : ℝ)|=(109664689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718076447/5000000000 : ℝ)|^8271 ≤ (8896223593553/20000000000000 : ℝ)^6223
        have hw : |(2718076447/5000000000 : ℝ)|=(2718076447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225660389/10000000000 : ℝ)|^8271 ≤ (8441331501581/20000000000000 : ℝ)^6223
        have hw : |(5225660389/10000000000 : ℝ)|=(5225660389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s3_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677692257/5000000000 : ℝ)*x 0 + (-460210151/2000000000 : ℝ)*x 1 + (2612830209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677692257/5000000000 : ℝ)^8271 ≤ (21802445126879/50000000000000 : ℝ)^6223 := by
    have hnat : (2677692257 : ℕ)^8271*50000000000000^6223 ≤ 21802445126879^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677692257 5000000000 21802445126879 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460210151/2000000000 : ℝ)^8271 ≤ (14188451919579/100000000000000 : ℝ)^6223 := by
    have hnat : (460210151 : ℕ)^8271*100000000000000^6223 ≤ 14188451919579^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460210151 2000000000 14188451919579 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612830209/5000000000 : ℝ)^8271 ≤ (21103328909609/50000000000000 : ℝ)^6223 := by
    have hnat : (2612830209 : ℕ)^8271*50000000000000^6223 ≤ 21103328909609^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612830209 5000000000 21103328909609 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677692257/5000000000 : ℝ), (-460210151/2000000000 : ℝ), (2612830209/5000000000 : ℝ)] ![(21802445126879/50000000000000 : ℝ), (14188451919579/100000000000000 : ℝ), (21103328909609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677692257/5000000000 : ℝ)|^8271 ≤ (21802445126879/50000000000000 : ℝ)^6223
        have hw : |(2677692257/5000000000 : ℝ)|=(2677692257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-460210151/2000000000 : ℝ)|^8271 ≤ (14188451919579/100000000000000 : ℝ)^6223
        have hw : |(-460210151/2000000000 : ℝ)|=(460210151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612830209/5000000000 : ℝ)|^8271 ≤ (21103328909609/50000000000000 : ℝ)^6223
        have hw : |(2612830209/5000000000 : ℝ)|=(2612830209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s3_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355384463/10000000000 : ℝ)*x 0 + (2612830411/5000000000 : ℝ)*x 1 + (-575262573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355384463/10000000000 : ℝ)^8271 ≤ (21802444850921/50000000000000 : ℝ)^6223 := by
    have hnat : (5355384463 : ℕ)^8271*50000000000000^6223 ≤ 21802444850921^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355384463 10000000000 21802444850921 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612830411/5000000000 : ℝ)^8271 ≤ (42206662156117/100000000000000 : ℝ)^6223 := by
    have hnat : (2612830411 : ℕ)^8271*100000000000000^6223 ≤ 42206662156117^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612830411 5000000000 42206662156117 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575262573/2500000000 : ℝ)^8271 ≤ (886778007821/6250000000000 : ℝ)^6223 := by
    have hnat : (575262573 : ℕ)^8271*6250000000000^6223 ≤ 886778007821^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575262573 2500000000 886778007821 6250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355384463/10000000000 : ℝ), (2612830411/5000000000 : ℝ), (-575262573/2500000000 : ℝ)] ![(21802444850921/50000000000000 : ℝ), (42206662156117/100000000000000 : ℝ), (886778007821/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355384463/10000000000 : ℝ)|^8271 ≤ (21802444850921/50000000000000 : ℝ)^6223
        have hw : |(5355384463/10000000000 : ℝ)|=(5355384463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612830411/5000000000 : ℝ)|^8271 ≤ (42206662156117/100000000000000 : ℝ)^6223
        have hw : |(2612830411/5000000000 : ℝ)|=(2612830411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-575262573/2500000000 : ℝ)|^8271 ≤ (886778007821/6250000000000 : ℝ)^6223
        have hw : |(-575262573/2500000000 : ℝ)|=(575262573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s3_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092764979/2500000000 : ℝ)*x 0 + (4169233071/10000000000 : ℝ)*x 1 + (4582750817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092764979/2500000000 : ℝ)^8271 ≤ (6657838249169/20000000000000 : ℝ)^6223 := by
    have hnat : (1092764979 : ℕ)^8271*20000000000000^6223 ≤ 6657838249169^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092764979 2500000000 6657838249169 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169233071/10000000000 : ℝ)^8271 ≤ (15630972963997/50000000000000 : ℝ)^6223 := by
    have hnat : (4169233071 : ℕ)^8271*50000000000000^6223 ≤ 15630972963997^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169233071 10000000000 15630972963997 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4582750817/10000000000 : ℝ)^8271 ≤ (7089772560183/20000000000000 : ℝ)^6223 := by
    have hnat : (4582750817 : ℕ)^8271*20000000000000^6223 ≤ 7089772560183^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582750817 10000000000 7089772560183 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092764979/2500000000 : ℝ), (4169233071/10000000000 : ℝ), (4582750817/10000000000 : ℝ)] ![(6657838249169/20000000000000 : ℝ), (15630972963997/50000000000000 : ℝ), (7089772560183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092764979/2500000000 : ℝ)|^8271 ≤ (6657838249169/20000000000000 : ℝ)^6223
        have hw : |(1092764979/2500000000 : ℝ)|=(1092764979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169233071/10000000000 : ℝ)|^8271 ≤ (15630972963997/50000000000000 : ℝ)^6223
        have hw : |(4169233071/10000000000 : ℝ)|=(4169233071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4582750817/10000000000 : ℝ)|^8271 ≤ (7089772560183/20000000000000 : ℝ)^6223
        have hw : |(4582750817/10000000000 : ℝ)|=(4582750817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s3_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219331593/1000000000 : ℝ)*x 0 + (326657219/625000000 : ℝ)*x 1 + (2717646173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219331593/1000000000 : ℝ)^8271 ≤ (13312403190891/100000000000000 : ℝ)^6223 := by
    have hnat : (219331593 : ℕ)^8271*100000000000000^6223 ≤ 13312403190891^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219331593 1000000000 13312403190891 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326657219/625000000 : ℝ)^8271 ≤ (2110791866449/5000000000000 : ℝ)^6223 := by
    have hnat : (326657219 : ℕ)^8271*5000000000000^6223 ≤ 2110791866449^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326657219 625000000 2110791866449 5000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717646173/5000000000 : ℝ)^8271 ≤ (8894351894447/20000000000000 : ℝ)^6223 := by
    have hnat : (2717646173 : ℕ)^8271*20000000000000^6223 ≤ 8894351894447^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717646173 5000000000 8894351894447 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219331593/1000000000 : ℝ), (326657219/625000000 : ℝ), (2717646173/5000000000 : ℝ)] ![(13312403190891/100000000000000 : ℝ), (2110791866449/5000000000000 : ℝ), (8894351894447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219331593/1000000000 : ℝ)|^8271 ≤ (13312403190891/100000000000000 : ℝ)^6223
        have hw : |(-219331593/1000000000 : ℝ)|=(219331593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326657219/625000000 : ℝ)|^8271 ≤ (2110791866449/5000000000000 : ℝ)^6223
        have hw : |(326657219/625000000 : ℝ)|=(326657219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717646173/5000000000 : ℝ)|^8271 ≤ (8894351894447/20000000000000 : ℝ)^6223
        have hw : |(2717646173/5000000000 : ℝ)|=(2717646173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s3_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060462519/2000000000 : ℝ)*x 0 + (-2091419299/10000000000 : ℝ)*x 1 + (1358823057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060462519/2000000000 : ℝ)^8271 ≤ (1075787272819/2500000000000 : ℝ)^6223 := by
    have hnat : (1060462519 : ℕ)^8271*2500000000000^6223 ≤ 1075787272819^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060462519 2000000000 1075787272819 2500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091419299/10000000000 : ℝ)^8271 ≤ (1249675088451/10000000000000 : ℝ)^6223 := by
    have hnat : (2091419299 : ℕ)^8271*10000000000000^6223 ≤ 1249675088451^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091419299 10000000000 1249675088451 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358823057/2500000000 : ℝ)^8271 ≤ (44471758189013/100000000000000 : ℝ)^6223 := by
    have hnat : (1358823057 : ℕ)^8271*100000000000000^6223 ≤ 44471758189013^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358823057 2500000000 44471758189013 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060462519/2000000000 : ℝ), (-2091419299/10000000000 : ℝ), (1358823057/2500000000 : ℝ)] ![(1075787272819/2500000000000 : ℝ), (1249675088451/10000000000000 : ℝ), (44471758189013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060462519/2000000000 : ℝ)|^8271 ≤ (1075787272819/2500000000000 : ℝ)^6223
        have hw : |(1060462519/2000000000 : ℝ)|=(1060462519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091419299/10000000000 : ℝ)|^8271 ≤ (1249675088451/10000000000000 : ℝ)^6223
        have hw : |(-2091419299/10000000000 : ℝ)|=(2091419299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358823057/2500000000 : ℝ)|^8271 ≤ (44471758189013/100000000000000 : ℝ)^6223
        have hw : |(1358823057/2500000000 : ℝ)|=(1358823057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s3_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302312907/10000000000 : ℝ)*x 0 + (5435292723/10000000000 : ℝ)*x 1 + (-2091418197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302312907/10000000000 : ℝ)^8271 ≤ (21515747139069/50000000000000 : ℝ)^6223 := by
    have hnat : (5302312907 : ℕ)^8271*50000000000000^6223 ≤ 21515747139069^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302312907 10000000000 21515747139069 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435292723/10000000000 : ℝ)^8271 ≤ (44471763572019/100000000000000 : ℝ)^6223 := by
    have hnat : (5435292723 : ℕ)^8271*100000000000000^6223 ≤ 44471763572019^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435292723 10000000000 44471763572019 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091418197/10000000000 : ℝ)^8271 ≤ (12496742132743/100000000000000 : ℝ)^6223 := by
    have hnat : (2091418197 : ℕ)^8271*100000000000000^6223 ≤ 12496742132743^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091418197 10000000000 12496742132743 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302312907/10000000000 : ℝ), (5435292723/10000000000 : ℝ), (-2091418197/10000000000 : ℝ)] ![(21515747139069/50000000000000 : ℝ), (44471763572019/100000000000000 : ℝ), (12496742132743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302312907/10000000000 : ℝ)|^8271 ≤ (21515747139069/50000000000000 : ℝ)^6223
        have hw : |(5302312907/10000000000 : ℝ)|=(5302312907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435292723/10000000000 : ℝ)|^8271 ≤ (44471763572019/100000000000000 : ℝ)^6223
        have hw : |(5435292723/10000000000 : ℝ)|=(5435292723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091418197/10000000000 : ℝ)|^8271 ≤ (12496742132743/100000000000000 : ℝ)^6223
        have hw : |(-2091418197/10000000000 : ℝ)|=(2091418197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s3_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874220339/2000000000 : ℝ)*x 0 + (4581071383/10000000000 : ℝ)*x 1 + (65170671/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874220339/2000000000 : ℝ)^8271 ≤ (332896141417/1000000000000 : ℝ)^6223 := by
    have hnat : (874220339 : ℕ)^8271*1000000000000^6223 ≤ 332896141417^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874220339 2000000000 332896141417 1000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4581071383/10000000000 : ℝ)^8271 ≤ (17715798811997/50000000000000 : ℝ)^6223 := by
    have hnat : (4581071383 : ℕ)^8271*50000000000000^6223 ≤ 17715798811997^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581071383 10000000000 17715798811997 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65170671/156250000 : ℝ)^8271 ≤ (7819697053931/25000000000000 : ℝ)^6223 := by
    have hnat : (65170671 : ℕ)^8271*25000000000000^6223 ≤ 7819697053931^6223*156250000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65170671 156250000 7819697053931 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874220339/2000000000 : ℝ), (4581071383/10000000000 : ℝ), (65170671/156250000 : ℝ)] ![(332896141417/1000000000000 : ℝ), (17715798811997/50000000000000 : ℝ), (7819697053931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874220339/2000000000 : ℝ)|^8271 ≤ (332896141417/1000000000000 : ℝ)^6223
        have hw : |(874220339/2000000000 : ℝ)|=(874220339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4581071383/10000000000 : ℝ)|^8271 ≤ (17715798811997/50000000000000 : ℝ)^6223
        have hw : |(4581071383/10000000000 : ℝ)|=(4581071383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65170671/156250000 : ℝ)|^8271 ≤ (7819697053931/25000000000000 : ℝ)^6223
        have hw : |(65170671/156250000 : ℝ)|=(65170671/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (877/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2087/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14889/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (877/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (877/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (877/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (877/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (877/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (877/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (877/10000 : ℝ) ^ (4135/1024 : ℝ) ≤ (1078379237724997/20000000000000000000 : ℝ) := by
    have hpowers : (877/10000 : ℝ)^4135 ≤ (1078379237724997/20000000000000000000 : ℝ)^1024 := by
      have hnat : (877 : ℕ)^4135*20000000000000000000^1024 ≤ 1078379237724997^1024*10000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        877 10000 1078379237724997 20000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (877/10000 : ℝ)) (X := (1078379237724997/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8351/50000 : ℝ) ^ (4135/1024 : ℝ) ≤ (18172401977926001/25000000000000000000 : ℝ) := by
    have hpowers : (8351/50000 : ℝ)^4135 ≤ (18172401977926001/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8351 : ℕ)^4135*25000000000000000000^1024 ≤ 18172401977926001^1024*50000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8351 50000 18172401977926001 25000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8351/50000 : ℝ)) (X := (18172401977926001/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001078379237724997/10000000000000000000 : ℝ) ≤ (10000267041244603/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (10001078379237724997/10000000000000000000 : ℝ)^1024 ≤ (10000267041244603/10000000000000000 : ℝ)^4135 := by
      have hnat : (10001078379237724997 : ℕ)^1024*10000000000000000^4135 ≤ 10000267041244603^4135*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001078379237724997 10000000000000000000 10000267041244603 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000267041244603/10000000000000000 : ℝ)) (X := (10001078379237724997/10000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078081504100328989/100000000000000000000 : ℝ) ≤ (10001933058909107/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (100078081504100328989/100000000000000000000 : ℝ)^1024 ≤ (10001933058909107/10000000000000000 : ℝ)^4135 := by
      have hnat : (100078081504100328989 : ℕ)^1024*10000000000000000^4135 ≤ 10001933058909107^4135*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078081504100328989 100000000000000000000 10001933058909107 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001933058909107/10000000000000000 : ℝ)) (X := (100078081504100328989/100000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518172401977926001/12500000000000000000 : ℝ) ≤ (10003599076573611/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (12518172401977926001/12500000000000000000 : ℝ)^1024 ≤ (10003599076573611/10000000000000000 : ℝ)^4135 := by
      have hnat : (12518172401977926001 : ℕ)^1024*10000000000000000^4135 ≤ 10003599076573611^4135*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518172401977926001 12500000000000000000 10003599076573611 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003599076573611/10000000000000000 : ℝ)) (X := (12518172401977926001/12500000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1078379237724997/20000000000000000000 : ℝ) ≤ ((19823224055329197709/19830000000000000000 : ℝ)+2*(208252208063/99150000000000 : ℝ)*(877/10000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (19823224055329197709/19830000000000000000 : ℝ)+2*(208252208063/99150000000000 : ℝ)*(877/10000 : ℝ)=(10000267041244603/10000000000000000 : ℝ) by norm_num, show 1+2*(1078379237724997/20000000000000000000 : ℝ)=(10001078379237724997/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18172401977926001/25000000000000000000 : ℝ)+(1078379237724997/20000000000000000000 : ℝ) ≤ ((19823224055329197709/19830000000000000000 : ℝ)+(208252208063/99150000000000 : ℝ)*((8351/50000 : ℝ)+(877/10000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (19823224055329197709/19830000000000000000 : ℝ)+(208252208063/99150000000000 : ℝ)*((8351/50000 : ℝ)+(877/10000 : ℝ))=(10001933058909107/10000000000000000 : ℝ) by norm_num, show 1+(18172401977926001/25000000000000000000 : ℝ)+(1078379237724997/20000000000000000000 : ℝ)=(100078081504100328989/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18172401977926001/25000000000000000000 : ℝ) ≤ ((19823224055329197709/19830000000000000000 : ℝ)+2*(208252208063/99150000000000 : ℝ)*(8351/50000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (19823224055329197709/19830000000000000000 : ℝ)+2*(208252208063/99150000000000 : ℝ)*(8351/50000 : ℝ)=(10003599076573611/10000000000000000 : ℝ) by norm_num, show 1+2*(18172401977926001/25000000000000000000 : ℝ)=(12518172401977926001/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19823224055329197709/19830000000000000000 : ℝ)*(X 1 0+X 2 0)+(208252208063/99150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (877/10000 : ℝ)) (hi := (8351/50000 : ℝ)) (c := (19823224055329197709/19830000000000000000 : ℝ)) (alpha := (208252208063/99150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19823224055329197709/19830000000000000000 : ℝ)*(X 0 1+X 2 1)+(208252208063/99150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (877/10000 : ℝ)) (hi := (8351/50000 : ℝ)) (c := (19823224055329197709/19830000000000000000 : ℝ)) (alpha := (208252208063/99150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19823224055329197709/19830000000000000000 : ℝ)*(X 0 2+X 1 2)+(208252208063/99150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (877/10000 : ℝ)) (hi := (8351/50000 : ℝ)) (c := (19823224055329197709/19830000000000000000 : ℝ)) (alpha := (208252208063/99150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-109664689/500000000 : ℝ)*X 0 0+(2718076447/5000000000 : ℝ)*X 0 1+(5225660389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677692257/5000000000 : ℝ)*X 1 0+(-460210151/2000000000 : ℝ)*X 1 1+(2612830209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355384463/10000000000 : ℝ)*X 2 0+(2612830411/5000000000 : ℝ)*X 2 1+(-575262573/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092764979/2500000000 : ℝ)*X 0 0+(4169233071/10000000000 : ℝ)*X 0 1+(4582750817/10000000000 : ℝ)*X 0 2+(1092764979/2500000000 : ℝ)*X 1 0+(4169233071/10000000000 : ℝ)*X 1 1+(4582750817/10000000000 : ℝ)*X 1 2+(1092764979/2500000000 : ℝ)*X 2 0+(4169233071/10000000000 : ℝ)*X 2 1+(4582750817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219331593/1000000000 : ℝ)*X 0 0+(326657219/625000000 : ℝ)*X 0 1+(2717646173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060462519/2000000000 : ℝ)*X 1 0+(-2091419299/10000000000 : ℝ)*X 1 1+(1358823057/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302312907/10000000000 : ℝ)*X 2 0+(5435292723/10000000000 : ℝ)*X 2 1+(-2091418197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874220339/2000000000 : ℝ)*X 0 0+(4581071383/10000000000 : ℝ)*X 0 1+(65170671/156250000 : ℝ)*X 0 2+(874220339/2000000000 : ℝ)*X 1 0+(4581071383/10000000000 : ℝ)*X 1 1+(65170671/156250000 : ℝ)*X 1 2+(874220339/2000000000 : ℝ)*X 2 0+(4581071383/10000000000 : ℝ)*X 2 1+(65170671/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (714571203049424548607806367/82625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277379291/12500000000000 : ℝ)*(base19) + (349619287/20000000000000 : ℝ)*(base23) + (227976041/100000000000000 : ℝ)*(lower2) + (115849993/100000000000000 : ℝ)*(upper3) + (117161003/50000000000000 : ℝ)*(upper5) + (1792289617057363/50000000000000 : ℝ)*(major0) + (1792289617057363/50000000000000 : ℝ)*(major1) + (1792289617057363/50000000000000 : ℝ)*(major2) + (1187700270906993/25000000000000 : ℝ)*(sp0) + (237542226683549/5000000000000 : ℝ)*(sp1) + (4750845004608873/100000000000000 : ℝ)*(sp2) + (60457341879083/2500000000000 : ℝ)*(sp3) + (5708634667/12500000000000 : ℝ)*(sp4) + (8876040981/50000000000000 : ℝ)*(sp7) + (2418311427245281/100000000000000 : ℝ)*(f.failure) + (4750846752705309/100000000000000 : ℝ)*(f.sum) + (20147151336287/4957500000000000000000000000 : ℝ)*base66 + (12633800269642018633/991500000000000000000000000000000 : ℝ)*base68 + (2157435232783018633/991500000000000000000000000000000 : ℝ)*base70 + (11694247881550018633/991500000000000000000000000000000 : ℝ)*base72 + (30052381075457/4957500000000000000000000000 : ℝ)*base74 + (2318594076562981367/991500000000000000000000000000000 : ℝ)*base75 + (5738244400478518633/991500000000000000000000000000000 : ℝ)*base78 + (13708095768643018633/991500000000000000000000000000000 : ℝ)*base80 + (6821608774763/1239375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (453733/2000000000000000000000 : ℝ)*base90 + (453733/2000000000000000000000 : ℝ)*base92 + (453733/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (257982158419909503355900101/41312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15909153/1250000000000 : ℝ)*(base19) + (142419159/6250000000000 : ℝ)*(base23) + (211323023/100000000000000 : ℝ)*(upper2) + (170045011/100000000000000 : ℝ)*(upper3) + (53139887/25000000000000 : ℝ)*(upper5) + (451746676843911/12500000000000 : ℝ)*(major0) + (451746676843911/12500000000000 : ℝ)*(major1) + (451746676843911/12500000000000 : ℝ)*(major2) + (16905848859/100000000000000 : ℝ)*(sp1) + (24717265777/50000000000000 : ℝ)*(sp2) + (598725576844399/12500000000000 : ℝ)*(sp4) + (4789786436174093/100000000000000 : ℝ)*(sp5) + (4789752901517093/100000000000000 : ℝ)*(sp6) + (1219071003296167/50000000000000 : ℝ)*(sp7) + (1219071003296167/50000000000000 : ℝ)*(f.failure) + (598725576844399/12500000000000 : ℝ)*(f.sum) + (5561022239377/1652500000000000000000000000 : ℝ)*base66 + (121875241982216633/82625000000000000000000000000000 : ℝ)*base67 + (324844838282533367/82625000000000000000000000000000 : ℝ)*base70 + (257305689362091633/82625000000000000000000000000000 : ℝ)*base71 + (7602059691877/1652500000000000000000000000 : ℝ)*base74 + (90458521066783367/82625000000000000000000000000000 : ℝ)*base76 + (287869173273091633/82625000000000000000000000000000 : ℝ)*base77 + (1051316029257341633/82625000000000000000000000000000 : ℝ)*base79 + (24526657274039/3305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2638269/1000000000000000000000 : ℝ)*base89 + (2638269/1000000000000000000000 : ℝ)*base91 + (2638269/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1078_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (877/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14889/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1078_s4_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196857439/10000000000 : ℝ)*x 0 + (337822627/625000000 : ℝ)*x 1 + (5254322609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196857439/10000000000 : ℝ)^8271 ≤ (13340980226321/100000000000000 : ℝ)^6223 := by
    have hnat : (2196857439 : ℕ)^8271*100000000000000^6223 ≤ 13340980226321^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196857439 10000000000 13340980226321 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337822627/625000000 : ℝ)^8271 ≤ (44144398838499/100000000000000 : ℝ)^6223 := by
    have hnat : (337822627 : ℕ)^8271*100000000000000^6223 ≤ 44144398838499^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337822627 625000000 44144398838499 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254322609/10000000000 : ℝ)^8271 ≤ (42514620930471/100000000000000 : ℝ)^6223 := by
    have hnat : (5254322609 : ℕ)^8271*100000000000000^6223 ≤ 42514620930471^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254322609 10000000000 42514620930471 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196857439/10000000000 : ℝ), (337822627/625000000 : ℝ), (5254322609/10000000000 : ℝ)] ![(13340980226321/100000000000000 : ℝ), (44144398838499/100000000000000 : ℝ), (42514620930471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196857439/10000000000 : ℝ)|^8271 ≤ (13340980226321/100000000000000 : ℝ)^6223
        have hw : |(-2196857439/10000000000 : ℝ)|=(2196857439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337822627/625000000 : ℝ)|^8271 ≤ (44144398838499/100000000000000 : ℝ)^6223
        have hw : |(337822627/625000000 : ℝ)|=(337822627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254322609/10000000000 : ℝ)|^8271 ≤ (42514620930471/100000000000000 : ℝ)^6223
        have hw : |(5254322609/10000000000 : ℝ)|=(5254322609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s4_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673848517/5000000000 : ℝ)*x 0 + (-1136783903/5000000000 : ℝ)*x 1 + (5254322471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673848517/5000000000 : ℝ)^8271 ≤ (1360053653629/3125000000000 : ℝ)^6223 := by
    have hnat : (2673848517 : ℕ)^8271*3125000000000^6223 ≤ 1360053653629^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673848517 5000000000 1360053653629 3125000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136783903/5000000000 : ℝ)^8271 ≤ (13963663623487/100000000000000 : ℝ)^6223 := by
    have hnat : (1136783903 : ℕ)^8271*100000000000000^6223 ≤ 13963663623487^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136783903 5000000000 13963663623487 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254322471/10000000000 : ℝ)^8271 ≤ (21257309723193/50000000000000 : ℝ)^6223 := by
    have hnat : (5254322471 : ℕ)^8271*50000000000000^6223 ≤ 21257309723193^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254322471 10000000000 21257309723193 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673848517/5000000000 : ℝ), (-1136783903/5000000000 : ℝ), (5254322471/10000000000 : ℝ)] ![(1360053653629/3125000000000 : ℝ), (13963663623487/100000000000000 : ℝ), (21257309723193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673848517/5000000000 : ℝ)|^8271 ≤ (1360053653629/3125000000000 : ℝ)^6223
        have hw : |(2673848517/5000000000 : ℝ)|=(2673848517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1136783903/5000000000 : ℝ)|^8271 ≤ (13963663623487/100000000000000 : ℝ)^6223
        have hw : |(-1136783903/5000000000 : ℝ)|=(1136783903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254322471/10000000000 : ℝ)|^8271 ≤ (21257309723193/50000000000000 : ℝ)^6223
        have hw : |(5254322471/10000000000 : ℝ)|=(5254322471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s4_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347697167/10000000000 : ℝ)*x 0 + (5254322499/10000000000 : ℝ)*x 1 + (-1136783797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347697167/10000000000 : ℝ)^8271 ≤ (21760859177379/50000000000000 : ℝ)^6223 := by
    have hnat : (5347697167 : ℕ)^8271*50000000000000^6223 ≤ 21760859177379^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347697167 10000000000 21760859177379 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254322499/10000000000 : ℝ)^8271 ≤ (8502923949501/20000000000000 : ℝ)^6223 := by
    have hnat : (5254322499 : ℕ)^8271*20000000000000^6223 ≤ 8502923949501^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254322499 10000000000 8502923949501 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136783797/5000000000 : ℝ)^8271 ≤ (3490915473233/25000000000000 : ℝ)^6223 := by
    have hnat : (1136783797 : ℕ)^8271*25000000000000^6223 ≤ 3490915473233^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136783797 5000000000 3490915473233 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347697167/10000000000 : ℝ), (5254322499/10000000000 : ℝ), (-1136783797/5000000000 : ℝ)] ![(21760859177379/50000000000000 : ℝ), (8502923949501/20000000000000 : ℝ), (3490915473233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347697167/10000000000 : ℝ)|^8271 ≤ (21760859177379/50000000000000 : ℝ)^6223
        have hw : |(5347697167/10000000000 : ℝ)|=(5347697167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254322499/10000000000 : ℝ)|^8271 ≤ (8502923949501/20000000000000 : ℝ)^6223
        have hw : |(5254322499/10000000000 : ℝ)|=(5254322499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1136783797/5000000000 : ℝ)|^8271 ≤ (3490915473233/25000000000000 : ℝ)^6223
        have hw : |(-1136783797/5000000000 : ℝ)|=(1136783797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s4_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437318013/1000000000 : ℝ)*x 0 + (4227550053/10000000000 : ℝ)*x 1 + (4523878689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437318013/1000000000 : ℝ)^8271 ≤ (33310654178411/100000000000000 : ℝ)^6223 := by
    have hnat : (437318013 : ℕ)^8271*100000000000000^6223 ≤ 33310654178411^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437318013 1000000000 33310654178411 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227550053/10000000000 : ℝ)^8271 ≤ (3184446270377/10000000000000 : ℝ)^6223 := by
    have hnat : (4227550053 : ℕ)^8271*10000000000000^6223 ≤ 3184446270377^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227550053 10000000000 3184446270377 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523878689/10000000000 : ℝ)^8271 ≤ (6968976621979/20000000000000 : ℝ)^6223 := by
    have hnat : (4523878689 : ℕ)^8271*20000000000000^6223 ≤ 6968976621979^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523878689 10000000000 6968976621979 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437318013/1000000000 : ℝ), (4227550053/10000000000 : ℝ), (4523878689/10000000000 : ℝ)] ![(33310654178411/100000000000000 : ℝ), (3184446270377/10000000000000 : ℝ), (6968976621979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437318013/1000000000 : ℝ)|^8271 ≤ (33310654178411/100000000000000 : ℝ)^6223
        have hw : |(437318013/1000000000 : ℝ)|=(437318013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227550053/10000000000 : ℝ)|^8271 ≤ (3184446270377/10000000000000 : ℝ)^6223
        have hw : |(4227550053/10000000000 : ℝ)|=(4227550053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523878689/10000000000 : ℝ)|^8271 ≤ (6968976621979/20000000000000 : ℝ)^6223
        have hw : |(4523878689/10000000000 : ℝ)|=(4523878689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s4_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098432831/5000000000 : ℝ)*x 0 + (5254762539/10000000000 : ℝ)*x 1 + (5404720053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098432831/5000000000 : ℝ)^8271 ≤ (13341046596753/100000000000000 : ℝ)^6223 := by
    have hnat : (1098432831 : ℕ)^8271*100000000000000^6223 ≤ 13341046596753^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098432831 5000000000 13341046596753 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254762539/10000000000 : ℝ)^8271 ≤ (42519352109243/100000000000000 : ℝ)^6223 := by
    have hnat : (5254762539 : ℕ)^8271*100000000000000^6223 ≤ 42519352109243^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254762539 10000000000 42519352109243 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404720053/10000000000 : ℝ)^8271 ≤ (22069800636567/50000000000000 : ℝ)^6223 := by
    have hnat : (5404720053 : ℕ)^8271*50000000000000^6223 ≤ 22069800636567^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404720053 10000000000 22069800636567 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098432831/5000000000 : ℝ), (5254762539/10000000000 : ℝ), (5404720053/10000000000 : ℝ)] ![(13341046596753/100000000000000 : ℝ), (42519352109243/100000000000000 : ℝ), (22069800636567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098432831/5000000000 : ℝ)|^8271 ≤ (13341046596753/100000000000000 : ℝ)^6223
        have hw : |(-1098432831/5000000000 : ℝ)|=(1098432831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254762539/10000000000 : ℝ)|^8271 ≤ (42519352109243/100000000000000 : ℝ)^6223
        have hw : |(5254762539/10000000000 : ℝ)|=(5254762539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404720053/10000000000 : ℝ)|^8271 ≤ (22069800636567/50000000000000 : ℝ)^6223
        have hw : |(5404720053/10000000000 : ℝ)|=(5404720053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s4_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654834899/5000000000 : ℝ)*x 0 + (-2123169601/10000000000 : ℝ)*x 1 + (337795009/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654834899/5000000000 : ℝ)^8271 ≤ (10777716816463/25000000000000 : ℝ)^6223 := by
    have hnat : (2654834899 : ℕ)^8271*25000000000000^6223 ≤ 10777716816463^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654834899 5000000000 10777716816463 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123169601/10000000000 : ℝ)^8271 ≤ (12749530460813/100000000000000 : ℝ)^6223 := by
    have hnat : (2123169601 : ℕ)^8271*100000000000000^6223 ≤ 12749530460813^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123169601 10000000000 12749530460813 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337795009/625000000 : ℝ)^8271 ≤ (22069801130451/50000000000000 : ℝ)^6223 := by
    have hnat : (337795009 : ℕ)^8271*50000000000000^6223 ≤ 22069801130451^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337795009 625000000 22069801130451 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654834899/5000000000 : ℝ), (-2123169601/10000000000 : ℝ), (337795009/625000000 : ℝ)] ![(10777716816463/25000000000000 : ℝ), (12749530460813/100000000000000 : ℝ), (22069801130451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654834899/5000000000 : ℝ)|^8271 ≤ (10777716816463/25000000000000 : ℝ)^6223
        have hw : |(2654834899/5000000000 : ℝ)|=(2654834899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123169601/10000000000 : ℝ)|^8271 ≤ (12749530460813/100000000000000 : ℝ)^6223
        have hw : |(-2123169601/10000000000 : ℝ)|=(2123169601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337795009/625000000 : ℝ)|^8271 ≤ (22069801130451/50000000000000 : ℝ)^6223
        have hw : |(337795009/625000000 : ℝ)|=(337795009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s4_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654834841/5000000000 : ℝ)*x 0 + (1080944003/2000000000 : ℝ)*x 1 + (-2123169933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654834841/5000000000 : ℝ)^8271 ≤ (43110866014051/100000000000000 : ℝ)^6223 := by
    have hnat : (2654834841 : ℕ)^8271*100000000000000^6223 ≤ 43110866014051^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654834841 5000000000 43110866014051 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080944003/2000000000 : ℝ)^8271 ≤ (2206980043033/5000000000000 : ℝ)^6223 := by
    have hnat : (1080944003 : ℕ)^8271*5000000000000^6223 ≤ 2206980043033^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080944003 2000000000 2206980043033 5000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123169933/10000000000 : ℝ)^8271 ≤ (12749533110569/100000000000000 : ℝ)^6223 := by
    have hnat : (2123169933 : ℕ)^8271*100000000000000^6223 ≤ 12749533110569^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123169933 10000000000 12749533110569 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654834841/5000000000 : ℝ), (1080944003/2000000000 : ℝ), (-2123169933/10000000000 : ℝ)] ![(43110866014051/100000000000000 : ℝ), (2206980043033/5000000000000 : ℝ), (12749533110569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654834841/5000000000 : ℝ)|^8271 ≤ (43110866014051/100000000000000 : ℝ)^6223
        have hw : |(2654834841/5000000000 : ℝ)|=(2654834841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080944003/2000000000 : ℝ)|^8271 ≤ (2206980043033/5000000000000 : ℝ)^6223
        have hw : |(1080944003/2000000000 : ℝ)|=(1080944003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123169933/10000000000 : ℝ)|^8271 ≤ (12749533110569/100000000000000 : ℝ)^6223
        have hw : |(-2123169933/10000000000 : ℝ)|=(2123169933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s4_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373195671/10000000000 : ℝ)*x 0 + (2261507083/5000000000 : ℝ)*x 1 + (845683659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373195671/10000000000 : ℝ)^8271 ≤ (6662162302529/20000000000000 : ℝ)^6223 := by
    have hnat : (4373195671 : ℕ)^8271*20000000000000^6223 ≤ 6662162302529^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373195671 10000000000 6662162302529 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261507083/5000000000 : ℝ)^8271 ≤ (17418016494783/50000000000000 : ℝ)^6223 := by
    have hnat : (2261507083 : ℕ)^8271*50000000000000^6223 ≤ 17418016494783^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261507083 5000000000 17418016494783 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845683659/2000000000 : ℝ)^8271 ≤ (31853155487077/100000000000000 : ℝ)^6223 := by
    have hnat : (845683659 : ℕ)^8271*100000000000000^6223 ≤ 31853155487077^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845683659 2000000000 31853155487077 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373195671/10000000000 : ℝ), (2261507083/5000000000 : ℝ), (845683659/2000000000 : ℝ)] ![(6662162302529/20000000000000 : ℝ), (17418016494783/50000000000000 : ℝ), (31853155487077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373195671/10000000000 : ℝ)|^8271 ≤ (6662162302529/20000000000000 : ℝ)^6223
        have hw : |(4373195671/10000000000 : ℝ)|=(4373195671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261507083/5000000000 : ℝ)|^8271 ≤ (17418016494783/50000000000000 : ℝ)^6223
        have hw : |(2261507083/5000000000 : ℝ)|=(2261507083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845683659/2000000000 : ℝ)|^8271 ≤ (31853155487077/100000000000000 : ℝ)^6223
        have hw : |(845683659/2000000000 : ℝ)|=(845683659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14889/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11047/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14889/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2087/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14889/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2087/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14889/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2087/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14889/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2087/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14889/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2087/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14889/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2087/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2087/20000 : ℝ) ^ (4135/1024 : ℝ) ≤ (2175796000924431/20000000000000000000 : ℝ) := by
    have hpowers : (2087/20000 : ℝ)^4135 ≤ (2175796000924431/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2087 : ℕ)^4135*20000000000000000000^1024 ≤ 2175796000924431^1024*20000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2087 20000 2175796000924431 20000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2087/20000 : ℝ)) (X := (2175796000924431/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14889/100000 : ℝ) ^ (4135/1024 : ℝ) ≤ (45704601633653191/100000000000000000000 : ℝ) := by
    have hpowers : (14889/100000 : ℝ)^4135 ≤ (45704601633653191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14889 : ℕ)^4135*100000000000000000000^1024 ≤ 45704601633653191^1024*100000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14889 100000 45704601633653191 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14889/100000 : ℝ)) (X := (45704601633653191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002175796000924431/10000000000000000000 : ℝ) ≤ (2500134693637703/2500000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (10002175796000924431/10000000000000000000 : ℝ)^1024 ≤ (2500134693637703/2500000000000000 : ℝ)^4135 := by
      have hnat : (10002175796000924431 : ℕ)^1024*2500000000000000^4135 ≤ 2500134693637703^4135*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002175796000924431 10000000000000000000 2500134693637703 2500000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134693637703/2500000000000000 : ℝ)) (X := (10002175796000924431/10000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028291790819137673/50000000000000000000 : ℝ) ≤ (2500350237354807/2500000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50028291790819137673/50000000000000000000 : ℝ)^1024 ≤ (2500350237354807/2500000000000000 : ℝ)^4135 := by
      have hnat : (50028291790819137673 : ℕ)^1024*2500000000000000^4135 ≤ 2500350237354807^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028291790819137673 50000000000000000000 2500350237354807 2500000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500350237354807/2500000000000000 : ℝ)) (X := (50028291790819137673/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045704601633653191/50000000000000000000 : ℝ) ≤ (2500565781071911/2500000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50045704601633653191/50000000000000000000 : ℝ)^1024 ≤ (2500565781071911/2500000000000000 : ℝ)^4135 := by
      have hnat : (50045704601633653191 : ℕ)^1024*2500000000000000^4135 ≤ 2500565781071911^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045704601633653191 50000000000000000000 2500565781071911 2500000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500565781071911/2500000000000000 : ℝ)) (X := (50045704601633653191/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2175796000924431/20000000000000000000 : ℝ) ≤ ((5565550764043184341/5567500000000000000 : ℝ)+2*(13471482319/6959375000000 : ℝ)*(2087/20000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (5565550764043184341/5567500000000000000 : ℝ)+2*(13471482319/6959375000000 : ℝ)*(2087/20000 : ℝ)=(2500134693637703/2500000000000000 : ℝ) by norm_num, show 1+2*(2175796000924431/20000000000000000000 : ℝ)=(10002175796000924431/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45704601633653191/100000000000000000000 : ℝ)+(2175796000924431/20000000000000000000 : ℝ) ≤ ((5565550764043184341/5567500000000000000 : ℝ)+(13471482319/6959375000000 : ℝ)*((14889/100000 : ℝ)+(2087/20000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (5565550764043184341/5567500000000000000 : ℝ)+(13471482319/6959375000000 : ℝ)*((14889/100000 : ℝ)+(2087/20000 : ℝ))=(2500350237354807/2500000000000000 : ℝ) by norm_num, show 1+(45704601633653191/100000000000000000000 : ℝ)+(2175796000924431/20000000000000000000 : ℝ)=(50028291790819137673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45704601633653191/100000000000000000000 : ℝ) ≤ ((5565550764043184341/5567500000000000000 : ℝ)+2*(13471482319/6959375000000 : ℝ)*(14889/100000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (5565550764043184341/5567500000000000000 : ℝ)+2*(13471482319/6959375000000 : ℝ)*(14889/100000 : ℝ)=(2500565781071911/2500000000000000 : ℝ) by norm_num, show 1+2*(45704601633653191/100000000000000000000 : ℝ)=(50045704601633653191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5565550764043184341/5567500000000000000 : ℝ)*(X 1 0+X 2 0)+(13471482319/6959375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (14889/100000 : ℝ)) (c := (5565550764043184341/5567500000000000000 : ℝ)) (alpha := (13471482319/6959375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5565550764043184341/5567500000000000000 : ℝ)*(X 0 1+X 2 1)+(13471482319/6959375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (14889/100000 : ℝ)) (c := (5565550764043184341/5567500000000000000 : ℝ)) (alpha := (13471482319/6959375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5565550764043184341/5567500000000000000 : ℝ)*(X 0 2+X 1 2)+(13471482319/6959375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (14889/100000 : ℝ)) (c := (5565550764043184341/5567500000000000000 : ℝ)) (alpha := (13471482319/6959375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2196857439/10000000000 : ℝ)*X 0 0+(337822627/625000000 : ℝ)*X 0 1+(5254322609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673848517/5000000000 : ℝ)*X 1 0+(-1136783903/5000000000 : ℝ)*X 1 1+(5254322471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347697167/10000000000 : ℝ)*X 2 0+(5254322499/10000000000 : ℝ)*X 2 1+(-1136783797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437318013/1000000000 : ℝ)*X 0 0+(4227550053/10000000000 : ℝ)*X 0 1+(4523878689/10000000000 : ℝ)*X 0 2+(437318013/1000000000 : ℝ)*X 1 0+(4227550053/10000000000 : ℝ)*X 1 1+(4523878689/10000000000 : ℝ)*X 1 2+(437318013/1000000000 : ℝ)*X 2 0+(4227550053/10000000000 : ℝ)*X 2 1+(4523878689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1098432831/5000000000 : ℝ)*X 0 0+(5254762539/10000000000 : ℝ)*X 0 1+(5404720053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654834899/5000000000 : ℝ)*X 1 0+(-2123169601/10000000000 : ℝ)*X 1 1+(337795009/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2654834841/5000000000 : ℝ)*X 2 0+(1080944003/2000000000 : ℝ)*X 2 1+(-2123169933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373195671/10000000000 : ℝ)*X 0 0+(2261507083/5000000000 : ℝ)*X 0 1+(845683659/2000000000 : ℝ)*X 0 2+(4373195671/10000000000 : ℝ)*X 1 0+(2261507083/5000000000 : ℝ)*X 1 1+(845683659/2000000000 : ℝ)*X 1 2+(4373195671/10000000000 : ℝ)*X 2 0+(2261507083/5000000000 : ℝ)*X 2 1+(845683659/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (751813682528419751749669059/69593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1786860443/100000000000000 : ℝ)*(base19) + (1242743807/100000000000000 : ℝ)*(base23) + (379151189/100000000000000 : ℝ)*(lower2) + (61737441/25000000000000 : ℝ)*(upper3) + (3163889/10000000000000 : ℝ)*(upper5) + (2501074464291633/50000000000000 : ℝ)*(major0) + (2501074464291633/50000000000000 : ℝ)*(major1) + (2501074464291633/50000000000000 : ℝ)*(major2) + (6629598663394439/100000000000000 : ℝ)*(sp0) + (3314815378303973/50000000000000 : ℝ)*(sp1) + (6629631300724583/100000000000000 : ℝ)*(sp2) + (674928866957613/20000000000000 : ℝ)*(sp3) + (33880073951/100000000000000 : ℝ)*(sp4) + (5154703427/25000000000000 : ℝ)*(sp7) + (1687332476800887/50000000000000 : ℝ)*(f.failure) + (6629632543468389/100000000000000 : ℝ)*(f.sum) + (17462528856603/11135000000000000000000000000 : ℝ)*base65 + (2099564533814231147/278375000000000000000000000000000 : ℝ)*base68 + (2478315654202106147/278375000000000000000000000000000 : ℝ)*base70 + (2573518034357231147/278375000000000000000000000000000 : ℝ)*base72 + (14958665299233/11135000000000000000000000000 : ℝ)*base73 + (85589412132393853/278375000000000000000000000000000 : ℝ)*base75 + (2248187907697106147/278375000000000000000000000000000 : ℝ)*base78 + (783416241384231147/278375000000000000000000000000000 : ℝ)*base80 + (31472395359023/11135000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (12987309/1000000000000000000000 : ℝ)*base89 + (12987309/1000000000000000000000 : ℝ)*base91 + (12987309/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25091711179479567572607/11135000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581556207/50000000000000 : ℝ)*(base19) + (140974611/12500000000000 : ℝ)*(base23) + (5505341/5000000000000 : ℝ)*(lower4) + (38044253/50000000000000 : ℝ)*(upper5) + (628939504344089/12500000000000 : ℝ)*(major0) + (628939504344089/12500000000000 : ℝ)*(major1) + (628939504344089/12500000000000 : ℝ)*(major2) + (236703807/50000000000000 : ℝ)*(sp0) + (1251445731/3125000000000 : ℝ)*(sp1) + (26502382427/100000000000000 : ℝ)*(sp2) + (6668554253636107/100000000000000 : ℝ)*(sp4) + (1333702703533583/20000000000000 : ℝ)*(sp5) + (3334263548432203/50000000000000 : ℝ)*(sp6) + (3394477267348057/100000000000000 : ℝ)*(sp7) + (3394477267348057/100000000000000 : ℝ)*(f.failure) + (6668554727043721/100000000000000 : ℝ)*(f.sum) + (46792716548051/11135000000000000000000000000 : ℝ)*base65 + (402637325395895901/69593750000000000000000000000000 : ℝ)*base68 + (7874031267135349/69593750000000000000000000000000 : ℝ)*base69 + (94575989654916599/69593750000000000000000000000000 : ℝ)*base71 + (30696892328229/11135000000000000000000000000 : ℝ)*base74 + (349400989252604099/69593750000000000000000000000000 : ℝ)*base75 + (293152553769489651/69593750000000000000000000000000 : ℝ)*base78 + (519812589650083401/69593750000000000000000000000000 : ℝ)*base80 + (10979611206931/11135000000000000000000000000 : ℝ)*base81 + (14381501/2000000000000000000000 : ℝ)*base90 + (14381501/2000000000000000000000 : ℝ)*base92 + (14381501/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1078_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14889/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1078_s5_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219765533/1000000000 : ℝ)*x 0 + (5396656203/10000000000 : ℝ)*x 1 + (2631152473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219765533/1000000000 : ℝ)^8271 ≤ (13347420637631/100000000000000 : ℝ)^6223 := by
    have hnat : (219765533 : ℕ)^8271*100000000000000^6223 ≤ 13347420637631^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219765533 1000000000 13347420637631 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396656203/10000000000 : ℝ)^8271 ≤ (22026046492311/50000000000000 : ℝ)^6223 := by
    have hnat : (5396656203 : ℕ)^8271*50000000000000^6223 ≤ 22026046492311^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396656203 10000000000 22026046492311 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631152473/5000000000 : ℝ)^8271 ≤ (42600486365017/100000000000000 : ℝ)^6223 := by
    have hnat : (2631152473 : ℕ)^8271*100000000000000^6223 ≤ 42600486365017^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631152473 5000000000 42600486365017 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219765533/1000000000 : ℝ), (5396656203/10000000000 : ℝ), (2631152473/5000000000 : ℝ)] ![(13347420637631/100000000000000 : ℝ), (22026046492311/50000000000000 : ℝ), (42600486365017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219765533/1000000000 : ℝ)|^8271 ≤ (13347420637631/100000000000000 : ℝ)^6223
        have hw : |(-219765533/1000000000 : ℝ)|=(219765533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396656203/10000000000 : ℝ)|^8271 ≤ (22026046492311/50000000000000 : ℝ)^6223
        have hw : |(5396656203/10000000000 : ℝ)|=(5396656203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631152473/5000000000 : ℝ)|^8271 ≤ (42600486365017/100000000000000 : ℝ)^6223
        have hw : |(2631152473/5000000000 : ℝ)|=(2631152473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s5_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345576399/10000000000 : ℝ)*x 0 + (-141615977/625000000 : ℝ)*x 1 + (5262303951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345576399/10000000000 : ℝ)^8271 ≤ (43498779999963/100000000000000 : ℝ)^6223 := by
    have hnat : (5345576399 : ℕ)^8271*100000000000000^6223 ≤ 43498779999963^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345576399 10000000000 43498779999963 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141615977/625000000 : ℝ)^8271 ≤ (3475186082289/25000000000000 : ℝ)^6223 := by
    have hnat : (141615977 : ℕ)^8271*25000000000000^6223 ≤ 3475186082289^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141615977 625000000 3475186082289 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262303951/10000000000 : ℝ)^8271 ≤ (42600475659199/100000000000000 : ℝ)^6223 := by
    have hnat : (5262303951 : ℕ)^8271*100000000000000^6223 ≤ 42600475659199^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262303951 10000000000 42600475659199 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345576399/10000000000 : ℝ), (-141615977/625000000 : ℝ), (5262303951/10000000000 : ℝ)] ![(43498779999963/100000000000000 : ℝ), (3475186082289/25000000000000 : ℝ), (42600475659199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345576399/10000000000 : ℝ)|^8271 ≤ (43498779999963/100000000000000 : ℝ)^6223
        have hw : |(5345576399/10000000000 : ℝ)|=(5345576399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141615977/625000000 : ℝ)|^8271 ≤ (3475186082289/25000000000000 : ℝ)^6223
        have hw : |(-141615977/625000000 : ℝ)|=(141615977/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262303951/10000000000 : ℝ)|^8271 ≤ (42600475659199/100000000000000 : ℝ)^6223
        have hw : |(5262303951/10000000000 : ℝ)|=(5262303951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s5_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672788063/5000000000 : ℝ)*x 0 + (526230491/1000000000 : ℝ)*x 1 + (-2265854729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672788063/5000000000 : ℝ)^8271 ≤ (43498777047371/100000000000000 : ℝ)^6223 := by
    have hnat : (2672788063 : ℕ)^8271*100000000000000^6223 ≤ 43498777047371^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672788063 5000000000 43498777047371 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526230491/1000000000 : ℝ)^8271 ≤ (42600485977671/100000000000000 : ℝ)^6223 := by
    have hnat : (526230491 : ℕ)^8271*100000000000000^6223 ≤ 42600485977671^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526230491 1000000000 42600485977671 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265854729/10000000000 : ℝ)^8271 ≤ (217199015097/1562500000000 : ℝ)^6223 := by
    have hnat : (2265854729 : ℕ)^8271*1562500000000^6223 ≤ 217199015097^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265854729 10000000000 217199015097 1562500000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672788063/5000000000 : ℝ), (526230491/1000000000 : ℝ), (-2265854729/10000000000 : ℝ)] ![(43498777047371/100000000000000 : ℝ), (42600485977671/100000000000000 : ℝ), (217199015097/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672788063/5000000000 : ℝ)|^8271 ≤ (43498777047371/100000000000000 : ℝ)^6223
        have hw : |(2672788063/5000000000 : ℝ)|=(2672788063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526230491/1000000000 : ℝ)|^8271 ≤ (42600485977671/100000000000000 : ℝ)^6223
        have hw : |(526230491/1000000000 : ℝ)|=(526230491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2265854729/10000000000 : ℝ)|^8271 ≤ (217199015097/1562500000000 : ℝ)^6223
        have hw : |(-2265854729/10000000000 : ℝ)|=(2265854729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s5_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186821227/5000000000 : ℝ)*x 0 + (530460577/1250000000 : ℝ)*x 1 + (90152463/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186821227/5000000000 : ℝ)^8271 ≤ (8328833685121/25000000000000 : ℝ)^6223 := by
    have hnat : (2186821227 : ℕ)^8271*25000000000000^6223 ≤ 8328833685121^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186821227 5000000000 8328833685121 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530460577/1250000000 : ℝ)^8271 ≤ (32006096814841/100000000000000 : ℝ)^6223 := by
    have hnat : (530460577 : ℕ)^8271*100000000000000^6223 ≤ 32006096814841^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530460577 1250000000 32006096814841 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90152463/200000000 : ℝ)^8271 ≤ (34678568429761/100000000000000 : ℝ)^6223 := by
    have hnat : (90152463 : ℕ)^8271*100000000000000^6223 ≤ 34678568429761^6223*200000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90152463 200000000 34678568429761 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186821227/5000000000 : ℝ), (530460577/1250000000 : ℝ), (90152463/200000000 : ℝ)] ![(8328833685121/25000000000000 : ℝ), (32006096814841/100000000000000 : ℝ), (34678568429761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186821227/5000000000 : ℝ)|^8271 ≤ (8328833685121/25000000000000 : ℝ)^6223
        have hw : |(2186821227/5000000000 : ℝ)|=(2186821227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530460577/1250000000 : ℝ)|^8271 ≤ (32006096814841/100000000000000 : ℝ)^6223
        have hw : |(530460577/1250000000 : ℝ)|=(530460577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90152463/200000000 : ℝ)|^8271 ≤ (34678568429761/100000000000000 : ℝ)^6223
        have hw : |(90152463/200000000 : ℝ)|=(90152463/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s5_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219766079/1000000000 : ℝ)*x 0 + (1052530803/2000000000 : ℝ)*x 1 + (1349076487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219766079/1000000000 : ℝ)^8271 ≤ (533898588491/4000000000000 : ℝ)^6223 := by
    have hnat : (219766079 : ℕ)^8271*4000000000000^6223 ≤ 533898588491^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219766079 1000000000 533898588491 4000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052530803/2000000000 : ℝ)^8271 ≤ (10651060563589/25000000000000 : ℝ)^6223 := by
    have hnat : (1052530803 : ℕ)^8271*25000000000000^6223 ≤ 10651060563589^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052530803 2000000000 10651060563589 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349076487/2500000000 : ℝ)^8271 ≤ (44048293018537/100000000000000 : ℝ)^6223 := by
    have hnat : (1349076487 : ℕ)^8271*100000000000000^6223 ≤ 44048293018537^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349076487 2500000000 44048293018537 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219766079/1000000000 : ℝ), (1052530803/2000000000 : ℝ), (1349076487/2500000000 : ℝ)] ![(533898588491/4000000000000 : ℝ), (10651060563589/25000000000000 : ℝ), (44048293018537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219766079/1000000000 : ℝ)|^8271 ≤ (533898588491/4000000000000 : ℝ)^6223
        have hw : |(-219766079/1000000000 : ℝ)|=(219766079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052530803/2000000000 : ℝ)|^8271 ≤ (10651060563589/25000000000000 : ℝ)^6223
        have hw : |(1052530803/2000000000 : ℝ)|=(1052530803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349076487/2500000000 : ℝ)|^8271 ≤ (44048293018537/100000000000000 : ℝ)^6223
        have hw : |(1349076487/2500000000 : ℝ)|=(1349076487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s5_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655852201/5000000000 : ℝ)*x 0 + (-1065926659/5000000000 : ℝ)*x 1 + (2698152911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655852201/5000000000 : ℝ)^8271 ≤ (21566412429673/50000000000000 : ℝ)^6223 := by
    have hnat : (2655852201 : ℕ)^8271*50000000000000^6223 ≤ 21566412429673^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655852201 5000000000 21566412429673 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065926659/5000000000 : ℝ)^8271 ≤ (6409441734553/50000000000000 : ℝ)^6223 := by
    have hnat : (1065926659 : ℕ)^8271*50000000000000^6223 ≤ 6409441734553^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065926659 5000000000 6409441734553 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698152911/5000000000 : ℝ)^8271 ≤ (44048291651559/100000000000000 : ℝ)^6223 := by
    have hnat : (2698152911 : ℕ)^8271*100000000000000^6223 ≤ 44048291651559^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698152911 5000000000 44048291651559 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655852201/5000000000 : ℝ), (-1065926659/5000000000 : ℝ), (2698152911/5000000000 : ℝ)] ![(21566412429673/50000000000000 : ℝ), (6409441734553/50000000000000 : ℝ), (44048291651559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655852201/5000000000 : ℝ)|^8271 ≤ (21566412429673/50000000000000 : ℝ)^6223
        have hw : |(2655852201/5000000000 : ℝ)|=(2655852201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065926659/5000000000 : ℝ)|^8271 ≤ (6409441734553/50000000000000 : ℝ)^6223
        have hw : |(-1065926659/5000000000 : ℝ)|=(1065926659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698152911/5000000000 : ℝ)|^8271 ≤ (44048291651559/100000000000000 : ℝ)^6223
        have hw : |(2698152911/5000000000 : ℝ)|=(2698152911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s5_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655852017/5000000000 : ℝ)*x 0 + (2698153103/5000000000 : ℝ)*x 1 + (-426370659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655852017/5000000000 : ℝ)^8271 ≤ (21566410443807/50000000000000 : ℝ)^6223 := by
    have hnat : (2655852017 : ℕ)^8271*50000000000000^6223 ≤ 21566410443807^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655852017 5000000000 21566410443807 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698153103/5000000000 : ℝ)^8271 ≤ (8809659163517/20000000000000 : ℝ)^6223 := by
    have hnat : (2698153103 : ℕ)^8271*20000000000000^6223 ≤ 8809659163517^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698153103 5000000000 8809659163517 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426370659/2000000000 : ℝ)^8271 ≤ (3204720821323/25000000000000 : ℝ)^6223 := by
    have hnat : (426370659 : ℕ)^8271*25000000000000^6223 ≤ 3204720821323^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426370659 2000000000 3204720821323 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655852017/5000000000 : ℝ), (2698153103/5000000000 : ℝ), (-426370659/2000000000 : ℝ)] ![(21566410443807/50000000000000 : ℝ), (8809659163517/20000000000000 : ℝ), (3204720821323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655852017/5000000000 : ℝ)|^8271 ≤ (21566410443807/50000000000000 : ℝ)^6223
        have hw : |(2655852017/5000000000 : ℝ)|=(2655852017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698153103/5000000000 : ℝ)|^8271 ≤ (8809659163517/20000000000000 : ℝ)^6223
        have hw : |(2698153103/5000000000 : ℝ)|=(2698153103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426370659/2000000000 : ℝ)|^8271 ≤ (3204720821323/25000000000000 : ℝ)^6223
        have hw : |(-426370659/2000000000 : ℝ)|=(426370659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s5_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373653749/10000000000 : ℝ)*x 0 + (2253468499/5000000000 : ℝ)*x 1 + (2122186543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373653749/10000000000 : ℝ)^8271 ≤ (4164431136619/12500000000000 : ℝ)^6223 := by
    have hnat : (4373653749 : ℕ)^8271*12500000000000^6223 ≤ 4164431136619^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373653749 10000000000 4164431136619 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253468499/5000000000 : ℝ)^8271 ≤ (17335776282289/50000000000000 : ℝ)^6223 := by
    have hnat : (2253468499 : ℕ)^8271*50000000000000^6223 ≤ 17335776282289^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253468499 5000000000 17335776282289 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122186543/5000000000 : ℝ)^8271 ≤ (8003249582507/25000000000000 : ℝ)^6223 := by
    have hnat : (2122186543 : ℕ)^8271*25000000000000^6223 ≤ 8003249582507^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122186543 5000000000 8003249582507 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373653749/10000000000 : ℝ), (2253468499/5000000000 : ℝ), (2122186543/5000000000 : ℝ)] ![(4164431136619/12500000000000 : ℝ), (17335776282289/50000000000000 : ℝ), (8003249582507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373653749/10000000000 : ℝ)|^8271 ≤ (4164431136619/12500000000000 : ℝ)^6223
        have hw : |(4373653749/10000000000 : ℝ)|=(4373653749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253468499/5000000000 : ℝ)|^8271 ≤ (17335776282289/50000000000000 : ℝ)^6223
        have hw : |(2253468499/5000000000 : ℝ)|=(2253468499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122186543/5000000000 : ℝ)|^8271 ≤ (8003249582507/25000000000000 : ℝ)^6223
        have hw : |(2122186543/5000000000 : ℝ)|=(2122186543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5609/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14063/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11047/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11047/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11047/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11047/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11047/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11047/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11047/100000 : ℝ) ^ (4135/1024 : ℝ) ≤ (13694257198320139/100000000000000000000 : ℝ) := by
    have hpowers : (11047/100000 : ℝ)^4135 ≤ (13694257198320139/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11047 : ℕ)^4135*100000000000000000000^1024 ≤ 13694257198320139^1024*100000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11047 100000 13694257198320139 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11047/100000 : ℝ)) (X := (13694257198320139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14241/100000 : ℝ) ^ (4135/1024 : ℝ) ≤ (19093860529857721/50000000000000000000 : ℝ) := by
    have hpowers : (14241/100000 : ℝ)^4135 ≤ (19093860529857721/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14241 : ℕ)^4135*50000000000000000000^1024 ≤ 19093860529857721^1024*100000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14241 100000 19093860529857721 50000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14241/100000 : ℝ)) (X := (19093860529857721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013694257198320139/50000000000000000000 : ℝ) ≤ (2000135636999499/2000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50013694257198320139/50000000000000000000 : ℝ)^1024 ≤ (2000135636999499/2000000000000000 : ℝ)^4135 := by
      have hnat : (50013694257198320139 : ℕ)^1024*2000000000000000^4135 ≤ 2000135636999499^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013694257198320139 50000000000000000000 2000135636999499 2000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000135636999499/2000000000000000 : ℝ)) (X := (50013694257198320139/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051881978258035581/100000000000000000000 : ℝ) ≤ (10001284565419611/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (100051881978258035581/100000000000000000000 : ℝ)^1024 ≤ (10001284565419611/10000000000000000 : ℝ)^4135 := by
      have hnat : (100051881978258035581 : ℕ)^1024*10000000000000000^4135 ≤ 10001284565419611^4135*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051881978258035581 100000000000000000000 10001284565419611 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001284565419611/10000000000000000 : ℝ)) (X := (100051881978258035581/100000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019093860529857721/25000000000000000000 : ℝ) ≤ (10001890945841727/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (25019093860529857721/25000000000000000000 : ℝ)^1024 ≤ (10001890945841727/10000000000000000 : ℝ)^4135 := by
      have hnat : (25019093860529857721 : ℕ)^1024*10000000000000000^4135 ≤ 10001890945841727^4135*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019093860529857721 25000000000000000000 10001890945841727 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001890945841727/10000000000000000 : ℝ)) (X := (25019093860529857721/25000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13694257198320139/100000000000000000000 : ℝ) ≤ ((15964384376917884063/15970000000000000000 : ℝ)+2*(151595105529/79850000000000 : ℝ)*(11047/100000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (15964384376917884063/15970000000000000000 : ℝ)+2*(151595105529/79850000000000 : ℝ)*(11047/100000 : ℝ)=(2000135636999499/2000000000000000 : ℝ) by norm_num, show 1+2*(13694257198320139/100000000000000000000 : ℝ)=(50013694257198320139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19093860529857721/50000000000000000000 : ℝ)+(13694257198320139/100000000000000000000 : ℝ) ≤ ((15964384376917884063/15970000000000000000 : ℝ)+(151595105529/79850000000000 : ℝ)*((14241/100000 : ℝ)+(11047/100000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (15964384376917884063/15970000000000000000 : ℝ)+(151595105529/79850000000000 : ℝ)*((14241/100000 : ℝ)+(11047/100000 : ℝ))=(10001284565419611/10000000000000000 : ℝ) by norm_num, show 1+(19093860529857721/50000000000000000000 : ℝ)+(13694257198320139/100000000000000000000 : ℝ)=(100051881978258035581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19093860529857721/50000000000000000000 : ℝ) ≤ ((15964384376917884063/15970000000000000000 : ℝ)+2*(151595105529/79850000000000 : ℝ)*(14241/100000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (15964384376917884063/15970000000000000000 : ℝ)+2*(151595105529/79850000000000 : ℝ)*(14241/100000 : ℝ)=(10001890945841727/10000000000000000 : ℝ) by norm_num, show 1+2*(19093860529857721/50000000000000000000 : ℝ)=(25019093860529857721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15964384376917884063/15970000000000000000 : ℝ)*(X 1 0+X 2 0)+(151595105529/79850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11047/100000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (15964384376917884063/15970000000000000000 : ℝ)) (alpha := (151595105529/79850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15964384376917884063/15970000000000000000 : ℝ)*(X 0 1+X 2 1)+(151595105529/79850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11047/100000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (15964384376917884063/15970000000000000000 : ℝ)) (alpha := (151595105529/79850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15964384376917884063/15970000000000000000 : ℝ)*(X 0 2+X 1 2)+(151595105529/79850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11047/100000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (15964384376917884063/15970000000000000000 : ℝ)) (alpha := (151595105529/79850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-219765533/1000000000 : ℝ)*X 0 0+(5396656203/10000000000 : ℝ)*X 0 1+(2631152473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345576399/10000000000 : ℝ)*X 1 0+(-141615977/625000000 : ℝ)*X 1 1+(5262303951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672788063/5000000000 : ℝ)*X 2 0+(526230491/1000000000 : ℝ)*X 2 1+(-2265854729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186821227/5000000000 : ℝ)*X 0 0+(530460577/1250000000 : ℝ)*X 0 1+(90152463/200000000 : ℝ)*X 0 2+(2186821227/5000000000 : ℝ)*X 1 0+(530460577/1250000000 : ℝ)*X 1 1+(90152463/200000000 : ℝ)*X 1 2+(2186821227/5000000000 : ℝ)*X 2 0+(530460577/1250000000 : ℝ)*X 2 1+(90152463/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219766079/1000000000 : ℝ)*X 0 0+(1052530803/2000000000 : ℝ)*X 0 1+(1349076487/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655852201/5000000000 : ℝ)*X 1 0+(-1065926659/5000000000 : ℝ)*X 1 1+(2698152911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655852017/5000000000 : ℝ)*X 2 0+(2698153103/5000000000 : ℝ)*X 2 1+(-426370659/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373653749/10000000000 : ℝ)*X 0 0+(2253468499/5000000000 : ℝ)*X 0 1+(2122186543/5000000000 : ℝ)*X 0 2+(4373653749/10000000000 : ℝ)*X 1 0+(2253468499/5000000000 : ℝ)*X 1 1+(2122186543/5000000000 : ℝ)*X 1 2+(4373653749/10000000000 : ℝ)*X 2 0+(2253468499/5000000000 : ℝ)*X 2 1+(2122186543/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3924017662459762740638073/1996250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (580456913/100000000000000 : ℝ)*(base19) + (58302787/50000000000000 : ℝ)*(base23) + (83876351/50000000000000 : ℝ)*(upper4) + (26066229/20000000000000 : ℝ)*(upper5) + (28079867832257/500000000000 : ℝ)*(major0) + (28079867832257/500000000000 : ℝ)*(major1) + (28079867832257/500000000000 : ℝ)*(major2) + (1488633605607693/20000000000000 : ℝ)*(sp0) + (1860783175591371/25000000000000 : ℝ)*(sp1) + (1488633895640771/20000000000000 : ℝ)*(sp2) + (378877011700603/10000000000000 : ℝ)*(sp3) + (1566770963/100000000000000 : ℝ)*(sp4) + (4538998379/12500000000000 : ℝ)*(sp5) + (7355564181/100000000000000 : ℝ)*(sp7) + (947194368142553/25000000000000 : ℝ)*(f.failure) + (7443169594809429/100000000000000 : ℝ)*(f.sum) + (10157279724747/1597000000000000000000000000 : ℝ)*base65 + (41094986953590191/7985000000000000000000000000000 : ℝ)*base67 + (6338667248579809/7985000000000000000000000000000 : ℝ)*base70 + (81249356166244809/7985000000000000000000000000000 : ℝ)*base72 + (7520555002501/798500000000000000000000000 : ℝ)*base73 + (44914136563969809/7985000000000000000000000000000 : ℝ)*base76 + (70591287584994809/7985000000000000000000000000000 : ℝ)*base78 + (79200740528259809/7985000000000000000000000000000 : ℝ)*base80 + (6409130622953/1597000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3448771/500000000000000000000 : ℝ)*base89 + (3448771/500000000000000000000 : ℝ)*base91 + (3448771/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4015098299080781328861/998125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1673022287/100000000000000 : ℝ)*(base19) + (53043783/4000000000000 : ℝ)*(base23) + (46249497/25000000000000 : ℝ)*(upper3) + (31467827/50000000000000 : ℝ)*(lower4) + (5645351991391557/100000000000000 : ℝ)*(major0) + (5645351991391557/100000000000000 : ℝ)*(major1) + (5645351991391557/100000000000000 : ℝ)*(major2) + (36636486101/100000000000000 : ℝ)*(sp1) + (2808786561/6250000000000 : ℝ)*(sp2) + (65270589/50000000000000 : ℝ)*(sp3) + (1870526606562179/25000000000000 : ℝ)*(sp4) + (935258514592541/12500000000000 : ℝ)*(sp5) + (1870515039892291/25000000000000 : ℝ)*(sp6) + (1904298645952593/50000000000000 : ℝ)*(sp7) + (952149355611591/25000000000000 : ℝ)*(f.failure) + (1870526606562179/25000000000000 : ℝ)*(f.sum) + (3700286284601/1996250000000000000000000000 : ℝ)*base66 + (4681356905541656091/1597000000000000000000000000000000 : ℝ)*base67 + (11441114190914343909/1597000000000000000000000000000000 : ℝ)*base70 + (5959906468663343909/1597000000000000000000000000000000 : ℝ)*base72 + (4431430134703/3992500000000000000000000000 : ℝ)*base73 + (7372644706382656091/1597000000000000000000000000000000 : ℝ)*base75 + (3023160405327656091/1597000000000000000000000000000000 : ℝ)*base77 + (76462962413246343909/1597000000000000000000000000000000 : ℝ)*base80 + (10982565020757/3992500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2953437/500000000000000000000 : ℝ)*base89 + (2953437/500000000000000000000 : ℝ)*base91 + (2953437/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1078_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1078_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (877/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1078_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1078_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1078_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (877/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1078_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

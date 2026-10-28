-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1222_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:11:29.427214+00:00
-- url     : https://prove2.me/submissions/65e0e4ec-7de6-49ed-8819-fce2bf8b0fdf

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
theorem support_rectangle_w1222_s0_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-93337347/500000000 : ℝ)*x 0 + (241440973/400000000 : ℝ)*x 1 + (598813247/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93337347/500000000 : ℝ)^8415 ≤ (5439936787681/50000000000000 : ℝ)^6367 := by
    have hnat : (93337347 : ℕ)^8415*50000000000000^6367 ≤ 5439936787681^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93337347 500000000 5439936787681 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241440973/400000000 : ℝ)^8415 ≤ (2565651495443/5000000000000 : ℝ)^6367 := by
    have hnat : (241440973 : ℕ)^8415*5000000000000^6367 ≤ 2565651495443^6367*400000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241440973 400000000 2565651495443 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598813247/1250000000 : ℝ)^8415 ≤ (1512283860041/4000000000000 : ℝ)^6367 := by
    have hnat : (598813247 : ℕ)^8415*4000000000000^6367 ≤ 1512283860041^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598813247 1250000000 1512283860041 4000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93337347/500000000 : ℝ), (241440973/400000000 : ℝ), (598813247/1250000000 : ℝ)] ![(5439936787681/50000000000000 : ℝ), (2565651495443/5000000000000 : ℝ), (1512283860041/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93337347/500000000 : ℝ)|^8415 ≤ (5439936787681/50000000000000 : ℝ)^6367
        have hw : |(-93337347/500000000 : ℝ)|=(93337347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241440973/400000000 : ℝ)|^8415 ≤ (2565651495443/5000000000000 : ℝ)^6367
        have hw : |(241440973/400000000 : ℝ)|=(241440973/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598813247/1250000000 : ℝ)|^8415 ≤ (1512283860041/4000000000000 : ℝ)^6367
        have hw : |(598813247/1250000000 : ℝ)|=(598813247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s0_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5512286269/10000000000 : ℝ)*x 0 + (-2579322547/10000000000 : ℝ)*x 1 + (958101187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512286269/10000000000 : ℝ)^8415 ≤ (45512313608159/100000000000000 : ℝ)^6367 := by
    have hnat : (5512286269 : ℕ)^8415*100000000000000^6367 ≤ 45512313608159^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512286269 10000000000 45512313608159 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2579322547/10000000000 : ℝ)^8415 ≤ (8340295149337/50000000000000 : ℝ)^6367 := by
    have hnat : (2579322547 : ℕ)^8415*50000000000000^6367 ≤ 8340295149337^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579322547 10000000000 8340295149337 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958101187/2000000000 : ℝ)^8415 ≤ (4725887009171/12500000000000 : ℝ)^6367 := by
    have hnat : (958101187 : ℕ)^8415*12500000000000^6367 ≤ 4725887009171^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958101187 2000000000 4725887009171 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512286269/10000000000 : ℝ), (-2579322547/10000000000 : ℝ), (958101187/2000000000 : ℝ)] ![(45512313608159/100000000000000 : ℝ), (8340295149337/50000000000000 : ℝ), (4725887009171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512286269/10000000000 : ℝ)|^8415 ≤ (45512313608159/100000000000000 : ℝ)^6367
        have hw : |(5512286269/10000000000 : ℝ)|=(5512286269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2579322547/10000000000 : ℝ)|^8415 ≤ (8340295149337/50000000000000 : ℝ)^6367
        have hw : |(-2579322547/10000000000 : ℝ)|=(2579322547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958101187/2000000000 : ℝ)|^8415 ≤ (4725887009171/12500000000000 : ℝ)^6367
        have hw : |(958101187/2000000000 : ℝ)|=(958101187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s0_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378071559/2500000000 : ℝ)*x 0 + (598813247/1250000000 : ℝ)*x 1 + (-2579322539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378071559/2500000000 : ℝ)^8415 ≤ (45512313248053/100000000000000 : ℝ)^6367 := by
    have hnat : (1378071559 : ℕ)^8415*100000000000000^6367 ≤ 45512313248053^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378071559 2500000000 45512313248053 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598813247/1250000000 : ℝ)^8415 ≤ (1512283860041/4000000000000 : ℝ)^6367 := by
    have hnat : (598813247 : ℕ)^8415*4000000000000^6367 ≤ 1512283860041^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598813247 1250000000 1512283860041 4000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579322539/10000000000 : ℝ)^8415 ≤ (2085073778787/12500000000000 : ℝ)^6367 := by
    have hnat : (2579322539 : ℕ)^8415*12500000000000^6367 ≤ 2085073778787^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579322539 10000000000 2085073778787 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378071559/2500000000 : ℝ), (598813247/1250000000 : ℝ), (-2579322539/10000000000 : ℝ)] ![(45512313248053/100000000000000 : ℝ), (1512283860041/4000000000000 : ℝ), (2085073778787/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378071559/2500000000 : ℝ)|^8415 ≤ (45512313248053/100000000000000 : ℝ)^6367
        have hw : |(1378071559/2500000000 : ℝ)|=(1378071559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598813247/1250000000 : ℝ)|^8415 ≤ (1512283860041/4000000000000 : ℝ)^6367
        have hw : |(598813247/1250000000 : ℝ)|=(598813247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2579322539/10000000000 : ℝ)|^8415 ≤ (2085073778787/12500000000000 : ℝ)^6367
        have hw : |(-2579322539/10000000000 : ℝ)|=(2579322539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s0_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048649217/2500000000 : ℝ)*x 0 + (3117658427/10000000000 : ℝ)*x 1 + (5634526527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048649217/2500000000 : ℝ)^8415 ≤ (15859712772781/50000000000000 : ℝ)^6367 := by
    have hnat : (1048649217 : ℕ)^8415*50000000000000^6367 ≤ 15859712772781^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048649217 2500000000 15859712772781 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117658427/10000000000 : ℝ)^8415 ≤ (21429604227951/100000000000000 : ℝ)^6367 := by
    have hnat : (3117658427 : ℕ)^8415*100000000000000^6367 ≤ 21429604227951^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117658427 10000000000 21429604227951 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5634526527/10000000000 : ℝ)^8415 ≤ (46850970211731/100000000000000 : ℝ)^6367 := by
    have hnat : (5634526527 : ℕ)^8415*100000000000000^6367 ≤ 46850970211731^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634526527 10000000000 46850970211731 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048649217/2500000000 : ℝ), (3117658427/10000000000 : ℝ), (5634526527/10000000000 : ℝ)] ![(15859712772781/50000000000000 : ℝ), (21429604227951/100000000000000 : ℝ), (46850970211731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048649217/2500000000 : ℝ)|^8415 ≤ (15859712772781/50000000000000 : ℝ)^6367
        have hw : |(1048649217/2500000000 : ℝ)|=(1048649217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117658427/10000000000 : ℝ)|^8415 ≤ (21429604227951/100000000000000 : ℝ)^6367
        have hw : |(3117658427/10000000000 : ℝ)|=(3117658427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5634526527/10000000000 : ℝ)|^8415 ≤ (46850970211731/100000000000000 : ℝ)^6367
        have hw : |(5634526527/10000000000 : ℝ)|=(5634526527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s0_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1871661663/10000000000 : ℝ)*x 0 + (4822593439/10000000000 : ℝ)*x 1 + (6002803313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871661663/10000000000 : ℝ)^8415 ≤ (10917747513069/100000000000000 : ℝ)^6367 := by
    have hnat : (1871661663 : ℕ)^8415*100000000000000^6367 ≤ 10917747513069^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871661663 10000000000 10917747513069 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4822593439/10000000000 : ℝ)^8415 ≤ (38142149477029/100000000000000 : ℝ)^6367 := by
    have hnat : (4822593439 : ℕ)^8415*100000000000000^6367 ≤ 38142149477029^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822593439 10000000000 38142149477029 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6002803313/10000000000 : ℝ)^8415 ≤ (1273502574777/2500000000000 : ℝ)^6367 := by
    have hnat : (6002803313 : ℕ)^8415*2500000000000^6367 ≤ 1273502574777^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002803313 10000000000 1273502574777 2500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1871661663/10000000000 : ℝ), (4822593439/10000000000 : ℝ), (6002803313/10000000000 : ℝ)] ![(10917747513069/100000000000000 : ℝ), (38142149477029/100000000000000 : ℝ), (1273502574777/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1871661663/10000000000 : ℝ)|^8415 ≤ (10917747513069/100000000000000 : ℝ)^6367
        have hw : |(-1871661663/10000000000 : ℝ)|=(1871661663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4822593439/10000000000 : ℝ)|^8415 ≤ (38142149477029/100000000000000 : ℝ)^6367
        have hw : |(4822593439/10000000000 : ℝ)|=(4822593439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6002803313/10000000000 : ℝ)|^8415 ≤ (1273502574777/2500000000000 : ℝ)^6367
        have hw : |(6002803313/10000000000 : ℝ)|=(6002803313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s0_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646685551/1250000000 : ℝ)*x 0 + (-1367023339/10000000000 : ℝ)*x 1 + (750350651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646685551/1250000000 : ℝ)^8415 ≤ (20926136294749/50000000000000 : ℝ)^6367 := by
    have hnat : (646685551 : ℕ)^8415*50000000000000^6367 ≤ 20926136294749^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646685551 1250000000 20926136294749 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367023339/10000000000 : ℝ)^8415 ≤ (3603801572973/50000000000000 : ℝ)^6367 := by
    have hnat : (1367023339 : ℕ)^8415*50000000000000^6367 ≤ 3603801572973^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367023339 10000000000 3603801572973 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750350651/1250000000 : ℝ)^8415 ≤ (12735031061191/25000000000000 : ℝ)^6367 := by
    have hnat : (750350651 : ℕ)^8415*25000000000000^6367 ≤ 12735031061191^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750350651 1250000000 12735031061191 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646685551/1250000000 : ℝ), (-1367023339/10000000000 : ℝ), (750350651/1250000000 : ℝ)] ![(20926136294749/50000000000000 : ℝ), (3603801572973/50000000000000 : ℝ), (12735031061191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646685551/1250000000 : ℝ)|^8415 ≤ (20926136294749/50000000000000 : ℝ)^6367
        have hw : |(646685551/1250000000 : ℝ)|=(646685551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367023339/10000000000 : ℝ)|^8415 ≤ (3603801572973/50000000000000 : ℝ)^6367
        have hw : |(-1367023339/10000000000 : ℝ)|=(1367023339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750350651/1250000000 : ℝ)|^8415 ≤ (12735031061191/25000000000000 : ℝ)^6367
        have hw : |(750350651/1250000000 : ℝ)|=(750350651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s0_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586742689/5000000000 : ℝ)*x 0 + (6002803751/10000000000 : ℝ)*x 1 + (-1367024197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586742689/5000000000 : ℝ)^8415 ≤ (5231535370081/12500000000000 : ℝ)^6367 := by
    have hnat : (2586742689 : ℕ)^8415*12500000000000^6367 ≤ 5231535370081^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586742689 5000000000 5231535370081 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6002803751/10000000000 : ℝ)^8415 ≤ (50940107903541/100000000000000 : ℝ)^6367 := by
    have hnat : (6002803751 : ℕ)^8415*100000000000000^6367 ≤ 50940107903541^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002803751 10000000000 50940107903541 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367024197/10000000000 : ℝ)^8415 ≤ (144152182497/2000000000000 : ℝ)^6367 := by
    have hnat : (1367024197 : ℕ)^8415*2000000000000^6367 ≤ 144152182497^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367024197 10000000000 144152182497 2000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586742689/5000000000 : ℝ), (6002803751/10000000000 : ℝ), (-1367024197/10000000000 : ℝ)] ![(5231535370081/12500000000000 : ℝ), (50940107903541/100000000000000 : ℝ), (144152182497/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586742689/5000000000 : ℝ)|^8415 ≤ (5231535370081/12500000000000 : ℝ)^6367
        have hw : |(2586742689/5000000000 : ℝ)|=(2586742689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6002803751/10000000000 : ℝ)|^8415 ≤ (50940107903541/100000000000000 : ℝ)^6367
        have hw : |(6002803751/10000000000 : ℝ)|=(6002803751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1367024197/10000000000 : ℝ)|^8415 ≤ (144152182497/2000000000000 : ℝ)^6367
        have hw : |(-1367024197/10000000000 : ℝ)|=(1367024197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s0_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1051131869/2500000000 : ℝ)*x 0 + (1113938109/2000000000 : ℝ)*x 1 + (127391361/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051131869/2500000000 : ℝ)^8415 ≤ (31818713242373/100000000000000 : ℝ)^6367 := by
    have hnat : (1051131869 : ℕ)^8415*100000000000000^6367 ≤ 31818713242373^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051131869 2500000000 31818713242373 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113938109/2000000000 : ℝ)^8415 ≤ (46139773158533/100000000000000 : ℝ)^6367 := by
    have hnat : (1113938109 : ℕ)^8415*100000000000000^6367 ≤ 46139773158533^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113938109 2000000000 46139773158533 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127391361/400000000 : ℝ)^8415 ≤ (551037839599/2500000000000 : ℝ)^6367 := by
    have hnat : (127391361 : ℕ)^8415*2500000000000^6367 ≤ 551037839599^6367*400000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127391361 400000000 551037839599 2500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051131869/2500000000 : ℝ), (1113938109/2000000000 : ℝ), (127391361/400000000 : ℝ)] ![(31818713242373/100000000000000 : ℝ), (46139773158533/100000000000000 : ℝ), (551037839599/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051131869/2500000000 : ℝ)|^8415 ≤ (31818713242373/100000000000000 : ℝ)^6367
        have hw : |(1051131869/2500000000 : ℝ)|=(1051131869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1113938109/2000000000 : ℝ)|^8415 ≤ (46139773158533/100000000000000 : ℝ)^6367
        have hw : |(1113938109/2000000000 : ℝ)|=(1113938109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127391361/400000000 : ℝ)|^8415 ≤ (551037839599/2500000000000 : ℝ)^6367
        have hw : |(127391361/400000000 : ℝ)|=(127391361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (369/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27511/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4207/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4207 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4207*1^1024 ≤ 0^1024*1^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4207/1024 : ℝ) ≤ (579487268491837327/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4207 ≤ (579487268491837327/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4207*25000000000000000000^1024 ≤ 579487268491837327^1024*5^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 579487268491837327 25000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (579487268491837327/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4207 := by
      have hnat : (1 : ℕ)^1024*1^4207 ≤ 1^4207*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25579487268491837327/25000000000000000000 : ℝ) ≤ (10055931651006763/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (25579487268491837327/25000000000000000000 : ℝ)^1024 ≤ (10055931651006763/10000000000000000 : ℝ)^4207 := by
      have hnat : (25579487268491837327 : ℕ)^1024*10000000000000000^4207 ≤ 10055931651006763^4207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25579487268491837327 25000000000000000000 10055931651006763 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055931651006763/10000000000000000 : ℝ)) (X := (25579487268491837327/25000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13079487268491837327/12500000000000000000 : ℝ) ≤ (5055931651006763/5000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (13079487268491837327/12500000000000000000 : ℝ)^1024 ≤ (5055931651006763/5000000000000000 : ℝ)^4207 := by
      have hnat : (13079487268491837327 : ℕ)^1024*5000000000000000^4207 ≤ 5055931651006763^4207*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13079487268491837327 12500000000000000000 5055931651006763 5000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055931651006763/5000000000000000 : ℝ)) (X := (13079487268491837327/12500000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55931651006763/4000000000000000 : ℝ)*(0 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(55931651006763/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(579487268491837327/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55931651006763/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (1 : ℝ)+(55931651006763/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055931651006763/10000000000000000 : ℝ) by norm_num, show 1+(579487268491837327/25000000000000000000 : ℝ)+(0 : ℝ)=(25579487268491837327/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(579487268491837327/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55931651006763/4000000000000000 : ℝ)*(2/5 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(55931651006763/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055931651006763/5000000000000000 : ℝ) by norm_num, show 1+2*(579487268491837327/25000000000000000000 : ℝ)=(13079487268491837327/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55931651006763/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55931651006763/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55931651006763/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55931651006763/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55931651006763/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55931651006763/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-93337347/500000000 : ℝ)*X 0 0+(241440973/400000000 : ℝ)*X 0 1+(598813247/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512286269/10000000000 : ℝ)*X 1 0+(-2579322547/10000000000 : ℝ)*X 1 1+(958101187/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378071559/2500000000 : ℝ)*X 2 0+(598813247/1250000000 : ℝ)*X 2 1+(-2579322539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048649217/2500000000 : ℝ)*X 0 0+(3117658427/10000000000 : ℝ)*X 0 1+(5634526527/10000000000 : ℝ)*X 0 2+(1048649217/2500000000 : ℝ)*X 1 0+(3117658427/10000000000 : ℝ)*X 1 1+(5634526527/10000000000 : ℝ)*X 1 2+(1048649217/2500000000 : ℝ)*X 2 0+(3117658427/10000000000 : ℝ)*X 2 1+(5634526527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1871661663/10000000000 : ℝ)*X 0 0+(4822593439/10000000000 : ℝ)*X 0 1+(6002803313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646685551/1250000000 : ℝ)*X 1 0+(-1367023339/10000000000 : ℝ)*X 1 1+(750350651/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586742689/5000000000 : ℝ)*X 2 0+(6002803751/10000000000 : ℝ)*X 2 1+(-1367024197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1051131869/2500000000 : ℝ)*X 0 0+(1113938109/2000000000 : ℝ)*X 0 1+(127391361/400000000 : ℝ)*X 0 2+(1051131869/2500000000 : ℝ)*X 1 0+(1113938109/2000000000 : ℝ)*X 1 1+(127391361/400000000 : ℝ)*X 1 2+(1051131869/2500000000 : ℝ)*X 2 0+(1113938109/2000000000 : ℝ)*X 2 1+(127391361/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164254770509596017343743/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75740263/100000000000000 : ℝ)*(base1) + (1604853041/100000000000000 : ℝ)*(base19) + (745218273/50000000000000 : ℝ)*(base23) + (109609917/100000000000000 : ℝ)*(base24) + (182524541/50000000000000 : ℝ)*(upper3) + (150026425442487/25000000000000 : ℝ)*(major0) + (150026425442487/25000000000000 : ℝ)*(major1) + (150026425442487/25000000000000 : ℝ)*(major2) + (802884006575787/100000000000000 : ℝ)*(sp0) + (802885884704321/100000000000000 : ℝ)*(sp1) + (802885889510899/100000000000000 : ℝ)*(sp2) + (99330206538989/25000000000000 : ℝ)*(sp3) + (1779360919/50000000000000 : ℝ)*(sp4) + (2793079953/100000000000000 : ℝ)*(sp7) + (99330923744043/25000000000000 : ℝ)*(f.failure) + (401443744778681/50000000000000 : ℝ)*(f.sum) + (10058498560419/50000000000000000000000000000 : ℝ)*base66 + (2391220860419/100000000000000000000000000000 : ℝ)*base68 + (117373499760419/100000000000000000000000000000 : ℝ)*base70 + (302198973960419/100000000000000000000000000000 : ℝ)*base72 + (16713304039581/50000000000000000000000000000 : ℝ)*base73 + (346787227339581/100000000000000000000000000000 : ℝ)*base75 + (257840755460419/100000000000000000000000000000 : ℝ)*base78 + (5229502439581/100000000000000000000000000000 : ℝ)*base79 + (113145849260419/50000000000000000000000000000 : ℝ)*base82 + (111027/1250000000000000000000 : ℝ)*base89 + (111027/1250000000000000000000 : ℝ)*base91 + (111027/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (286172023668019755073611/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (880969099/100000000000000 : ℝ)*(base19) + (549817297/50000000000000 : ℝ)*(base23) + (2526259/5000000000000 : ℝ)*(base39) + (243435387/100000000000000 : ℝ)*(upper3) + (633304874914901/100000000000000 : ℝ)*(major0) + (633304874914901/100000000000000 : ℝ)*(major1) + (316652412194861/50000000000000 : ℝ)*(major2) + (555286639/25000000000000 : ℝ)*(sp1) + (238364173/10000000000000 : ℝ)*(sp2) + (8908213/12500000000000 : ℝ)*(sp3) + (211826271096089/25000000000000 : ℝ)*(sp4) + (847301982268701/100000000000000 : ℝ)*(sp5) + (211825412908303/25000000000000 : ℝ)*(sp6) + (209652224131939/50000000000000 : ℝ)*(sp7) + (209652259764791/50000000000000 : ℝ)*(f.failure) + (169461026981907/20000000000000 : ℝ)*(f.sum) + (1093165781365349/400000000000000000000000000000 : ℝ)*base65 + (208923095555057/200000000000000000000000000000 : ℝ)*base68 + (4316520446075463/400000000000000000000000000000 : ℝ)*base69 + (72066929555057/200000000000000000000000000000 : ℝ)*base72 + (1167754831365349/400000000000000000000000000000 : ℝ)*base73 + (2604987150075463/400000000000000000000000000000 : ℝ)*base75 + (573271165924537/400000000000000000000000000000 : ℝ)*base78 + (2090130523524537/400000000000000000000000000000 : ℝ)*base80 + (1372401455675463/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13279201/2500000000000000000000 : ℝ)*base90 + (13279201/2500000000000000000000 : ℝ)*base92 + (38279201/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1222_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (369/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27511/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1222_s1_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1032807407/5000000000 : ℝ)*x 0 + (1420162939/2500000000 : ℝ)*x 1 + (627322529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032807407/5000000000 : ℝ)^8415 ≤ (497495427331/4000000000000 : ℝ)^6367 := by
    have hnat : (1032807407 : ℕ)^8415*4000000000000^6367 ≤ 497495427331^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032807407 5000000000 497495427331 4000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1420162939/2500000000 : ℝ)^8415 ≤ (47358532468173/100000000000000 : ℝ)^6367 := by
    have hnat : (1420162939 : ℕ)^8415*100000000000000^6367 ≤ 47358532468173^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420162939 2500000000 47358532468173 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627322529/1250000000 : ℝ)^8415 ≤ (40204081837873/100000000000000 : ℝ)^6367 := by
    have hnat : (627322529 : ℕ)^8415*100000000000000^6367 ≤ 40204081837873^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627322529 1250000000 40204081837873 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1032807407/5000000000 : ℝ), (1420162939/2500000000 : ℝ), (627322529/1250000000 : ℝ)] ![(497495427331/4000000000000 : ℝ), (47358532468173/100000000000000 : ℝ), (40204081837873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1032807407/5000000000 : ℝ)|^8415 ≤ (497495427331/4000000000000 : ℝ)^6367
        have hw : |(-1032807407/5000000000 : ℝ)|=(1032807407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1420162939/2500000000 : ℝ)|^8415 ≤ (47358532468173/100000000000000 : ℝ)^6367
        have hw : |(1420162939/2500000000 : ℝ)|=(1420162939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627322529/1250000000 : ℝ)|^8415 ≤ (40204081837873/100000000000000 : ℝ)^6367
        have hw : |(627322529/1250000000 : ℝ)|=(627322529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s1_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5414744543/10000000000 : ℝ)*x 0 + (-2421483169/10000000000 : ℝ)*x 1 + (501858023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414744543/10000000000 : ℝ)^8415 ≤ (44450950159909/100000000000000 : ℝ)^6367 := by
    have hnat : (5414744543 : ℕ)^8415*100000000000000^6367 ≤ 44450950159909^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414744543 10000000000 44450950159909 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2421483169/10000000000 : ℝ)^8415 ≤ (15344968009887/100000000000000 : ℝ)^6367 := by
    have hnat : (2421483169 : ℕ)^8415*100000000000000^6367 ≤ 15344968009887^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421483169 10000000000 15344968009887 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501858023/1000000000 : ℝ)^8415 ≤ (40204081816697/100000000000000 : ℝ)^6367 := by
    have hnat : (501858023 : ℕ)^8415*100000000000000^6367 ≤ 40204081816697^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501858023 1000000000 40204081816697 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414744543/10000000000 : ℝ), (-2421483169/10000000000 : ℝ), (501858023/1000000000 : ℝ)] ![(44450950159909/100000000000000 : ℝ), (15344968009887/100000000000000 : ℝ), (40204081816697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414744543/10000000000 : ℝ)|^8415 ≤ (44450950159909/100000000000000 : ℝ)^6367
        have hw : |(5414744543/10000000000 : ℝ)|=(5414744543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2421483169/10000000000 : ℝ)|^8415 ≤ (15344968009887/100000000000000 : ℝ)^6367
        have hw : |(-2421483169/10000000000 : ℝ)|=(2421483169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501858023/1000000000 : ℝ)|^8415 ≤ (40204081816697/100000000000000 : ℝ)^6367
        have hw : |(501858023/1000000000 : ℝ)|=(501858023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s1_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5414744557/10000000000 : ℝ)*x 0 + (2509290119/5000000000 : ℝ)*x 1 + (-2421483139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414744557/10000000000 : ℝ)^8415 ≤ (44450950311807/100000000000000 : ℝ)^6367 := by
    have hnat : (5414744557 : ℕ)^8415*100000000000000^6367 ≤ 44450950311807^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414744557 10000000000 44450950311807 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509290119/5000000000 : ℝ)^8415 ≤ (201020409507/500000000000 : ℝ)^6367 := by
    have hnat : (2509290119 : ℕ)^8415*500000000000^6367 ≤ 201020409507^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509290119 5000000000 201020409507 500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2421483139/10000000000 : ℝ)^8415 ≤ (7672483879313/50000000000000 : ℝ)^6367 := by
    have hnat : (2421483139 : ℕ)^8415*50000000000000^6367 ≤ 7672483879313^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421483139 10000000000 7672483879313 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414744557/10000000000 : ℝ), (2509290119/5000000000 : ℝ), (-2421483139/10000000000 : ℝ)] ![(44450950311807/100000000000000 : ℝ), (201020409507/500000000000 : ℝ), (7672483879313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414744557/10000000000 : ℝ)|^8415 ≤ (44450950311807/100000000000000 : ℝ)^6367
        have hw : |(5414744557/10000000000 : ℝ)|=(5414744557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509290119/5000000000 : ℝ)|^8415 ≤ (201020409507/500000000000 : ℝ)^6367
        have hw : |(2509290119/5000000000 : ℝ)|=(2509290119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2421483139/10000000000 : ℝ)|^8415 ≤ (7672483879313/50000000000000 : ℝ)^6367
        have hw : |(-2421483139/10000000000 : ℝ)|=(2421483139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s1_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (172423579/400000000 : ℝ)*x 0 + (738366421/2000000000 : ℝ)*x 1 + (2514853377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172423579/400000000 : ℝ)^8415 ≤ (1315352783393/4000000000000 : ℝ)^6367 := by
    have hnat : (172423579 : ℕ)^8415*4000000000000^6367 ≤ 1315352783393^6367*400000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172423579 400000000 1315352783393 4000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (738366421/2000000000 : ℝ)^8415 ≤ (26794250421813/100000000000000 : ℝ)^6367 := by
    have hnat : (738366421 : ℕ)^8415*100000000000000^6367 ≤ 26794250421813^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738366421 2000000000 26794250421813 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2514853377/5000000000 : ℝ)^8415 ≤ (20160964988473/50000000000000 : ℝ)^6367 := by
    have hnat : (2514853377 : ℕ)^8415*50000000000000^6367 ≤ 20160964988473^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514853377 5000000000 20160964988473 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172423579/400000000 : ℝ), (738366421/2000000000 : ℝ), (2514853377/5000000000 : ℝ)] ![(1315352783393/4000000000000 : ℝ), (26794250421813/100000000000000 : ℝ), (20160964988473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172423579/400000000 : ℝ)|^8415 ≤ (1315352783393/4000000000000 : ℝ)^6367
        have hw : |(172423579/400000000 : ℝ)|=(172423579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(738366421/2000000000 : ℝ)|^8415 ≤ (26794250421813/100000000000000 : ℝ)^6367
        have hw : |(738366421/2000000000 : ℝ)|=(738366421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2514853377/5000000000 : ℝ)|^8415 ≤ (20160964988473/50000000000000 : ℝ)^6367
        have hw : |(2514853377/5000000000 : ℝ)|=(2514853377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s1_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-41326227/200000000 : ℝ)*x 0 + (1256835663/2500000000 : ℝ)*x 1 + (283586201/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41326227/200000000 : ℝ)^8415 ≤ (2488585790957/20000000000000 : ℝ)^6367 := by
    have hnat : (41326227 : ℕ)^8415*20000000000000^6367 ≤ 2488585790957^6367*200000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41326227 200000000 2488585790957 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1256835663/2500000000 : ℝ)^8415 ≤ (8059376646417/20000000000000 : ℝ)^6367 := by
    have hnat : (1256835663 : ℕ)^8415*20000000000000^6367 ≤ 8059376646417^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256835663 2500000000 8059376646417 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283586201/500000000 : ℝ)^8415 ≤ (23630093896019/50000000000000 : ℝ)^6367 := by
    have hnat : (283586201 : ℕ)^8415*50000000000000^6367 ≤ 23630093896019^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283586201 500000000 23630093896019 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41326227/200000000 : ℝ), (1256835663/2500000000 : ℝ), (283586201/500000000 : ℝ)] ![(2488585790957/20000000000000 : ℝ), (8059376646417/20000000000000 : ℝ), (23630093896019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41326227/200000000 : ℝ)|^8415 ≤ (2488585790957/20000000000000 : ℝ)^6367
        have hw : |(-41326227/200000000 : ℝ)|=(41326227/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1256835663/2500000000 : ℝ)|^8415 ≤ (8059376646417/20000000000000 : ℝ)^6367
        have hw : |(1256835663/2500000000 : ℝ)|=(1256835663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283586201/500000000 : ℝ)|^8415 ≤ (23630093896019/50000000000000 : ℝ)^6367
        have hw : |(283586201/500000000 : ℝ)|=(283586201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s1_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (655542199/1250000000 : ℝ)*x 0 + (-442086249/2500000000 : ℝ)*x 1 + (2835858777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655542199/1250000000 : ℝ)^8415 ≤ (42611491717333/100000000000000 : ℝ)^6367 := by
    have hnat : (655542199 : ℕ)^8415*100000000000000^6367 ≤ 42611491717333^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655542199 1250000000 42611491717333 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442086249/2500000000 : ℝ)^8415 ≤ (2025678336459/20000000000000 : ℝ)^6367 := by
    have hnat : (442086249 : ℕ)^8415*20000000000000^6367 ≤ 2025678336459^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442086249 2500000000 2025678336459 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2835858777/5000000000 : ℝ)^8415 ≤ (2363005829149/5000000000000 : ℝ)^6367 := by
    have hnat : (2835858777 : ℕ)^8415*5000000000000^6367 ≤ 2363005829149^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835858777 5000000000 2363005829149 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655542199/1250000000 : ℝ), (-442086249/2500000000 : ℝ), (2835858777/5000000000 : ℝ)] ![(42611491717333/100000000000000 : ℝ), (2025678336459/20000000000000 : ℝ), (2363005829149/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655542199/1250000000 : ℝ)|^8415 ≤ (42611491717333/100000000000000 : ℝ)^6367
        have hw : |(655542199/1250000000 : ℝ)|=(655542199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442086249/2500000000 : ℝ)|^8415 ≤ (2025678336459/20000000000000 : ℝ)^6367
        have hw : |(-442086249/2500000000 : ℝ)|=(442086249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2835858777/5000000000 : ℝ)|^8415 ≤ (2363005829149/5000000000000 : ℝ)^6367
        have hw : |(2835858777/5000000000 : ℝ)|=(2835858777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s1_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2622168847/5000000000 : ℝ)*x 0 + (5671718039/10000000000 : ℝ)*x 1 + (-1768344147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622168847/5000000000 : ℝ)^8415 ≤ (4261149281269/10000000000000 : ℝ)^6367 := by
    have hnat : (2622168847 : ℕ)^8415*10000000000000^6367 ≤ 4261149281269^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622168847 5000000000 4261149281269 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5671718039/10000000000 : ℝ)^8415 ≤ (47260121924209/100000000000000 : ℝ)^6367 := by
    have hnat : (5671718039 : ℕ)^8415*100000000000000^6367 ≤ 47260121924209^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671718039 10000000000 47260121924209 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768344147/10000000000 : ℝ)^8415 ≤ (2532096313853/25000000000000 : ℝ)^6367 := by
    have hnat : (1768344147 : ℕ)^8415*25000000000000^6367 ≤ 2532096313853^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768344147 10000000000 2532096313853 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622168847/5000000000 : ℝ), (5671718039/10000000000 : ℝ), (-1768344147/10000000000 : ℝ)] ![(4261149281269/10000000000000 : ℝ), (47260121924209/100000000000000 : ℝ), (2532096313853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622168847/5000000000 : ℝ)|^8415 ≤ (4261149281269/10000000000000 : ℝ)^6367
        have hw : |(2622168847/5000000000 : ℝ)|=(2622168847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5671718039/10000000000 : ℝ)|^8415 ≤ (47260121924209/100000000000000 : ℝ)^6367
        have hw : |(5671718039/10000000000 : ℝ)|=(5671718039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1768344147/10000000000 : ℝ)|^8415 ≤ (2532096313853/25000000000000 : ℝ)^6367
        have hw : |(-1768344147/10000000000 : ℝ)|=(1768344147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s1_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (862400729/2000000000 : ℝ)*x 0 + (5011994061/10000000000 : ℝ)*x 1 + (3709885481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862400729/2000000000 : ℝ)^8415 ≤ (16449039297771/50000000000000 : ℝ)^6367 := by
    have hnat : (862400729 : ℕ)^8415*50000000000000^6367 ≤ 16449039297771^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862400729 2000000000 16449039297771 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5011994061/10000000000 : ℝ)^8415 ≤ (10033590761691/25000000000000 : ℝ)^6367 := by
    have hnat : (5011994061 : ℕ)^8415*25000000000000^6367 ≤ 10033590761691^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011994061 10000000000 10033590761691 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3709885481/10000000000 : ℝ)^8415 ≤ (26967558344169/100000000000000 : ℝ)^6367 := by
    have hnat : (3709885481 : ℕ)^8415*100000000000000^6367 ≤ 26967558344169^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709885481 10000000000 26967558344169 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862400729/2000000000 : ℝ), (5011994061/10000000000 : ℝ), (3709885481/10000000000 : ℝ)] ![(16449039297771/50000000000000 : ℝ), (10033590761691/25000000000000 : ℝ), (26967558344169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862400729/2000000000 : ℝ)|^8415 ≤ (16449039297771/50000000000000 : ℝ)^6367
        have hw : |(862400729/2000000000 : ℝ)|=(862400729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5011994061/10000000000 : ℝ)|^8415 ≤ (10033590761691/25000000000000 : ℝ)^6367
        have hw : |(5011994061/10000000000 : ℝ)|=(5011994061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3709885481/10000000000 : ℝ)|^8415 ≤ (26967558344169/100000000000000 : ℝ)^6367
        have hw : |(3709885481/10000000000 : ℝ)|=(3709885481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3043/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5021/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (369/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (369/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (369/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (369/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (369/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (369/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (369/50000 : ℝ) ^ (4207/1024 : ℝ) ≤ (174231264303/100000000000000000000 : ℝ) := by
    have hpowers : (369/50000 : ℝ)^4207 ≤ (174231264303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (369 : ℕ)^4207*100000000000000000000^1024 ≤ 174231264303^1024*50000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 50000 174231264303 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/50000 : ℝ)) (X := (174231264303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27511/100000 : ℝ) ^ (4207/1024 : ℝ) ≤ (24902266635176703/5000000000000000000 : ℝ) := by
    have hpowers : (27511/100000 : ℝ)^4207 ≤ (24902266635176703/5000000000000000000 : ℝ)^1024 := by
      have hnat : (27511 : ℕ)^4207*5000000000000000000^1024 ≤ 24902266635176703^1024*100000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27511 100000 24902266635176703 5000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27511/100000 : ℝ)) (X := (24902266635176703/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000174231264303/50000000000000000000 : ℝ) ≤ (10000000008481713/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50000000174231264303/50000000000000000000 : ℝ)^1024 ≤ (10000000008481713/10000000000000000 : ℝ)^4207 := by
      have hnat : (50000000174231264303 : ℕ)^1024*10000000000000000^4207 ≤ 10000000008481713^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000174231264303 50000000000000000000 10000000008481713 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000008481713/10000000000000000 : ℝ)) (X := (50000000174231264303/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100498045506934798363/100000000000000000000 : ℝ) ≤ (10012099845615981/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (100498045506934798363/100000000000000000000 : ℝ)^1024 ≤ (10012099845615981/10000000000000000 : ℝ)^4207 := by
      have hnat : (100498045506934798363 : ℕ)^1024*10000000000000000^4207 ≤ 10012099845615981^4207*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100498045506934798363 100000000000000000000 10012099845615981 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012099845615981/10000000000000000 : ℝ)) (X := (100498045506934798363/100000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2524902266635176703/2500000000000000000 : ℝ) ≤ (10024199682750249/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (2524902266635176703/2500000000000000000 : ℝ)^1024 ≤ (10024199682750249/10000000000000000 : ℝ)^4207 := by
      have hnat : (2524902266635176703 : ℕ)^1024*10000000000000000^4207 ≤ 10024199682750249^4207*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2524902266635176703 2500000000000000000 10024199682750249 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024199682750249/10000000000000000 : ℝ)) (X := (2524902266635176703/2500000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(174231264303/100000000000000000000 : ℝ) ≤ ((6529564411401724941/6530000000000000000 : ℝ)+2*(3024959283567/669325000000000 : ℝ)*(369/50000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (6529564411401724941/6530000000000000000 : ℝ)+2*(3024959283567/669325000000000 : ℝ)*(369/50000 : ℝ)=(10000000008481713/10000000000000000 : ℝ) by norm_num, show 1+2*(174231264303/100000000000000000000 : ℝ)=(50000000174231264303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24902266635176703/5000000000000000000 : ℝ)+(174231264303/100000000000000000000 : ℝ) ≤ ((6529564411401724941/6530000000000000000 : ℝ)+(3024959283567/669325000000000 : ℝ)*((27511/100000 : ℝ)+(369/50000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (6529564411401724941/6530000000000000000 : ℝ)+(3024959283567/669325000000000 : ℝ)*((27511/100000 : ℝ)+(369/50000 : ℝ))=(10012099845615981/10000000000000000 : ℝ) by norm_num, show 1+(24902266635176703/5000000000000000000 : ℝ)+(174231264303/100000000000000000000 : ℝ)=(100498045506934798363/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24902266635176703/5000000000000000000 : ℝ) ≤ ((6529564411401724941/6530000000000000000 : ℝ)+2*(3024959283567/669325000000000 : ℝ)*(27511/100000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (6529564411401724941/6530000000000000000 : ℝ)+2*(3024959283567/669325000000000 : ℝ)*(27511/100000 : ℝ)=(10024199682750249/10000000000000000 : ℝ) by norm_num, show 1+2*(24902266635176703/5000000000000000000 : ℝ)=(2524902266635176703/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6529564411401724941/6530000000000000000 : ℝ)*(X 1 0+X 2 0)+(3024959283567/669325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (369/50000 : ℝ)) (hi := (27511/100000 : ℝ)) (c := (6529564411401724941/6530000000000000000 : ℝ)) (alpha := (3024959283567/669325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6529564411401724941/6530000000000000000 : ℝ)*(X 0 1+X 2 1)+(3024959283567/669325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (369/50000 : ℝ)) (hi := (27511/100000 : ℝ)) (c := (6529564411401724941/6530000000000000000 : ℝ)) (alpha := (3024959283567/669325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6529564411401724941/6530000000000000000 : ℝ)*(X 0 2+X 1 2)+(3024959283567/669325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (369/50000 : ℝ)) (hi := (27511/100000 : ℝ)) (c := (6529564411401724941/6530000000000000000 : ℝ)) (alpha := (3024959283567/669325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1032807407/5000000000 : ℝ)*X 0 0+(1420162939/2500000000 : ℝ)*X 0 1+(627322529/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5414744543/10000000000 : ℝ)*X 1 0+(-2421483169/10000000000 : ℝ)*X 1 1+(501858023/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5414744557/10000000000 : ℝ)*X 2 0+(2509290119/5000000000 : ℝ)*X 2 1+(-2421483139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172423579/400000000 : ℝ)*X 0 0+(738366421/2000000000 : ℝ)*X 0 1+(2514853377/5000000000 : ℝ)*X 0 2+(172423579/400000000 : ℝ)*X 1 0+(738366421/2000000000 : ℝ)*X 1 1+(2514853377/5000000000 : ℝ)*X 1 2+(172423579/400000000 : ℝ)*X 2 0+(738366421/2000000000 : ℝ)*X 2 1+(2514853377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-41326227/200000000 : ℝ)*X 0 0+(1256835663/2500000000 : ℝ)*X 0 1+(283586201/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((655542199/1250000000 : ℝ)*X 1 0+(-442086249/2500000000 : ℝ)*X 1 1+(2835858777/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2622168847/5000000000 : ℝ)*X 2 0+(5671718039/10000000000 : ℝ)*X 2 1+(-1768344147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862400729/2000000000 : ℝ)*X 0 0+(5011994061/10000000000 : ℝ)*X 0 1+(3709885481/10000000000 : ℝ)*X 0 2+(862400729/2000000000 : ℝ)*X 1 0+(5011994061/10000000000 : ℝ)*X 1 1+(3709885481/10000000000 : ℝ)*X 1 2+(862400729/2000000000 : ℝ)*X 2 0+(5011994061/10000000000 : ℝ)*X 2 1+(3709885481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6903485579699525096297567277/2677300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35468629/100000000000000 : ℝ)*(base1) + (587889897/100000000000000 : ℝ)*(base19) + (591795129/100000000000000 : ℝ)*(base23) + (64689831/100000000000000 : ℝ)*(upper3) + (9574487/12500000000000 : ℝ)*(upper5) + (225787467114287/20000000000000 : ℝ)*(major0) + (225787467114287/20000000000000 : ℝ)*(major1) + (225787467114287/20000000000000 : ℝ)*(major2) + (377603456971863/25000000000000 : ℝ)*(sp0) + (377604105168453/25000000000000 : ℝ)*(sp1) + (755208208384291/50000000000000 : ℝ)*(sp2) + (373727931326459/50000000000000 : ℝ)*(sp3) + (3216144887/100000000000000 : ℝ)*(sp4) + (1678506763/100000000000000 : ℝ)*(sp7) + (747457576628311/100000000000000 : ℝ)*(f.failure) + (151041700856371/10000000000000 : ℝ)*(f.sum) + (9279887114021/5354600000000000000000000000 : ℝ)*base65 + (50642674399682814747/5354600000000000000000000000000000 : ℝ)*base67 + (25522115686256814747/5354600000000000000000000000000000 : ℝ)*base69 + (39684784650475614747/5354600000000000000000000000000000 : ℝ)*base71 + (111776721503951/26773000000000000000000000000 : ℝ)*base73 + (69131037461739214747/5354600000000000000000000000000000 : ℝ)*base75 + (2185984008988814747/5354600000000000000000000000000000 : ℝ)*base77 + (18282168147874814747/5354600000000000000000000000000000 : ℝ)*base79 + (30885861589959/5354600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (11342079/5000000000000000000000 : ℝ)*base89 + (11342079/5000000000000000000000 : ℝ)*base91 + (11342079/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44844907823458292929438006461/6693250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204885599/50000000000000 : ℝ)*(base19) + (267429731/25000000000000 : ℝ)*(base23) + (34770659/25000000000000 : ℝ)*(lower2) + (10315569/4000000000000 : ℝ)*(lower3) + (423526501/100000000000000 : ℝ)*(lower4) + (579969676839391/50000000000000 : ℝ)*(major0) + (579969676839391/50000000000000 : ℝ)*(major1) + (579969676839391/50000000000000 : ℝ)*(major2) + (8699545361/100000000000000 : ℝ)*(sp0) + (2689192439/100000000000000 : ℝ)*(sp2) + (775943048308407/50000000000000 : ℝ)*(sp4) + (1551894386390977/100000000000000 : ℝ)*(sp5) + (1551891037250813/100000000000000 : ℝ)*(sp6) + (38399184393069/5000000000000 : ℝ)*(sp7) + (38399184393069/5000000000000 : ℝ)*(f.failure) + (12124178095017/781250000000 : ℝ)*(f.sum) + (669319265680357/66932500000000000000000000000 : ℝ)*base66 + (131785133068656788171/13386500000000000000000000000000000 : ℝ)*base67 + (62227794922794788171/13386500000000000000000000000000000 : ℝ)*base69 + (55167250526566788171/13386500000000000000000000000000000 : ℝ)*base71 + (17158747615807/16733125000000000000000000000 : ℝ)*base73 + (167224349506445788171/13386500000000000000000000000000000 : ℝ)*base75 + (126676027811040288171/13386500000000000000000000000000000 : ℝ)*base77 + (207886293966514288171/13386500000000000000000000000000000 : ℝ)*base79 + (31800490591441/8366562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2047259/250000000000000000000 : ℝ)*base90 + (2047259/250000000000000000000 : ℝ)*base92 + (2047259/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1222_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3043/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5021/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1222_s2_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528665681/2500000000 : ℝ)*x 0 + (137405803/250000000 : ℝ)*x 1 + (258586917/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528665681/2500000000 : ℝ)^8415 ≤ (1603648400371/12500000000000 : ℝ)^6367 := by
    have hnat : (528665681 : ℕ)^8415*12500000000000^6367 ≤ 1603648400371^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528665681 2500000000 1603648400371 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137405803/250000000 : ℝ)^8415 ≤ (45337207981137/100000000000000 : ℝ)^6367 := by
    have hnat : (137405803 : ℕ)^8415*100000000000000^6367 ≤ 45337207981137^6367*250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137405803 250000000 45337207981137 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258586917/500000000 : ℝ)^8415 ≤ (41833604806311/100000000000000 : ℝ)^6367 := by
    have hnat : (258586917 : ℕ)^8415*100000000000000^6367 ≤ 41833604806311^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258586917 500000000 41833604806311 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528665681/2500000000 : ℝ), (137405803/250000000 : ℝ), (258586917/500000000 : ℝ)] ![(1603648400371/12500000000000 : ℝ), (45337207981137/100000000000000 : ℝ), (41833604806311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528665681/2500000000 : ℝ)|^8415 ≤ (1603648400371/12500000000000 : ℝ)^6367
        have hw : |(-528665681/2500000000 : ℝ)|=(528665681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137405803/250000000 : ℝ)|^8415 ≤ (45337207981137/100000000000000 : ℝ)^6367
        have hw : |(137405803/250000000 : ℝ)|=(137405803/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258586917/500000000 : ℝ)|^8415 ≤ (41833604806311/100000000000000 : ℝ)^6367
        have hw : |(258586917/500000000 : ℝ)|=(258586917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s2_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685251241/5000000000 : ℝ)*x 0 + (-2282866377/10000000000 : ℝ)*x 1 + (2585869137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685251241/5000000000 : ℝ)^8415 ≤ (21985781960179/50000000000000 : ℝ)^6367 := by
    have hnat : (2685251241 : ℕ)^8415*50000000000000^6367 ≤ 21985781960179^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685251241 5000000000 21985781960179 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282866377/10000000000 : ℝ)^8415 ≤ (221794249347/1562500000000 : ℝ)^6367 := by
    have hnat : (2282866377 : ℕ)^8415*1562500000000^6367 ≤ 221794249347^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282866377 10000000000 221794249347 1562500000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585869137/5000000000 : ℝ)^8415 ≤ (20916802050361/50000000000000 : ℝ)^6367 := by
    have hnat : (2585869137 : ℕ)^8415*50000000000000^6367 ≤ 20916802050361^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585869137 5000000000 20916802050361 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685251241/5000000000 : ℝ), (-2282866377/10000000000 : ℝ), (2585869137/5000000000 : ℝ)] ![(21985781960179/50000000000000 : ℝ), (221794249347/1562500000000 : ℝ), (20916802050361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685251241/5000000000 : ℝ)|^8415 ≤ (21985781960179/50000000000000 : ℝ)^6367
        have hw : |(2685251241/5000000000 : ℝ)|=(2685251241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282866377/10000000000 : ℝ)|^8415 ≤ (221794249347/1562500000000 : ℝ)^6367
        have hw : |(-2282866377/10000000000 : ℝ)|=(2282866377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585869137/5000000000 : ℝ)|^8415 ≤ (20916802050361/50000000000000 : ℝ)^6367
        have hw : |(2585869137/5000000000 : ℝ)|=(2585869137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s2_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370502287/10000000000 : ℝ)*x 0 + (5171738447/10000000000 : ℝ)*x 1 + (-2282866409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370502287/10000000000 : ℝ)^8415 ≤ (2198578090511/5000000000000 : ℝ)^6367 := by
    have hnat : (5370502287 : ℕ)^8415*5000000000000^6367 ≤ 2198578090511^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370502287 10000000000 2198578090511 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5171738447/10000000000 : ℝ)^8415 ≤ (41833605950221/100000000000000 : ℝ)^6367 := by
    have hnat : (5171738447 : ℕ)^8415*100000000000000^6367 ≤ 41833605950221^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171738447 10000000000 41833605950221 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282866409/10000000000 : ℝ)^8415 ≤ (2838966444237/20000000000000 : ℝ)^6367 := by
    have hnat : (2282866409 : ℕ)^8415*20000000000000^6367 ≤ 2838966444237^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282866409 10000000000 2838966444237 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370502287/10000000000 : ℝ), (5171738447/10000000000 : ℝ), (-2282866409/10000000000 : ℝ)] ![(2198578090511/5000000000000 : ℝ), (41833605950221/100000000000000 : ℝ), (2838966444237/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370502287/10000000000 : ℝ)|^8415 ≤ (2198578090511/5000000000000 : ℝ)^6367
        have hw : |(5370502287/10000000000 : ℝ)|=(5370502287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5171738447/10000000000 : ℝ)|^8415 ≤ (41833605950221/100000000000000 : ℝ)^6367
        have hw : |(5171738447/10000000000 : ℝ)|=(5171738447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282866409/10000000000 : ℝ)|^8415 ≤ (2838966444237/20000000000000 : ℝ)^6367
        have hw : |(-2282866409/10000000000 : ℝ)|=(2282866409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s2_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086106601/2500000000 : ℝ)*x 0 + (503575549/1250000000 : ℝ)*x 1 + (4684322083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086106601/2500000000 : ℝ)^8415 ≤ (8306351928601/25000000000000 : ℝ)^6367 := by
    have hnat : (1086106601 : ℕ)^8415*25000000000000^6367 ≤ 8306351928601^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086106601 2500000000 8306351928601 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503575549/1250000000 : ℝ)^8415 ≤ (3758886759443/12500000000000 : ℝ)^6367 := by
    have hnat : (503575549 : ℕ)^8415*12500000000000^6367 ≤ 3758886759443^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503575549 1250000000 3758886759443 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4684322083/10000000000 : ℝ)^8415 ≤ (18351749093391/50000000000000 : ℝ)^6367 := by
    have hnat : (4684322083 : ℕ)^8415*50000000000000^6367 ≤ 18351749093391^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4684322083 10000000000 18351749093391 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086106601/2500000000 : ℝ), (503575549/1250000000 : ℝ), (4684322083/10000000000 : ℝ)] ![(8306351928601/25000000000000 : ℝ), (3758886759443/12500000000000 : ℝ), (18351749093391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086106601/2500000000 : ℝ)|^8415 ≤ (8306351928601/25000000000000 : ℝ)^6367
        have hw : |(1086106601/2500000000 : ℝ)|=(1086106601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503575549/1250000000 : ℝ)|^8415 ≤ (3758886759443/12500000000000 : ℝ)^6367
        have hw : |(503575549/1250000000 : ℝ)|=(503575549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4684322083/10000000000 : ℝ)|^8415 ≤ (18351749093391/50000000000000 : ℝ)^6367
        have hw : |(4684322083/10000000000 : ℝ)|=(4684322083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s2_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-33042897/156250000 : ℝ)*x 0 + (5173853467/10000000000 : ℝ)*x 1 + (549409691/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33042897/156250000 : ℝ)^8415 ≤ (801865636539/6250000000000 : ℝ)^6367 := by
    have hnat : (33042897 : ℕ)^8415*6250000000000^6367 ≤ 801865636539^6367*156250000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33042897 156250000 801865636539 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173853467/10000000000 : ℝ)^8415 ≤ (20928109289631/50000000000000 : ℝ)^6367 := by
    have hnat : (5173853467 : ℕ)^8415*50000000000000^6367 ≤ 20928109289631^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173853467 10000000000 20928109289631 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549409691/1000000000 : ℝ)^8415 ≤ (45313931226281/100000000000000 : ℝ)^6367 := by
    have hnat : (549409691 : ℕ)^8415*100000000000000^6367 ≤ 45313931226281^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549409691 1000000000 45313931226281 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33042897/156250000 : ℝ), (5173853467/10000000000 : ℝ), (549409691/1000000000 : ℝ)] ![(801865636539/6250000000000 : ℝ), (20928109289631/50000000000000 : ℝ), (45313931226281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33042897/156250000 : ℝ)|^8415 ≤ (801865636539/6250000000000 : ℝ)^6367
        have hw : |(-33042897/156250000 : ℝ)|=(33042897/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173853467/10000000000 : ℝ)|^8415 ≤ (20928109289631/50000000000000 : ℝ)^6367
        have hw : |(5173853467/10000000000 : ℝ)|=(5173853467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549409691/1000000000 : ℝ)|^8415 ≤ (45313931226281/100000000000000 : ℝ)^6367
        have hw : |(549409691/1000000000 : ℝ)|=(549409691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s2_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287739139/10000000000 : ℝ)*x 0 + (-980253789/5000000000 : ℝ)*x 1 + (2747048473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287739139/10000000000 : ℝ)^8415 ≤ (1723127641351/4000000000000 : ℝ)^6367 := by
    have hnat : (5287739139 : ℕ)^8415*4000000000000^6367 ≤ 1723127641351^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287739139 10000000000 1723127641351 4000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980253789/5000000000 : ℝ)^8415 ≤ (725492333117/6250000000000 : ℝ)^6367 := by
    have hnat : (980253789 : ℕ)^8415*6250000000000^6367 ≤ 725492333117^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980253789 5000000000 725492333117 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747048473/5000000000 : ℝ)^8415 ≤ (22656965809353/50000000000000 : ℝ)^6367 := by
    have hnat : (2747048473 : ℕ)^8415*50000000000000^6367 ≤ 22656965809353^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747048473 5000000000 22656965809353 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287739139/10000000000 : ℝ), (-980253789/5000000000 : ℝ), (2747048473/5000000000 : ℝ)] ![(1723127641351/4000000000000 : ℝ), (725492333117/6250000000000 : ℝ), (22656965809353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287739139/10000000000 : ℝ)|^8415 ≤ (1723127641351/4000000000000 : ℝ)^6367
        have hw : |(5287739139/10000000000 : ℝ)|=(5287739139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-980253789/5000000000 : ℝ)|^8415 ≤ (725492333117/6250000000000 : ℝ)^6367
        have hw : |(-980253789/5000000000 : ℝ)|=(980253789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747048473/5000000000 : ℝ)|^8415 ≤ (22656965809353/50000000000000 : ℝ)^6367
        have hw : |(2747048473/5000000000 : ℝ)|=(2747048473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s2_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287739321/10000000000 : ℝ)*x 0 + (2747048497/5000000000 : ℝ)*x 1 + (-1960507261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287739321/10000000000 : ℝ)^8415 ≤ (43078192993423/100000000000000 : ℝ)^6367 := by
    have hnat : (5287739321 : ℕ)^8415*100000000000000^6367 ≤ 43078192993423^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287739321 10000000000 43078192993423 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747048497/5000000000 : ℝ)^8415 ≤ (2265696607097/5000000000000 : ℝ)^6367 := by
    have hnat : (2747048497 : ℕ)^8415*5000000000000^6367 ≤ 2265696607097^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747048497 5000000000 2265696607097 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1960507261/10000000000 : ℝ)^8415 ≤ (11607874849237/100000000000000 : ℝ)^6367 := by
    have hnat : (1960507261 : ℕ)^8415*100000000000000^6367 ≤ 11607874849237^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960507261 10000000000 11607874849237 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287739321/10000000000 : ℝ), (2747048497/5000000000 : ℝ), (-1960507261/10000000000 : ℝ)] ![(43078192993423/100000000000000 : ℝ), (2265696607097/5000000000000 : ℝ), (11607874849237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287739321/10000000000 : ℝ)|^8415 ≤ (43078192993423/100000000000000 : ℝ)^6367
        have hw : |(5287739321/10000000000 : ℝ)|=(5287739321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747048497/5000000000 : ℝ)|^8415 ≤ (2265696607097/5000000000000 : ℝ)^6367
        have hw : |(2747048497/5000000000 : ℝ)|=(2747048497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1960507261/10000000000 : ℝ)|^8415 ≤ (11607874849237/100000000000000 : ℝ)^6367
        have hw : |(-1960507261/10000000000 : ℝ)|=(1960507261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s2_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4344592959/10000000000 : ℝ)*x 0 + (468004809/1000000000 : ℝ)*x 1 + (2016459381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344592959/10000000000 : ℝ)^8415 ≤ (3322709123137/10000000000000 : ℝ)^6367 := by
    have hnat : (4344592959 : ℕ)^8415*10000000000000^6367 ≤ 3322709123137^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344592959 10000000000 3322709123137 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468004809/1000000000 : ℝ)^8415 ≤ (36659244440633/100000000000000 : ℝ)^6367 := by
    have hnat : (468004809 : ℕ)^8415*100000000000000^6367 ≤ 36659244440633^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468004809 1000000000 36659244440633 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016459381/5000000000 : ℝ)^8415 ≤ (7528416077513/25000000000000 : ℝ)^6367 := by
    have hnat : (2016459381 : ℕ)^8415*25000000000000^6367 ≤ 7528416077513^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016459381 5000000000 7528416077513 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344592959/10000000000 : ℝ), (468004809/1000000000 : ℝ), (2016459381/5000000000 : ℝ)] ![(3322709123137/10000000000000 : ℝ), (36659244440633/100000000000000 : ℝ), (7528416077513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344592959/10000000000 : ℝ)|^8415 ≤ (3322709123137/10000000000000 : ℝ)^6367
        have hw : |(4344592959/10000000000 : ℝ)|=(4344592959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(468004809/1000000000 : ℝ)|^8415 ≤ (36659244440633/100000000000000 : ℝ)^6367
        have hw : |(468004809/1000000000 : ℝ)|=(468004809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016459381/5000000000 : ℝ)|^8415 ≤ (7528416077513/25000000000000 : ℝ)^6367
        have hw : |(2016459381/5000000000 : ℝ)|=(2016459381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5021/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3043/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9417/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4069/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5021/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3043/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5021/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3043/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5021/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3043/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5021/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3043/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5021/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3043/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5021/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3043/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3043/50000 : ℝ) ^ (4207/1024 : ℝ) ≤ (506432162508281/50000000000000000000 : ℝ) := by
    have hpowers : (3043/50000 : ℝ)^4207 ≤ (506432162508281/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3043 : ℕ)^4207*50000000000000000000^1024 ≤ 506432162508281^1024*50000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3043 50000 506432162508281 50000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3043/50000 : ℝ)) (X := (506432162508281/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5021/25000 : ℝ) ^ (4207/1024 : ℝ) ≤ (13671963905572937/10000000000000000000 : ℝ) := by
    have hpowers : (5021/25000 : ℝ)^4207 ≤ (13671963905572937/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5021 : ℕ)^4207*10000000000000000000^1024 ≤ 13671963905572937^1024*25000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5021 25000 13671963905572937 10000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5021/25000 : ℝ)) (X := (13671963905572937/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000506432162508281/25000000000000000000 : ℝ) ≤ (2000009861327509/2000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (25000506432162508281/25000000000000000000 : ℝ)^1024 ≤ (2000009861327509/2000000000000000 : ℝ)^4207 := by
      have hnat : (25000506432162508281 : ℕ)^1024*2000000000000000^4207 ≤ 2000009861327509^4207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000506432162508281 25000000000000000000 2000009861327509 2000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000009861327509/2000000000000000 : ℝ)) (X := (25000506432162508281/25000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25034433125845186483/25000000000000000000 : ℝ) ≤ (2500837679202939/2500000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (25034433125845186483/25000000000000000000 : ℝ)^1024 ≤ (2500837679202939/2500000000000000 : ℝ)^4207 := by
      have hnat : (25034433125845186483 : ℕ)^1024*2500000000000000^4207 ≤ 2500837679202939^4207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034433125845186483 25000000000000000000 2500837679202939 2500000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500837679202939/2500000000000000 : ℝ)) (X := (25034433125845186483/25000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5013671963905572937/5000000000000000000 : ℝ) ≤ (10006652126985967/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (5013671963905572937/5000000000000000000 : ℝ)^1024 ≤ (10006652126985967/10000000000000000 : ℝ)^4207 := by
      have hnat : (5013671963905572937 : ℕ)^1024*10000000000000000^4207 ≤ 10006652126985967^4207*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5013671963905572937 5000000000000000000 10006652126985967 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006652126985967/10000000000000000 : ℝ)) (X := (5013671963905572937/5000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(506432162508281/50000000000000000000 : ℝ) ≤ ((69970252714835929309/69990000000000000000 : ℝ)+2*(3301410174211/1399800000000000 : ℝ)*(3043/50000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (69970252714835929309/69990000000000000000 : ℝ)+2*(3301410174211/1399800000000000 : ℝ)*(3043/50000 : ℝ)=(2000009861327509/2000000000000000 : ℝ) by norm_num, show 1+2*(506432162508281/50000000000000000000 : ℝ)=(25000506432162508281/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13671963905572937/10000000000000000000 : ℝ)+(506432162508281/50000000000000000000 : ℝ) ≤ ((69970252714835929309/69990000000000000000 : ℝ)+(3301410174211/1399800000000000 : ℝ)*((5021/25000 : ℝ)+(3043/50000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (69970252714835929309/69990000000000000000 : ℝ)+(3301410174211/1399800000000000 : ℝ)*((5021/25000 : ℝ)+(3043/50000 : ℝ))=(2500837679202939/2500000000000000 : ℝ) by norm_num, show 1+(13671963905572937/10000000000000000000 : ℝ)+(506432162508281/50000000000000000000 : ℝ)=(25034433125845186483/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13671963905572937/10000000000000000000 : ℝ) ≤ ((69970252714835929309/69990000000000000000 : ℝ)+2*(3301410174211/1399800000000000 : ℝ)*(5021/25000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (69970252714835929309/69990000000000000000 : ℝ)+2*(3301410174211/1399800000000000 : ℝ)*(5021/25000 : ℝ)=(10006652126985967/10000000000000000 : ℝ) by norm_num, show 1+2*(13671963905572937/10000000000000000000 : ℝ)=(5013671963905572937/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69970252714835929309/69990000000000000000 : ℝ)*(X 1 0+X 2 0)+(3301410174211/1399800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (3043/50000 : ℝ)) (hi := (5021/25000 : ℝ)) (c := (69970252714835929309/69990000000000000000 : ℝ)) (alpha := (3301410174211/1399800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69970252714835929309/69990000000000000000 : ℝ)*(X 0 1+X 2 1)+(3301410174211/1399800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (3043/50000 : ℝ)) (hi := (5021/25000 : ℝ)) (c := (69970252714835929309/69990000000000000000 : ℝ)) (alpha := (3301410174211/1399800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69970252714835929309/69990000000000000000 : ℝ)*(X 0 2+X 1 2)+(3301410174211/1399800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (3043/50000 : ℝ)) (hi := (5021/25000 : ℝ)) (c := (69970252714835929309/69990000000000000000 : ℝ)) (alpha := (3301410174211/1399800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-528665681/2500000000 : ℝ)*X 0 0+(137405803/250000000 : ℝ)*X 0 1+(258586917/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685251241/5000000000 : ℝ)*X 1 0+(-2282866377/10000000000 : ℝ)*X 1 1+(2585869137/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370502287/10000000000 : ℝ)*X 2 0+(5171738447/10000000000 : ℝ)*X 2 1+(-2282866409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086106601/2500000000 : ℝ)*X 0 0+(503575549/1250000000 : ℝ)*X 0 1+(4684322083/10000000000 : ℝ)*X 0 2+(1086106601/2500000000 : ℝ)*X 1 0+(503575549/1250000000 : ℝ)*X 1 1+(4684322083/10000000000 : ℝ)*X 1 2+(1086106601/2500000000 : ℝ)*X 2 0+(503575549/1250000000 : ℝ)*X 2 1+(4684322083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33042897/156250000 : ℝ)*X 0 0+(5173853467/10000000000 : ℝ)*X 0 1+(549409691/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287739139/10000000000 : ℝ)*X 1 0+(-980253789/5000000000 : ℝ)*X 1 1+(2747048473/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287739321/10000000000 : ℝ)*X 2 0+(2747048497/5000000000 : ℝ)*X 2 1+(-1960507261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4344592959/10000000000 : ℝ)*X 0 0+(468004809/1000000000 : ℝ)*X 0 1+(2016459381/5000000000 : ℝ)*X 0 2+(4344592959/10000000000 : ℝ)*X 1 0+(468004809/1000000000 : ℝ)*X 1 1+(2016459381/5000000000 : ℝ)*X 1 2+(4344592959/10000000000 : ℝ)*X 2 0+(468004809/1000000000 : ℝ)*X 2 1+(2016459381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2372408848770176390496969619/291625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1649327771/100000000000000 : ℝ)*(base19) + (1422033239/100000000000000 : ℝ)*(base23) + (30987169/50000000000000 : ℝ)*(lower2) + (129685947/50000000000000 : ℝ)*(upper3) + (116212161/100000000000000 : ℝ)*(upper5) + (1151705587902409/50000000000000 : ℝ)*(major0) + (1151705587902409/50000000000000 : ℝ)*(major1) + (1151705587902409/50000000000000 : ℝ)*(major2) + (385217707284267/12500000000000 : ℝ)*(sp0) + (308175603542023/10000000000000 : ℝ)*(sp1) + (1540878131357381/50000000000000 : ℝ)*(sp2) + (152505478729717/10000000000000 : ℝ)*(sp3) + (2003309233/12500000000000 : ℝ)*(sp4) + (30026229/312500000000 : ℝ)*(sp7) + (30501287913809/2000000000000 : ℝ)*(f.failure) + (3081757684748001/100000000000000 : ℝ)*(f.sum) + (72105491919581/34995000000000000000000000000 : ℝ)*base66 + (11306665252184585127/1166500000000000000000000000000000 : ℝ)*base67 + (20244950152901585127/1166500000000000000000000000000000 : ℝ)*base69 + (2359070848586585127/1166500000000000000000000000000000 : ℝ)*base71 + (69884355980051/34995000000000000000000000000 : ℝ)*base74 + (6964174380991585127/1166500000000000000000000000000000 : ℝ)*base75 + (5833316317225585127/1166500000000000000000000000000000 : ℝ)*base77 + (2854784501514414873/1166500000000000000000000000000000 : ℝ)*base80 + (111687352628359/34995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (85399/100000000000000000000 : ℝ)*base90 + (85399/100000000000000000000 : ℝ)*base92 + (85399/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1689790004261940136668745033/291625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1524358727/100000000000000 : ℝ)*(base19) + (178500349/10000000000000 : ℝ)*(base23) + (9013751/25000000000000 : ℝ)*(upper2) + (209380497/100000000000000 : ℝ)*(upper3) + (23163761/20000000000000 : ℝ)*(upper5) + (1166977566243437/50000000000000 : ℝ)*(major0) + (1166977566243437/50000000000000 : ℝ)*(major1) + (1166977566243437/50000000000000 : ℝ)*(major2) + (15160820897/100000000000000 : ℝ)*(sp1) + (5147576109/25000000000000 : ℝ)*(sp2) + (1561311421286083/50000000000000 : ℝ)*(sp4) + (1561303078696271/50000000000000 : ℝ)*(sp5) + (3122600467264239/100000000000000 : ℝ)*(sp6) + (772643614627563/50000000000000 : ℝ)*(sp7) + (772643614627563/50000000000000 : ℝ)*(f.failure) + (1561311421286083/50000000000000 : ℝ)*(f.sum) + (80139652586263/34995000000000000000000000000 : ℝ)*base66 + (8773056882130484989/1166500000000000000000000000000000 : ℝ)*base68 + (6478868915095484989/1166500000000000000000000000000000 : ℝ)*base70 + (13022519170686484989/1166500000000000000000000000000000 : ℝ)*base72 + (3850617153841/17497500000000000000000000000 : ℝ)*base73 + (12225842826520484989/1166500000000000000000000000000000 : ℝ)*base76 + (11162673919659984989/1166500000000000000000000000000000 : ℝ)*base78 + (870808134025515011/1166500000000000000000000000000000 : ℝ)*base79 + (1969642351219/4374375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5512307/2500000000000000000000 : ℝ)*base89 + (5512307/2500000000000000000000 : ℝ)*base91 + (5512307/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1222_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5021/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3043/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1222_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1222_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1222_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1222_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4069/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1222_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

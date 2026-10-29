-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1496_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:51:33.570665+00:00
-- url     : https://prove2.me/submissions/944c2047-eea2-46ba-b0ec-8d83a9e1d2d6

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
theorem support_rectangle_w1496_s6_0 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1891917437/10000000000 : ℝ)*x 0 + (10615863/19531250 : ℝ)*x 1 + (5216786127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1891917437/10000000000 : ℝ)^4489 ≤ (1156664670649/10000000000000 : ℝ)^3465 := by
    have hnat : (1891917437 : ℕ)^4489*10000000000000^3465 ≤ 1156664670649^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891917437 10000000000 1156664670649 10000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10615863/19531250 : ℝ)^4489 ≤ (45391785278377/100000000000000 : ℝ)^3465 := by
    have hnat : (10615863 : ℕ)^4489*100000000000000^3465 ≤ 45391785278377^3465*19531250^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10615863 19531250 45391785278377 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216786127/10000000000 : ℝ)^4489 ≤ (2690097999969/6250000000000 : ℝ)^3465 := by
    have hnat : (5216786127 : ℕ)^4489*6250000000000^3465 ≤ 2690097999969^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216786127 10000000000 2690097999969 6250000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1891917437/10000000000 : ℝ), (10615863/19531250 : ℝ), (5216786127/10000000000 : ℝ)] ![(1156664670649/10000000000000 : ℝ), (45391785278377/100000000000000 : ℝ), (2690097999969/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1891917437/10000000000 : ℝ)|^4489 ≤ (1156664670649/10000000000000 : ℝ)^3465
        have hw : |(-1891917437/10000000000 : ℝ)|=(1891917437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10615863/19531250 : ℝ)|^4489 ≤ (45391785278377/100000000000000 : ℝ)^3465
        have hw : |(10615863/19531250 : ℝ)|=(10615863/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216786127/10000000000 : ℝ)|^4489 ≤ (2690097999969/6250000000000 : ℝ)^3465
        have hw : |(5216786127/10000000000 : ℝ)|=(5216786127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s6_1 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352464629/10000000000 : ℝ)*x 0 + (-250484719/1250000000 : ℝ)*x 1 + (326049133/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352464629/10000000000 : ℝ)^4489 ≤ (44497356306039/100000000000000 : ℝ)^3465 := by
    have hnat : (5352464629 : ℕ)^4489*100000000000000^3465 ≤ 44497356306039^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352464629 10000000000 44497356306039 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250484719/1250000000 : ℝ)^4489 ≤ (12461075667641/100000000000000 : ℝ)^3465 := by
    have hnat : (250484719 : ℕ)^4489*100000000000000^3465 ≤ 12461075667641^3465*1250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250484719 1250000000 12461075667641 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326049133/625000000 : ℝ)^4489 ≤ (43041568010193/100000000000000 : ℝ)^3465 := by
    have hnat : (326049133 : ℕ)^4489*100000000000000^3465 ≤ 43041568010193^3465*625000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326049133 625000000 43041568010193 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352464629/10000000000 : ℝ), (-250484719/1250000000 : ℝ), (326049133/625000000 : ℝ)] ![(44497356306039/100000000000000 : ℝ), (12461075667641/100000000000000 : ℝ), (43041568010193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352464629/10000000000 : ℝ)|^4489 ≤ (44497356306039/100000000000000 : ℝ)^3465
        have hw : |(5352464629/10000000000 : ℝ)|=(5352464629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250484719/1250000000 : ℝ)|^4489 ≤ (12461075667641/100000000000000 : ℝ)^3465
        have hw : |(-250484719/1250000000 : ℝ)|=(250484719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326049133/625000000 : ℝ)|^4489 ≤ (43041568010193/100000000000000 : ℝ)^3465
        have hw : |(326049133/625000000 : ℝ)|=(326049133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s6_2 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352464629/10000000000 : ℝ)*x 0 + (5216786127/10000000000 : ℝ)*x 1 + (-250484719/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352464629/10000000000 : ℝ)^4489 ≤ (44497356306039/100000000000000 : ℝ)^3465 := by
    have hnat : (5352464629 : ℕ)^4489*100000000000000^3465 ≤ 44497356306039^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352464629 10000000000 44497356306039 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216786127/10000000000 : ℝ)^4489 ≤ (2690097999969/6250000000000 : ℝ)^3465 := by
    have hnat : (5216786127 : ℕ)^4489*6250000000000^3465 ≤ 2690097999969^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216786127 10000000000 2690097999969 6250000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250484719/1250000000 : ℝ)^4489 ≤ (12461075667641/100000000000000 : ℝ)^3465 := by
    have hnat : (250484719 : ℕ)^4489*100000000000000^3465 ≤ 12461075667641^3465*1250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250484719 1250000000 12461075667641 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352464629/10000000000 : ℝ), (5216786127/10000000000 : ℝ), (-250484719/1250000000 : ℝ)] ![(44497356306039/100000000000000 : ℝ), (2690097999969/6250000000000 : ℝ), (12461075667641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352464629/10000000000 : ℝ)|^4489 ≤ (44497356306039/100000000000000 : ℝ)^3465
        have hw : |(5352464629/10000000000 : ℝ)|=(5352464629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216786127/10000000000 : ℝ)|^4489 ≤ (2690097999969/6250000000000 : ℝ)^3465
        have hw : |(5216786127/10000000000 : ℝ)|=(5216786127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250484719/1250000000 : ℝ)|^4489 ≤ (12461075667641/100000000000000 : ℝ)^3465
        have hw : |(-250484719/1250000000 : ℝ)|=(250484719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s6_3 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4277281957/10000000000 : ℝ)*x 0 + (2019167647/5000000000 : ℝ)*x 1 + (4528301803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277281957/10000000000 : ℝ)^4489 ≤ (3327883711567/10000000000000 : ℝ)^3465 := by
    have hnat : (4277281957 : ℕ)^4489*10000000000000^3465 ≤ 3327883711567^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277281957 10000000000 3327883711567 10000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2019167647/5000000000 : ℝ)^4489 ≤ (15445240245993/50000000000000 : ℝ)^3465 := by
    have hnat : (2019167647 : ℕ)^4489*50000000000000^3465 ≤ 15445240245993^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019167647 5000000000 15445240245993 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4528301803/10000000000 : ℝ)^4489 ≤ (35830682377909/100000000000000 : ℝ)^3465 := by
    have hnat : (4528301803 : ℕ)^4489*100000000000000^3465 ≤ 35830682377909^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528301803 10000000000 35830682377909 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277281957/10000000000 : ℝ), (2019167647/5000000000 : ℝ), (4528301803/10000000000 : ℝ)] ![(3327883711567/10000000000000 : ℝ), (15445240245993/50000000000000 : ℝ), (35830682377909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277281957/10000000000 : ℝ)|^4489 ≤ (3327883711567/10000000000000 : ℝ)^3465
        have hw : |(4277281957/10000000000 : ℝ)|=(4277281957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2019167647/5000000000 : ℝ)|^4489 ≤ (15445240245993/50000000000000 : ℝ)^3465
        have hw : |(2019167647/5000000000 : ℝ)|=(2019167647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4528301803/10000000000 : ℝ)|^4489 ≤ (35830682377909/100000000000000 : ℝ)^3465
        have hw : |(4528301803/10000000000 : ℝ)|=(4528301803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s6_4 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1891946993/10000000000 : ℝ)*x 0 + (1304476881/2500000000 : ℝ)*x 1 + (543419227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1891946993/10000000000 : ℝ)^4489 ≤ (5783440402411/50000000000000 : ℝ)^3465 := by
    have hnat : (1891946993 : ℕ)^4489*50000000000000^3465 ≤ 5783440402411^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891946993 10000000000 5783440402411 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304476881/2500000000 : ℝ)^4489 ≤ (21526777418283/50000000000000 : ℝ)^3465 := by
    have hnat : (1304476881 : ℕ)^4489*50000000000000^3465 ≤ 21526777418283^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304476881 2500000000 21526777418283 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543419227/1000000000 : ℝ)^4489 ≤ (22689782173183/50000000000000 : ℝ)^3465 := by
    have hnat : (543419227 : ℕ)^4489*50000000000000^3465 ≤ 22689782173183^3465*1000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543419227 1000000000 22689782173183 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1891946993/10000000000 : ℝ), (1304476881/2500000000 : ℝ), (543419227/1000000000 : ℝ)] ![(5783440402411/50000000000000 : ℝ), (21526777418283/50000000000000 : ℝ), (22689782173183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1891946993/10000000000 : ℝ)|^4489 ≤ (5783440402411/50000000000000 : ℝ)^3465
        have hw : |(-1891946993/10000000000 : ℝ)|=(1891946993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304476881/2500000000 : ℝ)|^4489 ≤ (21526777418283/50000000000000 : ℝ)^3465
        have hw : |(1304476881/2500000000 : ℝ)|=(1304476881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543419227/1000000000 : ℝ)|^4489 ≤ (22689782173183/50000000000000 : ℝ)^3465
        have hw : |(543419227/1000000000 : ℝ)|=(543419227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s6_5 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661904923/1250000000 : ℝ)*x 0 + (-1786471637/10000000000 : ℝ)*x 1 + (2717096103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661904923/1250000000 : ℝ)^4489 ≤ (43882000845527/100000000000000 : ℝ)^3465 := by
    have hnat : (661904923 : ℕ)^4489*100000000000000^3465 ≤ 43882000845527^3465*1250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661904923 1250000000 43882000845527 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1786471637/10000000000 : ℝ)^4489 ≤ (1073843548307/10000000000000 : ℝ)^3465 := by
    have hnat : (1786471637 : ℕ)^4489*10000000000000^3465 ≤ 1073843548307^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786471637 10000000000 1073843548307 10000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717096103/5000000000 : ℝ)^4489 ≤ (22689781826987/50000000000000 : ℝ)^3465 := by
    have hnat : (2717096103 : ℕ)^4489*50000000000000^3465 ≤ 22689781826987^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717096103 5000000000 22689781826987 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661904923/1250000000 : ℝ), (-1786471637/10000000000 : ℝ), (2717096103/5000000000 : ℝ)] ![(43882000845527/100000000000000 : ℝ), (1073843548307/10000000000000 : ℝ), (22689781826987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661904923/1250000000 : ℝ)|^4489 ≤ (43882000845527/100000000000000 : ℝ)^3465
        have hw : |(661904923/1250000000 : ℝ)|=(661904923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1786471637/10000000000 : ℝ)|^4489 ≤ (1073843548307/10000000000000 : ℝ)^3465
        have hw : |(-1786471637/10000000000 : ℝ)|=(1786471637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717096103/5000000000 : ℝ)|^4489 ≤ (22689781826987/50000000000000 : ℝ)^3465
        have hw : |(2717096103/5000000000 : ℝ)|=(2717096103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s6_6 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295239313/10000000000 : ℝ)*x 0 + (1358548057/2500000000 : ℝ)*x 1 + (-223308963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295239313/10000000000 : ℝ)^4489 ≤ (43882000083263/100000000000000 : ℝ)^3465 := by
    have hnat : (5295239313 : ℕ)^4489*100000000000000^3465 ≤ 43882000083263^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295239313 10000000000 43882000083263 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358548057/2500000000 : ℝ)^4489 ≤ (2836222743249/6250000000000 : ℝ)^3465 := by
    have hnat : (1358548057 : ℕ)^4489*6250000000000^3465 ≤ 2836222743249^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358548057 2500000000 2836222743249 6250000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223308963/1250000000 : ℝ)^4489 ≤ (1342304500603/12500000000000 : ℝ)^3465 := by
    have hnat : (223308963 : ℕ)^4489*12500000000000^3465 ≤ 1342304500603^3465*1250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223308963 1250000000 1342304500603 12500000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295239313/10000000000 : ℝ), (1358548057/2500000000 : ℝ), (-223308963/1250000000 : ℝ)] ![(43882000083263/100000000000000 : ℝ), (2836222743249/6250000000000 : ℝ), (1342304500603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295239313/10000000000 : ℝ)|^4489 ≤ (43882000083263/100000000000000 : ℝ)^3465
        have hw : |(5295239313/10000000000 : ℝ)|=(5295239313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358548057/2500000000 : ℝ)|^4489 ≤ (2836222743249/6250000000000 : ℝ)^3465
        have hw : |(1358548057/2500000000 : ℝ)|=(1358548057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223308963/1250000000 : ℝ)|^4489 ≤ (1342304500603/12500000000000 : ℝ)^3465
        have hw : |(-223308963/1250000000 : ℝ)|=(223308963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s6_7 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6843757/16000000 : ℝ)*x 0 + (4525787797/10000000000 : ℝ)*x 1 + (2020434043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6843757/16000000 : ℝ)^4489 ≤ (16639752034641/50000000000000 : ℝ)^3465 := by
    have hnat : (6843757 : ℕ)^4489*50000000000000^3465 ≤ 16639752034641^3465*16000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6843757 16000000 16639752034641 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525787797/10000000000 : ℝ)^4489 ≤ (17902456712909/50000000000000 : ℝ)^3465 := by
    have hnat : (4525787797 : ℕ)^4489*50000000000000^3465 ≤ 17902456712909^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525787797 10000000000 17902456712909 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020434043/5000000000 : ℝ)^4489 ≤ (3091558249757/10000000000000 : ℝ)^3465 := by
    have hnat : (2020434043 : ℕ)^4489*10000000000000^3465 ≤ 3091558249757^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020434043 5000000000 3091558249757 10000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6843757/16000000 : ℝ), (4525787797/10000000000 : ℝ), (2020434043/5000000000 : ℝ)] ![(16639752034641/50000000000000 : ℝ), (17902456712909/50000000000000 : ℝ), (3091558249757/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6843757/16000000 : ℝ)|^4489 ≤ (16639752034641/50000000000000 : ℝ)^3465
        have hw : |(6843757/16000000 : ℝ)|=(6843757/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525787797/10000000000 : ℝ)|^4489 ≤ (17902456712909/50000000000000 : ℝ)^3465
        have hw : |(4525787797/10000000000 : ℝ)|=(4525787797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2020434043/5000000000 : ℝ)|^4489 ≤ (3091558249757/10000000000000 : ℝ)^3465
        have hw : |(2020434043/5000000000 : ℝ)|=(2020434043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1496_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10853/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10851/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10851/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10851/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10851/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10851/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10851/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10851/100000 : ℝ) ^ (4487/1024 : ℝ) ≤ (29686346425467/500000000000000000 : ℝ) := by
    have hpowers : (10851/100000 : ℝ)^4487 ≤ (29686346425467/500000000000000000 : ℝ)^1024 := by
      have hnat : (10851 : ℕ)^4487*500000000000000000^1024 ≤ 29686346425467^1024*100000^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10851 100000 29686346425467 500000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10851/100000 : ℝ)) (X := (29686346425467/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4487/1024 : ℝ) ≤ (2816496779067197/10000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4487 ≤ (2816496779067197/10000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4487*10000000000000000000^1024 ≤ 2816496779067197^1024*2500^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 2816496779067197 10000000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (2816496779067197/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250029686346425467/250000000000000000 : ℝ) ≤ (5000135491089251/5000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (250029686346425467/250000000000000000 : ℝ)^1024 ≤ (5000135491089251/5000000000000000 : ℝ)^4487 := by
      have hnat : (250029686346425467 : ℕ)^1024*5000000000000000^4487 ≤ 5000135491089251^4487*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250029686346425467 250000000000000000 5000135491089251 5000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000135491089251/5000000000000000 : ℝ)) (X := (250029686346425467/250000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003410223707576537/10000000000000000000 : ℝ) ≤ (625048635079393/625000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (10003410223707576537/10000000000000000000 : ℝ)^1024 ≤ (625048635079393/625000000000000 : ℝ)^4487 := by
      have hnat : (10003410223707576537 : ℕ)^1024*625000000000000^4487 ≤ 625048635079393^4487*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003410223707576537 10000000000000000000 625048635079393 625000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625048635079393/625000000000000 : ℝ)) (X := (10003410223707576537/10000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002816496779067197/5000000000000000000 : ℝ) ≤ (5000642670181037/5000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (5002816496779067197/5000000000000000000 : ℝ)^1024 ≤ (5000642670181037/5000000000000000 : ℝ)^4487 := by
      have hnat : (5002816496779067197 : ℕ)^1024*5000000000000000^4487 ≤ 5000642670181037^4487*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002816496779067197 5000000000000000000 5000642670181037 5000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000642670181037/5000000000000000 : ℝ)) (X := (5002816496779067197/5000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(29686346425467/500000000000000000 : ℝ) ≤ ((7713374595975724331/7715000000000000000 : ℝ)+2*(84529848631/77150000000000 : ℝ)*(10851/100000 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (7713374595975724331/7715000000000000000 : ℝ)+2*(84529848631/77150000000000 : ℝ)*(10851/100000 : ℝ)=(5000135491089251/5000000000000000 : ℝ) by norm_num, show 1+2*(29686346425467/500000000000000000 : ℝ)=(250029686346425467/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2816496779067197/10000000000000000000 : ℝ)+(29686346425467/500000000000000000 : ℝ) ≤ ((7713374595975724331/7715000000000000000 : ℝ)+(84529848631/77150000000000 : ℝ)*((387/2500 : ℝ)+(10851/100000 : ℝ)))^(4487/1024 : ℝ) := by
    rw [show (7713374595975724331/7715000000000000000 : ℝ)+(84529848631/77150000000000 : ℝ)*((387/2500 : ℝ)+(10851/100000 : ℝ))=(625048635079393/625000000000000 : ℝ) by norm_num, show 1+(2816496779067197/10000000000000000000 : ℝ)+(29686346425467/500000000000000000 : ℝ)=(10003410223707576537/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2816496779067197/10000000000000000000 : ℝ) ≤ ((7713374595975724331/7715000000000000000 : ℝ)+2*(84529848631/77150000000000 : ℝ)*(387/2500 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (7713374595975724331/7715000000000000000 : ℝ)+2*(84529848631/77150000000000 : ℝ)*(387/2500 : ℝ)=(5000642670181037/5000000000000000 : ℝ) by norm_num, show 1+2*(2816496779067197/10000000000000000000 : ℝ)=(5002816496779067197/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7713374595975724331/7715000000000000000 : ℝ)*(X 1 0+X 2 0)+(84529848631/77150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (7713374595975724331/7715000000000000000 : ℝ)) (alpha := (84529848631/77150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7713374595975724331/7715000000000000000 : ℝ)*(X 0 1+X 2 1)+(84529848631/77150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (7713374595975724331/7715000000000000000 : ℝ)) (alpha := (84529848631/77150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7713374595975724331/7715000000000000000 : ℝ)*(X 0 2+X 1 2)+(84529848631/77150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (7713374595975724331/7715000000000000000 : ℝ)) (alpha := (84529848631/77150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1891917437/10000000000 : ℝ)*X 0 0+(10615863/19531250 : ℝ)*X 0 1+(5216786127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352464629/10000000000 : ℝ)*X 1 0+(-250484719/1250000000 : ℝ)*X 1 1+(326049133/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352464629/10000000000 : ℝ)*X 2 0+(5216786127/10000000000 : ℝ)*X 2 1+(-250484719/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4277281957/10000000000 : ℝ)*X 0 0+(2019167647/5000000000 : ℝ)*X 0 1+(4528301803/10000000000 : ℝ)*X 0 2+(4277281957/10000000000 : ℝ)*X 1 0+(2019167647/5000000000 : ℝ)*X 1 1+(4528301803/10000000000 : ℝ)*X 1 2+(4277281957/10000000000 : ℝ)*X 2 0+(2019167647/5000000000 : ℝ)*X 2 1+(4528301803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1891946993/10000000000 : ℝ)*X 0 0+(1304476881/2500000000 : ℝ)*X 0 1+(543419227/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661904923/1250000000 : ℝ)*X 1 0+(-1786471637/10000000000 : ℝ)*X 1 1+(2717096103/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295239313/10000000000 : ℝ)*X 2 0+(1358548057/2500000000 : ℝ)*X 2 1+(-223308963/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((6843757/16000000 : ℝ)*X 0 0+(4525787797/10000000000 : ℝ)*X 0 1+(2020434043/5000000000 : ℝ)*X 0 2+(6843757/16000000 : ℝ)*X 1 0+(4525787797/10000000000 : ℝ)*X 1 1+(2020434043/5000000000 : ℝ)*X 1 2+(6843757/16000000 : ℝ)*X 2 0+(4525787797/10000000000 : ℝ)*X 2 1+(2020434043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222077436032236971656354793/96437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411348251/100000000000000 : ℝ)*(base19) + (383841339/100000000000000 : ℝ)*(base23) + (7361489/50000000000000 : ℝ)*(lower2) + (58202691/100000000000000 : ℝ)*(upper3) + (37462991/100000000000000 : ℝ)*(upper5) + (827110698311633/25000000000000 : ℝ)*(major0) + (827110698311633/25000000000000 : ℝ)*(major1) + (827110698311633/25000000000000 : ℝ)*(major2) + (571989680343637/12500000000000 : ℝ)*(sp0) + (571990428187059/12500000000000 : ℝ)*(sp1) + (571990431625423/12500000000000 : ℝ)*(sp2) + (510239644248529/25000000000000 : ℝ)*(sp3) + (6394095627/100000000000000 : ℝ)*(sp4) + (773973453/25000000000000 : ℝ)*(sp7) + (255120209110991/12500000000000 : ℝ)*(f.failure) + (1143980959211181/25000000000000 : ℝ)*(f.sum) + (43716581373849/7715000000000000000000000000 : ℝ)*base65 + (892178986673742523/192875000000000000000000000000000 : ℝ)*base67 + (2159852340897492523/192875000000000000000000000000000 : ℝ)*base69 + (2191891397730742523/192875000000000000000000000000000 : ℝ)*base71 + (6837478142319/1928750000000000000000000000 : ℝ)*base74 + (1001879843877242523/192875000000000000000000000000000 : ℝ)*base75 + (3439211004622742523/192875000000000000000000000000000 : ℝ)*base77 + (1157688002937242523/192875000000000000000000000000000 : ℝ)*base79 + (6383503482451/1928750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (255921/156250000000000000000 : ℝ)*base90 + (255921/156250000000000000000 : ℝ)*base92 + (255921/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (630333732468713913662429133/96437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (917604793/100000000000000 : ℝ)*(base19) + (885407743/100000000000000 : ℝ)*(base23) + (283022721/100000000000000 : ℝ)*(lower1) + (85564859/100000000000000 : ℝ)*(upper3) + (21248241/100000000000000 : ℝ)*(lower4) + (41600017/50000000000000 : ℝ)*(upper5) + (835713972437673/25000000000000 : ℝ)*(major0) + (835713972437673/25000000000000 : ℝ)*(major1) + (835713972437673/25000000000000 : ℝ)*(major2) + (955934597/100000000000000 : ℝ)*(sp1) + (2311760311535459/50000000000000 : ℝ)*(sp4) + (577939843691441/12500000000000 : ℝ)*(sp5) + (184940789506527/4000000000000 : ℝ)*(sp6) + (515547734639373/25000000000000 : ℝ)*(sp7) + (515547734639373/25000000000000 : ℝ)*(f.failure) + (2311760311535459/50000000000000 : ℝ)*(f.sum) + (11458570840607/3857500000000000000000000000 : ℝ)*base65 + (1547752766404921763/192875000000000000000000000000000 : ℝ)*base67 + (993971606318921763/192875000000000000000000000000000 : ℝ)*base69 + (2222649662194046763/192875000000000000000000000000000 : ℝ)*base71 + (1685053647211/1928750000000000000000000000 : ℝ)*base73 + (173030544952421763/192875000000000000000000000000000 : ℝ)*base75 + (1389963827577796763/192875000000000000000000000000000 : ℝ)*base77 + (882523637989421763/192875000000000000000000000000000 : ℝ)*base79 + (8904249544847/964375000000000000000000000 : ℝ)*base82 + (903837/312500000000000000000 : ℝ)*base89 + (903837/312500000000000000000 : ℝ)*base91 + (903837/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1496_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1496_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1496_box_0 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418846279/2500000000 : ℝ)*x 0 + (2702282659/5000000000 : ℝ)*x 1 + (135114061/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418846279/2500000000 : ℝ)^4489 ≤ (4940715246763/50000000000000 : ℝ)^3465 := by
    have hnat : (418846279 : ℕ)^4489*50000000000000^3465 ≤ 4940715246763^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418846279 2500000000 4940715246763 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702282659/5000000000 : ℝ)^4489 ≤ (45059300286401/100000000000000 : ℝ)^3465 := by
    have hnat : (2702282659 : ℕ)^4489*100000000000000^3465 ≤ 45059300286401^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702282659 5000000000 45059300286401 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135114061/250000000 : ℝ)^4489 ≤ (4505926920069/10000000000000 : ℝ)^3465 := by
    have hnat : (135114061 : ℕ)^4489*10000000000000^3465 ≤ 4505926920069^3465*250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135114061 250000000 4505926920069 10000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418846279/2500000000 : ℝ), (2702282659/5000000000 : ℝ), (135114061/250000000 : ℝ)] ![(4940715246763/50000000000000 : ℝ), (45059300286401/100000000000000 : ℝ), (4505926920069/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418846279/2500000000 : ℝ)|^4489 ≤ (4940715246763/50000000000000 : ℝ)^3465
        have hw : |(-418846279/2500000000 : ℝ)|=(418846279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702282659/5000000000 : ℝ)|^4489 ≤ (45059300286401/100000000000000 : ℝ)^3465
        have hw : |(2702282659/5000000000 : ℝ)|=(2702282659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135114061/250000000 : ℝ)|^4489 ≤ (4505926920069/10000000000000 : ℝ)^3465
        have hw : |(135114061/250000000 : ℝ)|=(135114061/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_1 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635269287/5000000000 : ℝ)*x 0 + (-1861173219/10000000000 : ℝ)*x 1 + (1351140913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635269287/5000000000 : ℝ)^4489 ≤ (10904248269339/25000000000000 : ℝ)^3465 := by
    have hnat : (2635269287 : ℕ)^4489*25000000000000^3465 ≤ 10904248269339^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635269287 5000000000 10904248269339 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1861173219/10000000000 : ℝ)^4489 ≤ (5661862307919/50000000000000 : ℝ)^3465 := by
    have hnat : (1861173219 : ℕ)^4489*50000000000000^3465 ≤ 5661862307919^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861173219 10000000000 5661862307919 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351140913/2500000000 : ℝ)^4489 ≤ (11264820572921/25000000000000 : ℝ)^3465 := by
    have hnat : (1351140913 : ℕ)^4489*25000000000000^3465 ≤ 11264820572921^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351140913 2500000000 11264820572921 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635269287/5000000000 : ℝ), (-1861173219/10000000000 : ℝ), (1351140913/2500000000 : ℝ)] ![(10904248269339/25000000000000 : ℝ), (5661862307919/50000000000000 : ℝ), (11264820572921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635269287/5000000000 : ℝ)|^4489 ≤ (10904248269339/25000000000000 : ℝ)^3465
        have hw : |(2635269287/5000000000 : ℝ)|=(2635269287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1861173219/10000000000 : ℝ)|^4489 ≤ (5661862307919/50000000000000 : ℝ)^3465
        have hw : |(-1861173219/10000000000 : ℝ)|=(1861173219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351140913/2500000000 : ℝ)|^4489 ≤ (11264820572921/25000000000000 : ℝ)^3465
        have hw : |(1351140913/2500000000 : ℝ)|=(1351140913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_2 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270539163/10000000000 : ℝ)*x 0 + (1080912813/2000000000 : ℝ)*x 1 + (-1861171851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270539163/10000000000 : ℝ)^4489 ≤ (10904249848049/25000000000000 : ℝ)^3465 := by
    have hnat : (5270539163 : ℕ)^4489*25000000000000^3465 ≤ 10904249848049^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270539163 10000000000 10904249848049 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080912813/2000000000 : ℝ)^4489 ≤ (45059286752559/100000000000000 : ℝ)^3465 := by
    have hnat : (1080912813 : ℕ)^4489*100000000000000^3465 ≤ 45059286752559^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080912813 2000000000 45059286752559 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1861171851/10000000000 : ℝ)^4489 ≤ (5661856916477/50000000000000 : ℝ)^3465 := by
    have hnat : (1861171851 : ℕ)^4489*50000000000000^3465 ≤ 5661856916477^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861171851 10000000000 5661856916477 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270539163/10000000000 : ℝ), (1080912813/2000000000 : ℝ), (-1861171851/10000000000 : ℝ)] ![(10904249848049/25000000000000 : ℝ), (45059286752559/100000000000000 : ℝ), (5661856916477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270539163/10000000000 : ℝ)|^4489 ≤ (10904249848049/25000000000000 : ℝ)^3465
        have hw : |(5270539163/10000000000 : ℝ)|=(5270539163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080912813/2000000000 : ℝ)|^4489 ≤ (45059286752559/100000000000000 : ℝ)^3465
        have hw : |(1080912813/2000000000 : ℝ)|=(1080912813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1861171851/10000000000 : ℝ)|^4489 ≤ (5661856916477/50000000000000 : ℝ)^3465
        have hw : |(-1861171851/10000000000 : ℝ)|=(1861171851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_3 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2240545939/5000000000 : ℝ)*x 0 + (4182464541/10000000000 : ℝ)*x 1 + (4182465407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240545939/5000000000 : ℝ)^4489 ≤ (35347480967583/100000000000000 : ℝ)^3465 := by
    have hnat : (2240545939 : ℕ)^4489*100000000000000^3465 ≤ 35347480967583^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240545939 5000000000 35347480967583 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4182464541/10000000000 : ℝ)^4489 ≤ (32326255168853/100000000000000 : ℝ)^3465 := by
    have hnat : (4182464541 : ℕ)^4489*100000000000000^3465 ≤ 32326255168853^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182464541 10000000000 32326255168853 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4182465407/10000000000 : ℝ)^4489 ≤ (32326263840217/100000000000000 : ℝ)^3465 := by
    have hnat : (4182465407 : ℕ)^4489*100000000000000^3465 ≤ 32326263840217^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182465407 10000000000 32326263840217 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240545939/5000000000 : ℝ), (4182464541/10000000000 : ℝ), (4182465407/10000000000 : ℝ)] ![(35347480967583/100000000000000 : ℝ), (32326255168853/100000000000000 : ℝ), (32326263840217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240545939/5000000000 : ℝ)|^4489 ≤ (35347480967583/100000000000000 : ℝ)^3465
        have hw : |(2240545939/5000000000 : ℝ)|=(2240545939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4182464541/10000000000 : ℝ)|^4489 ≤ (32326255168853/100000000000000 : ℝ)^3465
        have hw : |(4182464541/10000000000 : ℝ)|=(4182464541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4182465407/10000000000 : ℝ)|^4489 ≤ (32326263840217/100000000000000 : ℝ)^3465
        have hw : |(4182465407/10000000000 : ℝ)|=(4182465407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_4 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-528474899/2500000000 : ℝ)*x 0 + (5243071101/10000000000 : ℝ)*x 1 + (2621535477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528474899/2500000000 : ℝ)^4489 ≤ (6677267423181/50000000000000 : ℝ)^3465 := by
    have hnat : (528474899 : ℕ)^4489*50000000000000^3465 ≤ 6677267423181^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528474899 2500000000 6677267423181 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243071101/10000000000 : ℝ)^4489 ≤ (8664546670817/20000000000000 : ℝ)^3465 := by
    have hnat : (5243071101 : ℕ)^4489*20000000000000^3465 ≤ 8664546670817^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243071101 10000000000 8664546670817 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621535477/5000000000 : ℝ)^4489 ≤ (43322731780487/100000000000000 : ℝ)^3465 := by
    have hnat : (2621535477 : ℕ)^4489*100000000000000^3465 ≤ 43322731780487^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621535477 5000000000 43322731780487 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528474899/2500000000 : ℝ), (5243071101/10000000000 : ℝ), (2621535477/5000000000 : ℝ)] ![(6677267423181/50000000000000 : ℝ), (8664546670817/20000000000000 : ℝ), (43322731780487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528474899/2500000000 : ℝ)|^4489 ≤ (6677267423181/50000000000000 : ℝ)^3465
        have hw : |(-528474899/2500000000 : ℝ)|=(528474899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243071101/10000000000 : ℝ)|^4489 ≤ (8664546670817/20000000000000 : ℝ)^3465
        have hw : |(5243071101/10000000000 : ℝ)|=(5243071101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621535477/5000000000 : ℝ)|^4489 ≤ (43322731780487/100000000000000 : ℝ)^3465
        have hw : |(2621535477/5000000000 : ℝ)|=(2621535477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_5 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383113947/10000000000 : ℝ)*x 0 + (-1927534259/10000000000 : ℝ)*x 1 + (1048614209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383113947/10000000000 : ℝ)^4489 ≤ (2241386840213/5000000000000 : ℝ)^3465 := by
    have hnat : (5383113947 : ℕ)^4489*5000000000000^3465 ≤ 2241386840213^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383113947 10000000000 2241386840213 5000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927534259/10000000000 : ℝ)^4489 ≤ (11849530433537/100000000000000 : ℝ)^3465 := by
    have hnat : (1927534259 : ℕ)^4489*100000000000000^3465 ≤ 11849530433537^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927534259 10000000000 11849530433537 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048614209/2000000000 : ℝ)^4489 ≤ (43322732754619/100000000000000 : ℝ)^3465 := by
    have hnat : (1048614209 : ℕ)^4489*100000000000000^3465 ≤ 43322732754619^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048614209 2000000000 43322732754619 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383113947/10000000000 : ℝ), (-1927534259/10000000000 : ℝ), (1048614209/2000000000 : ℝ)] ![(2241386840213/5000000000000 : ℝ), (11849530433537/100000000000000 : ℝ), (43322732754619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383113947/10000000000 : ℝ)|^4489 ≤ (2241386840213/5000000000000 : ℝ)^3465
        have hw : |(5383113947/10000000000 : ℝ)|=(5383113947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927534259/10000000000 : ℝ)|^4489 ≤ (11849530433537/100000000000000 : ℝ)^3465
        have hw : |(-1927534259/10000000000 : ℝ)|=(1927534259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048614209/2000000000 : ℝ)|^4489 ≤ (43322732754619/100000000000000 : ℝ)^3465
        have hw : |(1048614209/2000000000 : ℝ)|=(1048614209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_6 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691557057/5000000000 : ℝ)*x 0 + (5243071197/10000000000 : ℝ)*x 1 + (-481883457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691557057/5000000000 : ℝ)^4489 ≤ (22413869302967/50000000000000 : ℝ)^3465 := by
    have hnat : (2691557057 : ℕ)^4489*50000000000000^3465 ≤ 22413869302967^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691557057 5000000000 22413869302967 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243071197/10000000000 : ℝ)^4489 ≤ (43322734381741/100000000000000 : ℝ)^3465 := by
    have hnat : (5243071197 : ℕ)^4489*100000000000000^3465 ≤ 43322734381741^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243071197 10000000000 43322734381741 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481883457/2500000000 : ℝ)^4489 ≤ (5924763500471/50000000000000 : ℝ)^3465 := by
    have hnat : (481883457 : ℕ)^4489*50000000000000^3465 ≤ 5924763500471^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481883457 2500000000 5924763500471 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691557057/5000000000 : ℝ), (5243071197/10000000000 : ℝ), (-481883457/2500000000 : ℝ)] ![(22413869302967/50000000000000 : ℝ), (43322734381741/100000000000000 : ℝ), (5924763500471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691557057/5000000000 : ℝ)|^4489 ≤ (22413869302967/50000000000000 : ℝ)^3465
        have hw : |(2691557057/5000000000 : ℝ)|=(2691557057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243071197/10000000000 : ℝ)|^4489 ≤ (43322734381741/100000000000000 : ℝ)^3465
        have hw : |(5243071197/10000000000 : ℝ)|=(5243071197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-481883457/2500000000 : ℝ)|^4489 ≤ (5924763500471/50000000000000 : ℝ)^3465
        have hw : |(-481883457/2500000000 : ℝ)|=(481883457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_7 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (203556687/500000000 : ℝ)*x 0 + (877461477/2000000000 : ℝ)*x 1 + (2193653947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203556687/500000000 : ℝ)^4489 ≤ (31215898676487/100000000000000 : ℝ)^3465 := by
    have hnat : (203556687 : ℕ)^4489*100000000000000^3465 ≤ 31215898676487^3465*500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203556687 500000000 31215898676487 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877461477/2000000000 : ℝ)^4489 ≤ (6878409613719/20000000000000 : ℝ)^3465 := by
    have hnat : (877461477 : ℕ)^4489*20000000000000^3465 ≤ 6878409613719^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877461477 2000000000 6878409613719 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193653947/5000000000 : ℝ)^4489 ≤ (8598013309451/25000000000000 : ℝ)^3465 := by
    have hnat : (2193653947 : ℕ)^4489*25000000000000^3465 ≤ 8598013309451^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193653947 5000000000 8598013309451 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(203556687/500000000 : ℝ), (877461477/2000000000 : ℝ), (2193653947/5000000000 : ℝ)] ![(31215898676487/100000000000000 : ℝ), (6878409613719/20000000000000 : ℝ), (8598013309451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(203556687/500000000 : ℝ)|^4489 ≤ (31215898676487/100000000000000 : ℝ)^3465
        have hw : |(203556687/500000000 : ℝ)|=(203556687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(877461477/2000000000 : ℝ)|^4489 ≤ (6878409613719/20000000000000 : ℝ)^3465
        have hw : |(877461477/2000000000 : ℝ)|=(877461477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2193653947/5000000000 : ℝ)|^4489 ≤ (8598013309451/25000000000000 : ℝ)^3465
        have hw : |(2193653947/5000000000 : ℝ)|=(2193653947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_8 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1010659477/5000000000 : ℝ)*x 0 + (2565056007/5000000000 : ℝ)*x 1 + (5425063681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010659477/5000000000 : ℝ)^4489 ≤ (1260176596121/10000000000000 : ℝ)^3465 := by
    have hnat : (1010659477 : ℕ)^4489*10000000000000^3465 ≤ 1260176596121^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010659477 5000000000 1260176596121 10000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565056007/5000000000 : ℝ)^4489 ≤ (42117403851013/100000000000000 : ℝ)^3465 := by
    have hnat : (2565056007 : ℕ)^4489*100000000000000^3465 ≤ 42117403851013^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565056007 5000000000 42117403851013 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425063681/10000000000 : ℝ)^4489 ≤ (45280830174861/100000000000000 : ℝ)^3465 := by
    have hnat : (5425063681 : ℕ)^4489*100000000000000^3465 ≤ 45280830174861^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425063681 10000000000 45280830174861 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1010659477/5000000000 : ℝ), (2565056007/5000000000 : ℝ), (5425063681/10000000000 : ℝ)] ![(1260176596121/10000000000000 : ℝ), (42117403851013/100000000000000 : ℝ), (45280830174861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1010659477/5000000000 : ℝ)|^4489 ≤ (1260176596121/10000000000000 : ℝ)^3465
        have hw : |(-1010659477/5000000000 : ℝ)|=(1010659477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565056007/5000000000 : ℝ)|^4489 ≤ (42117403851013/100000000000000 : ℝ)^3465
        have hw : |(2565056007/5000000000 : ℝ)|=(2565056007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425063681/10000000000 : ℝ)|^4489 ≤ (45280830174861/100000000000000 : ℝ)^3465
        have hw : |(5425063681/10000000000 : ℝ)|=(5425063681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_9 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210249709/400000000 : ℝ)*x 0 + (-1852498089/10000000000 : ℝ)*x 1 + (1085012603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210249709/400000000 : ℝ)^4489 ≤ (169780408539/390625000000 : ℝ)^3465 := by
    have hnat : (210249709 : ℕ)^4489*390625000000^3465 ≤ 169780408539^3465*400000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210249709 400000000 169780408539 390625000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1852498089/10000000000 : ℝ)^4489 ≤ (1406924053723/12500000000000 : ℝ)^3465 := by
    have hnat : (1852498089 : ℕ)^4489*12500000000000^3465 ≤ 1406924053723^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852498089 10000000000 1406924053723 12500000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085012603/2000000000 : ℝ)^4489 ≤ (45280822973243/100000000000000 : ℝ)^3465 := by
    have hnat : (1085012603 : ℕ)^4489*100000000000000^3465 ≤ 45280822973243^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085012603 2000000000 45280822973243 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210249709/400000000 : ℝ), (-1852498089/10000000000 : ℝ), (1085012603/2000000000 : ℝ)] ![(169780408539/390625000000 : ℝ), (1406924053723/12500000000000 : ℝ), (45280822973243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210249709/400000000 : ℝ)|^4489 ≤ (169780408539/390625000000 : ℝ)^3465
        have hw : |(210249709/400000000 : ℝ)|=(210249709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1852498089/10000000000 : ℝ)|^4489 ≤ (1406924053723/12500000000000 : ℝ)^3465
        have hw : |(-1852498089/10000000000 : ℝ)|=(1852498089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085012603/2000000000 : ℝ)|^4489 ≤ (45280822973243/100000000000000 : ℝ)^3465
        have hw : |(1085012603/2000000000 : ℝ)|=(1085012603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_10 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628120713/5000000000 : ℝ)*x 0 + (2712532519/5000000000 : ℝ)*x 1 + (-1852497079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628120713/5000000000 : ℝ)^4489 ≤ (43463770670201/100000000000000 : ℝ)^3465 := by
    have hnat : (2628120713 : ℕ)^4489*100000000000000^3465 ≤ 43463770670201^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628120713 5000000000 43463770670201 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712532519/5000000000 : ℝ)^4489 ≤ (45280844848431/100000000000000 : ℝ)^3465 := by
    have hnat : (2712532519 : ℕ)^4489*100000000000000^3465 ≤ 45280844848431^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712532519 5000000000 45280844848431 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1852497079/10000000000 : ℝ)^4489 ≤ (11255384479721/100000000000000 : ℝ)^3465 := by
    have hnat : (1852497079 : ℕ)^4489*100000000000000^3465 ≤ 11255384479721^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852497079 10000000000 11255384479721 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628120713/5000000000 : ℝ), (2712532519/5000000000 : ℝ), (-1852497079/10000000000 : ℝ)] ![(43463770670201/100000000000000 : ℝ), (45280844848431/100000000000000 : ℝ), (11255384479721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628120713/5000000000 : ℝ)|^4489 ≤ (43463770670201/100000000000000 : ℝ)^3465
        have hw : |(2628120713/5000000000 : ℝ)|=(2628120713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712532519/5000000000 : ℝ)|^4489 ≤ (45280844848431/100000000000000 : ℝ)^3465
        have hw : |(2712532519/5000000000 : ℝ)|=(2712532519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1852497079/10000000000 : ℝ)|^4489 ≤ (11255384479721/100000000000000 : ℝ)^3465
        have hw : |(-1852497079/10000000000 : ℝ)|=(1852497079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_11 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (566497149/1250000000 : ℝ)*x 0 + (4156431469/10000000000 : ℝ)*x 1 + (4156430547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566497149/1250000000 : ℝ)^4489 ≤ (7173672659021/20000000000000 : ℝ)^3465 := by
    have hnat : (566497149 : ℕ)^4489*20000000000000^3465 ≤ 7173672659021^3465*1250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566497149 1250000000 7173672659021 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4156431469/10000000000 : ℝ)^4489 ≤ (32065822949419/100000000000000 : ℝ)^3465 := by
    have hnat : (4156431469 : ℕ)^4489*100000000000000^3465 ≤ 32065822949419^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156431469 10000000000 32065822949419 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156430547/10000000000 : ℝ)^4489 ≤ (32065813734341/100000000000000 : ℝ)^3465 := by
    have hnat : (4156430547 : ℕ)^4489*100000000000000^3465 ≤ 32065813734341^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156430547 10000000000 32065813734341 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(566497149/1250000000 : ℝ), (4156431469/10000000000 : ℝ), (4156430547/10000000000 : ℝ)] ![(7173672659021/20000000000000 : ℝ), (32065822949419/100000000000000 : ℝ), (32065813734341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(566497149/1250000000 : ℝ)|^4489 ≤ (7173672659021/20000000000000 : ℝ)^3465
        have hw : |(566497149/1250000000 : ℝ)|=(566497149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4156431469/10000000000 : ℝ)|^4489 ≤ (32065822949419/100000000000000 : ℝ)^3465
        have hw : |(4156431469/10000000000 : ℝ)|=(4156431469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156430547/10000000000 : ℝ)|^4489 ≤ (32065813734341/100000000000000 : ℝ)^3465
        have hw : |(4156430547/10000000000 : ℝ)|=(4156430547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_12 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1768003559/10000000000 : ℝ)*x 0 + (5513835783/10000000000 : ℝ)*x 1 + (209122379/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1768003559/10000000000 : ℝ)^4489 ≤ (662177362673/6250000000000 : ℝ)^3465 := by
    have hnat : (1768003559 : ℕ)^4489*6250000000000^3465 ≤ 662177362673^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768003559 10000000000 662177362673 6250000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513835783/10000000000 : ℝ)^4489 ≤ (46243056481319/100000000000000 : ℝ)^3465 := by
    have hnat : (5513835783 : ℕ)^4489*100000000000000^3465 ≤ 46243056481319^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513835783 10000000000 46243056481319 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209122379/400000000 : ℝ)^4489 ≤ (21581052851843/50000000000000 : ℝ)^3465 := by
    have hnat : (209122379 : ℕ)^4489*50000000000000^3465 ≤ 21581052851843^3465*400000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209122379 400000000 21581052851843 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1768003559/10000000000 : ℝ), (5513835783/10000000000 : ℝ), (209122379/400000000 : ℝ)] ![(662177362673/6250000000000 : ℝ), (46243056481319/100000000000000 : ℝ), (21581052851843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1768003559/10000000000 : ℝ)|^4489 ≤ (662177362673/6250000000000 : ℝ)^3465
        have hw : |(-1768003559/10000000000 : ℝ)|=(1768003559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513835783/10000000000 : ℝ)|^4489 ≤ (46243056481319/100000000000000 : ℝ)^3465
        have hw : |(5513835783/10000000000 : ℝ)|=(5513835783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209122379/400000000 : ℝ)|^4489 ≤ (21581052851843/50000000000000 : ℝ)^3465
        have hw : |(209122379/400000000 : ℝ)|=(209122379/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_13 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393577667/10000000000 : ℝ)*x 0 + (-38670431/200000000 : ℝ)*x 1 + (1045611913/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393577667/10000000000 : ℝ)^4489 ≤ (561758208467/1250000000000 : ℝ)^3465 := by
    have hnat : (5393577667 : ℕ)^4489*1250000000000^3465 ≤ 561758208467^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393577667 10000000000 561758208467 1250000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38670431/200000000 : ℝ)^4489 ≤ (5948618321477/50000000000000 : ℝ)^3465 := by
    have hnat : (38670431 : ℕ)^4489*50000000000000^3465 ≤ 5948618321477^3465*200000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38670431 200000000 5948618321477 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045611913/2000000000 : ℝ)^4489 ≤ (21581053333149/50000000000000 : ℝ)^3465 := by
    have hnat : (1045611913 : ℕ)^4489*50000000000000^3465 ≤ 21581053333149^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045611913 2000000000 21581053333149 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393577667/10000000000 : ℝ), (-38670431/200000000 : ℝ), (1045611913/2000000000 : ℝ)] ![(561758208467/1250000000000 : ℝ), (5948618321477/50000000000000 : ℝ), (21581053333149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393577667/10000000000 : ℝ)|^4489 ≤ (561758208467/1250000000000 : ℝ)^3465
        have hw : |(5393577667/10000000000 : ℝ)|=(5393577667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38670431/200000000 : ℝ)|^4489 ≤ (5948618321477/50000000000000 : ℝ)^3465
        have hw : |(-38670431/200000000 : ℝ)|=(38670431/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045611913/2000000000 : ℝ)|^4489 ≤ (21581053333149/50000000000000 : ℝ)^3465
        have hw : |(1045611913/2000000000 : ℝ)|=(1045611913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_14 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393577837/10000000000 : ℝ)*x 0 + (163376853/312500000 : ℝ)*x 1 + (-1933521681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393577837/10000000000 : ℝ)^4489 ≤ (11235164628113/25000000000000 : ℝ)^3465 := by
    have hnat : (5393577837 : ℕ)^4489*25000000000000^3465 ≤ 11235164628113^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393577837 10000000000 11235164628113 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163376853/312500000 : ℝ)^4489 ≤ (43162103789159/100000000000000 : ℝ)^3465 := by
    have hnat : (163376853 : ℕ)^4489*100000000000000^3465 ≤ 43162103789159^3465*312500000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163376853 312500000 43162103789159 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1933521681/10000000000 : ℝ)^4489 ≤ (11897237687229/100000000000000 : ℝ)^3465 := by
    have hnat : (1933521681 : ℕ)^4489*100000000000000^3465 ≤ 11897237687229^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933521681 10000000000 11897237687229 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393577837/10000000000 : ℝ), (163376853/312500000 : ℝ), (-1933521681/10000000000 : ℝ)] ![(11235164628113/25000000000000 : ℝ), (43162103789159/100000000000000 : ℝ), (11897237687229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393577837/10000000000 : ℝ)|^4489 ≤ (11235164628113/25000000000000 : ℝ)^3465
        have hw : |(5393577837/10000000000 : ℝ)|=(5393577837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163376853/312500000 : ℝ)|^4489 ≤ (43162103789159/100000000000000 : ℝ)^3465
        have hw : |(163376853/312500000 : ℝ)|=(163376853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1933521681/10000000000 : ℝ)|^4489 ≤ (11897237687229/100000000000000 : ℝ)^3465
        have hw : |(-1933521681/10000000000 : ℝ)|=(1933521681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_box_15 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4032165943/10000000000 : ℝ)*x 0 + (2203163079/5000000000 : ℝ)*x 1 + (550790833/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4032165943/10000000000 : ℝ)^4489 ≤ (15414678366653/50000000000000 : ℝ)^3465 := by
    have hnat : (4032165943 : ℕ)^4489*50000000000000^3465 ≤ 15414678366653^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032165943 10000000000 15414678366653 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203163079/5000000000 : ℝ)^4489 ≤ (34585319049979/100000000000000 : ℝ)^3465 := by
    have hnat : (2203163079 : ℕ)^4489*100000000000000^3465 ≤ 34585319049979^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203163079 5000000000 34585319049979 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550790833/1250000000 : ℝ)^4489 ≤ (6917064839059/20000000000000 : ℝ)^3465 := by
    have hnat : (550790833 : ℕ)^4489*20000000000000^3465 ≤ 6917064839059^3465*1250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550790833 1250000000 6917064839059 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4032165943/10000000000 : ℝ), (2203163079/5000000000 : ℝ), (550790833/1250000000 : ℝ)] ![(15414678366653/50000000000000 : ℝ), (34585319049979/100000000000000 : ℝ), (6917064839059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4032165943/10000000000 : ℝ)|^4489 ≤ (15414678366653/50000000000000 : ℝ)^3465
        have hw : |(4032165943/10000000000 : ℝ)|=(4032165943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2203163079/5000000000 : ℝ)|^4489 ≤ (34585319049979/100000000000000 : ℝ)^3465
        have hw : |(2203163079/5000000000 : ℝ)|=(2203163079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550790833/1250000000 : ℝ)|^4489 ≤ (6917064839059/20000000000000 : ℝ)^3465
        have hw : |(550790833/1250000000 : ℝ)|=(550790833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1496_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63719/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58553/100000 : ℝ) ∧ (40073/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42949/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10853/100000 : ℝ) ^ (4487/1024 : ℝ) ≤ (29710329698283/500000000000000000 : ℝ) := by
    have hpowers : (10853/100000 : ℝ)^4487 ≤ (29710329698283/500000000000000000 : ℝ)^1024 := by
      have hnat : (10853 : ℕ)^4487*500000000000000000^1024 ≤ 29710329698283^1024*100000^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10853 100000 29710329698283 500000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10853/100000 : ℝ)) (X := (29710329698283/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4487/1024 : ℝ) ≤ (5631399232709393/20000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4487 ≤ (5631399232709393/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4487*20000000000000000000^1024 ≤ 5631399232709393^1024*100000^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 5631399232709393 20000000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (5631399232709393/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250029710329698283/250000000000000000 : ℝ) ≤ (2000054240218397/2000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (250029710329698283/250000000000000000 : ℝ)^1024 ≤ (2000054240218397/2000000000000000 : ℝ)^4487 := by
      have hnat : (250029710329698283 : ℕ)^1024*2000000000000000^4487 ≤ 2000054240218397^4487*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250029710329698283 250000000000000000 2000054240218397 2000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000054240218397/2000000000000000 : ℝ)) (X := (250029710329698283/250000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006819812420640713/20000000000000000000 : ℝ) ≤ (2000155617766353/2000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (20006819812420640713/20000000000000000000 : ℝ)^1024 ≤ (2000155617766353/2000000000000000 : ℝ)^4487 := by
      have hnat : (20006819812420640713 : ℕ)^1024*2000000000000000^4487 ≤ 2000155617766353^4487*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006819812420640713 20000000000000000000 2000155617766353 2000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000155617766353/2000000000000000 : ℝ)) (X := (20006819812420640713/20000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005631399232709393/10000000000000000000 : ℝ) ≤ (2000256995314309/2000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (10005631399232709393/10000000000000000000 : ℝ)^1024 ≤ (2000256995314309/2000000000000000 : ℝ)^4487 := by
      have hnat : (10005631399232709393 : ℕ)^1024*2000000000000000^4487 ≤ 2000256995314309^4487*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005631399232709393 10000000000000000000 2000256995314309 2000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000256995314309/2000000000000000 : ℝ)) (X := (10005631399232709393/10000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(29710329698283/500000000000000000 : ℝ) ≤ ((4625025207097185793/4626000000000000000 : ℝ)+2*(25344386989/23130000000000 : ℝ)*(10853/100000 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (4625025207097185793/4626000000000000000 : ℝ)+2*(25344386989/23130000000000 : ℝ)*(10853/100000 : ℝ)=(2000054240218397/2000000000000000 : ℝ) by norm_num, show 1+2*(29710329698283/500000000000000000 : ℝ)=(250029710329698283/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5631399232709393/20000000000000000000 : ℝ)+(29710329698283/500000000000000000 : ℝ) ≤ ((4625025207097185793/4626000000000000000 : ℝ)+(25344386989/23130000000000 : ℝ)*((15479/100000 : ℝ)+(10853/100000 : ℝ)))^(4487/1024 : ℝ) := by
    rw [show (4625025207097185793/4626000000000000000 : ℝ)+(25344386989/23130000000000 : ℝ)*((15479/100000 : ℝ)+(10853/100000 : ℝ))=(2000155617766353/2000000000000000 : ℝ) by norm_num, show 1+(5631399232709393/20000000000000000000 : ℝ)+(29710329698283/500000000000000000 : ℝ)=(20006819812420640713/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5631399232709393/20000000000000000000 : ℝ) ≤ ((4625025207097185793/4626000000000000000 : ℝ)+2*(25344386989/23130000000000 : ℝ)*(15479/100000 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (4625025207097185793/4626000000000000000 : ℝ)+2*(25344386989/23130000000000 : ℝ)*(15479/100000 : ℝ)=(2000256995314309/2000000000000000 : ℝ) by norm_num, show 1+2*(5631399232709393/20000000000000000000 : ℝ)=(10005631399232709393/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4625025207097185793/4626000000000000000 : ℝ)*(X 1 0+X 2 0)+(25344386989/23130000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4625025207097185793/4626000000000000000 : ℝ)) (alpha := (25344386989/23130000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4625025207097185793/4626000000000000000 : ℝ)*(X 0 1+X 2 1)+(25344386989/23130000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4625025207097185793/4626000000000000000 : ℝ)) (alpha := (25344386989/23130000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4625025207097185793/4626000000000000000 : ℝ)*(X 0 2+X 1 2)+(25344386989/23130000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4625025207097185793/4626000000000000000 : ℝ)) (alpha := (25344386989/23130000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-418846279/2500000000 : ℝ)*X 0 0+(2702282659/5000000000 : ℝ)*X 0 1+(135114061/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635269287/5000000000 : ℝ)*X 1 0+(-1861173219/10000000000 : ℝ)*X 1 1+(1351140913/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270539163/10000000000 : ℝ)*X 2 0+(1080912813/2000000000 : ℝ)*X 2 1+(-1861171851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2240545939/5000000000 : ℝ)*X 0 0+(4182464541/10000000000 : ℝ)*X 0 1+(4182465407/10000000000 : ℝ)*X 0 2+(2240545939/5000000000 : ℝ)*X 1 0+(4182464541/10000000000 : ℝ)*X 1 1+(4182465407/10000000000 : ℝ)*X 1 2+(2240545939/5000000000 : ℝ)*X 2 0+(4182464541/10000000000 : ℝ)*X 2 1+(4182465407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528474899/2500000000 : ℝ)*X 0 0+(5243071101/10000000000 : ℝ)*X 0 1+(2621535477/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5383113947/10000000000 : ℝ)*X 1 0+(-1927534259/10000000000 : ℝ)*X 1 1+(1048614209/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2691557057/5000000000 : ℝ)*X 2 0+(5243071197/10000000000 : ℝ)*X 2 1+(-481883457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((203556687/500000000 : ℝ)*X 0 0+(877461477/2000000000 : ℝ)*X 0 1+(2193653947/5000000000 : ℝ)*X 0 2+(203556687/500000000 : ℝ)*X 1 0+(877461477/2000000000 : ℝ)*X 1 1+(2193653947/5000000000 : ℝ)*X 1 2+(203556687/500000000 : ℝ)*X 2 0+(877461477/2000000000 : ℝ)*X 2 1+(2193653947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1010659477/5000000000 : ℝ)*X 0 0+(2565056007/5000000000 : ℝ)*X 0 1+(5425063681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((210249709/400000000 : ℝ)*X 1 0+(-1852498089/10000000000 : ℝ)*X 1 1+(1085012603/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628120713/5000000000 : ℝ)*X 2 0+(2712532519/5000000000 : ℝ)*X 2 1+(-1852497079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((566497149/1250000000 : ℝ)*X 0 0+(4156431469/10000000000 : ℝ)*X 0 1+(4156430547/10000000000 : ℝ)*X 0 2+(566497149/1250000000 : ℝ)*X 1 0+(4156431469/10000000000 : ℝ)*X 1 1+(4156430547/10000000000 : ℝ)*X 1 2+(566497149/1250000000 : ℝ)*X 2 0+(4156431469/10000000000 : ℝ)*X 2 1+(4156430547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1768003559/10000000000 : ℝ)*X 0 0+(5513835783/10000000000 : ℝ)*X 0 1+(209122379/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5393577667/10000000000 : ℝ)*X 1 0+(-38670431/200000000 : ℝ)*X 1 1+(1045611913/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5393577837/10000000000 : ℝ)*X 2 0+(163376853/312500000 : ℝ)*X 2 1+(-1933521681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4032165943/10000000000 : ℝ)*X 0 0+(2203163079/5000000000 : ℝ)*X 0 1+(550790833/1250000000 : ℝ)*X 0 2+(4032165943/10000000000 : ℝ)*X 1 0+(2203163079/5000000000 : ℝ)*X 1 1+(550790833/1250000000 : ℝ)*X 1 2+(4032165943/10000000000 : ℝ)*X 2 0+(2203163079/5000000000 : ℝ)*X 2 1+(550790833/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63719/100000 : ℝ) ≤ (-49125781520987939770357276604123/77100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17941609/20000000000000 : ℝ)*(upper0) + (24921419/50000000000000 : ℝ)*(lower1) + (4516627/3125000000000 : ℝ)*(lower2) + (491413/6250000000000 : ℝ)*(upper5) + (2199690809639063/100000000000000 : ℝ)*(major0) + (2199690809639063/100000000000000 : ℝ)*(major1) + (2199690809639063/100000000000000 : ℝ)*(major2) + (69398801/5000000000000 : ℝ)*(sp1) + (765910604309979/25000000000000 : ℝ)*(sp4) + (1531820527025149/50000000000000 : ℝ)*(sp5) + (3063568143382067/100000000000000 : ℝ)*(sp6) + (339244541559057/25000000000000 : ℝ)*(sp7) + (12393201/50000000000000 : ℝ)*(sp8) + (297194577/400000000000 : ℝ)*(sp14) + (339244541559057/25000000000000 : ℝ)*(f.failure) + (1531821221013159/50000000000000 : ℝ)*(f.sum) + (937216414613/1156500000000000000000000000 : ℝ)*base65 + (3820342508733189347/154200000000000000000000000000000 : ℝ)*base68 + (1027226087875989347/154200000000000000000000000000000 : ℝ)*base70 + (1165309866857589347/154200000000000000000000000000000 : ℝ)*base72 + (2569348704481/115650000000000000000000000 : ℝ)*base74 + (1529174970936789347/154200000000000000000000000000000 : ℝ)*base76 + (133616139805989347/154200000000000000000000000000000 : ℝ)*base78 + (3298556085414189347/154200000000000000000000000000000 : ℝ)*base80 + (706130855891/578250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (26167/312500000000000000000 : ℝ)*base90 + (26167/312500000000000000000 : ℝ)*base92 + (26167/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58553/100000 : ℝ) ≤ (2821618316468232528671741896987/4818750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47413547/12500000000000 : ℝ)*(upper0) + (1995803/10000000000000 : ℝ)*(upper3) + (506373767/100000000000000 : ℝ)*(upper4) + (284359742842291/12500000000000 : ℝ)*(major0) + (284359742842291/12500000000000 : ℝ)*(major1) + (284359742842291/12500000000000 : ℝ)*(major2) + (3126848561851109/100000000000000 : ℝ)*(sp0) + (1563429092436201/50000000000000 : ℝ)*(sp1) + (781707390951643/25000000000000 : ℝ)*(sp2) + (1403342640172551/100000000000000 : ℝ)*(sp3) + (9321497867/50000000000000 : ℝ)*(sp5) + (11816015391/25000000000000 : ℝ)*(sp6) + (1130578953/6250000000000 : ℝ)*(sp7) + (28266017027/100000000000000 : ℝ)*(sp8) + (1403360729435799/100000000000000 : ℝ)*(f.failure) + (390859603483517/12500000000000 : ℝ)*(f.sum) + (486967087229/144562500000000000000000000 : ℝ)*base66 + (52044725384498921/19275000000000000000000000000000 : ℝ)*base67 + (146903463195623921/19275000000000000000000000000000 : ℝ)*base69 + (73035884010923921/19275000000000000000000000000000 : ℝ)*base71 + (6258284069867/2313000000000000000000000000 : ℝ)*base74 + (53959186001198921/19275000000000000000000000000000 : ℝ)*base75 + (118329113888273921/19275000000000000000000000000000 : ℝ)*base77 + (12771456820701079/19275000000000000000000000000000 : ℝ)*base80 + (8695067151619/2313000000000000000000000000 : ℝ)*base81 + (4532569/1250000000000000000000 : ℝ)*base90 + (4532569/1250000000000000000000 : ℝ)*base92 + (4532569/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40073/50000 : ℝ) ≤ (20598039832573147705895218886203/25700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150150187/100000000000000 : ℝ)*(upper1) + (13208081/20000000000000 : ℝ)*(lower3) + (20060463/50000000000000 : ℝ)*(upper4) + (5524167/100000000000000 : ℝ)*(lower5) + (2470610564950629/100000000000000 : ℝ)*(major0) + (2470610564950629/100000000000000 : ℝ)*(major1) + (2470610564950629/100000000000000 : ℝ)*(major2) + (2343738603/50000000000000 : ℝ)*(sp0) + (42011335139/12500000000000 : ℝ)*(sp2) + (53385015053/100000000000000 : ℝ)*(sp3) + (3390393240560011/100000000000000 : ℝ)*(sp8) + (3390397928037217/100000000000000 : ℝ)*(sp9) + (678012367471221/20000000000000 : ℝ)*(sp10) + (1524053811878069/100000000000000 : ℝ)*(sp11) + (1524107196893123/100000000000000 : ℝ)*(f.failure) + (3390397928037217/100000000000000 : ℝ)*(f.sum) + (1152112462411/385500000000000000000000000 : ℝ)*base65 + (66336983770201533/51400000000000000000000000000000 : ℝ)*base67 + (111916152271601533/51400000000000000000000000000000 : ℝ)*base69 + (334016083644801533/51400000000000000000000000000000 : ℝ)*base71 + (721397521837/771000000000000000000000000 : ℝ)*base74 + (121711649498001533/51400000000000000000000000000000 : ℝ)*base75 + (428083292469401533/51400000000000000000000000000000 : ℝ)*base77 + (277149786319001533/51400000000000000000000000000000 : ℝ)*base79 + (11446725719957/771000000000000000000000000 : ℝ)*base81 + (6537587/1250000000000000000000 : ℝ)*base89 + (6537587/1250000000000000000000 : ℝ)*base91 + (6537587/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-42949/50000 : ℝ) ≤ (-883009249590749431826633725571/1028000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65113759/100000000000000 : ℝ)*(lower1) + (5039639/100000000000000 : ℝ)*(lower3) + (3111923/20000000000000 : ℝ)*(lower4) + (264009/5000000000000 : ℝ)*(upper5) + (100371576318441/4000000000000 : ℝ)*(major0) + (100371576318441/4000000000000 : ℝ)*(major1) + (100371576318441/4000000000000 : ℝ)*(major2) + (19039385463/100000000000000 : ℝ)*(sp5) + (90760259987/100000000000000 : ℝ)*(sp6) + (12402290543/100000000000000 : ℝ)*(sp7) + (1749621391493709/50000000000000 : ℝ)*(sp12) + (699844748720391/20000000000000 : ℝ)*(sp13) + (349915202272743/10000000000000 : ℝ)*(sp14) + (773977788888687/50000000000000 : ℝ)*(sp15) + (1547967980067917/100000000000000 : ℝ)*(f.failure) + (1749621391493709/50000000000000 : ℝ)*(f.sum) + (116295743851/77100000000000000000000000 : ℝ)*base65 + (9228971207706143/2056000000000000000000000000000 : ℝ)*base68 + (1204108504621857/2056000000000000000000000000000 : ℝ)*base69 + (8388073461901857/2056000000000000000000000000000 : ℝ)*base71 + (163564005743/77100000000000000000000000 : ℝ)*base74 + (8169160255538143/2056000000000000000000000000000 : ℝ)*base76 + (16079088394909857/2056000000000000000000000000000 : ℝ)*base77 + (22125428838493857/2056000000000000000000000000000 : ℝ)*base79 + (3246159597901/385500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6017827/1250000000000000000000 : ℝ)*base90 + (6017827/1250000000000000000000 : ℝ)*base92 + (6017827/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1496_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63719/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58553/100000 : ℝ) else (40073/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42949/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1496_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1496_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63719/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58553/100000 : ℝ) else (40073/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42949/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1496_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1496_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63719/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58553/100000 : ℝ) else (40073/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42949/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1496_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

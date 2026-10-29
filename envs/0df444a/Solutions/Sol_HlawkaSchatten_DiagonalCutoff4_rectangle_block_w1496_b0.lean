-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1496_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:51:01.48191+00:00
-- url     : https://prove2.me/submissions/2090fd2a-07b6-4711-918c-f915e1c9816f

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
theorem support_rectangle_w1496_s0_0 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-340587511/2000000000 : ℝ)*x 0 + (2962627251/5000000000 : ℝ)*x 1 + (151512907/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340587511/2000000000 : ℝ)^4489 ≤ (10092468956621/100000000000000 : ℝ)^3465 := by
    have hnat : (340587511 : ℕ)^4489*100000000000000^3465 ≤ 10092468956621^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340587511 2000000000 10092468956621 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2962627251/5000000000 : ℝ)^4489 ≤ (50761665432869/100000000000000 : ℝ)^3465 := by
    have hnat : (2962627251 : ℕ)^4489*100000000000000^3465 ≤ 50761665432869^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2962627251 5000000000 50761665432869 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151512907/312500000 : ℝ)^4489 ≤ (2446616599477/6250000000000 : ℝ)^3465 := by
    have hnat : (151512907 : ℕ)^4489*6250000000000^3465 ≤ 2446616599477^3465*312500000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151512907 312500000 2446616599477 6250000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340587511/2000000000 : ℝ), (2962627251/5000000000 : ℝ), (151512907/312500000 : ℝ)] ![(10092468956621/100000000000000 : ℝ), (50761665432869/100000000000000 : ℝ), (2446616599477/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340587511/2000000000 : ℝ)|^4489 ≤ (10092468956621/100000000000000 : ℝ)^3465
        have hw : |(-340587511/2000000000 : ℝ)|=(340587511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2962627251/5000000000 : ℝ)|^4489 ≤ (50761665432869/100000000000000 : ℝ)^3465
        have hw : |(2962627251/5000000000 : ℝ)|=(2962627251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151512907/312500000 : ℝ)|^4489 ≤ (2446616599477/6250000000000 : ℝ)^3465
        have hw : |(151512907/312500000 : ℝ)|=(151512907/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s0_1 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5481469681/10000000000 : ℝ)*x 0 + (-2307783299/10000000000 : ℝ)*x 1 + (4848413681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5481469681/10000000000 : ℝ)^4489 ≤ (45891696664997/100000000000000 : ℝ)^3465 := by
    have hnat : (5481469681 : ℕ)^4489*100000000000000^3465 ≤ 45891696664997^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481469681 10000000000 45891696664997 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307783299/10000000000 : ℝ)^4489 ≤ (935151928551/6250000000000 : ℝ)^3465 := by
    have hnat : (2307783299 : ℕ)^4489*6250000000000^3465 ≤ 935151928551^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307783299 10000000000 935151928551 6250000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4848413681/10000000000 : ℝ)^4489 ≤ (9786468115967/25000000000000 : ℝ)^3465 := by
    have hnat : (4848413681 : ℕ)^4489*25000000000000^3465 ≤ 9786468115967^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4848413681 10000000000 9786468115967 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5481469681/10000000000 : ℝ), (-2307783299/10000000000 : ℝ), (4848413681/10000000000 : ℝ)] ![(45891696664997/100000000000000 : ℝ), (935151928551/6250000000000 : ℝ), (9786468115967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5481469681/10000000000 : ℝ)|^4489 ≤ (45891696664997/100000000000000 : ℝ)^3465
        have hw : |(5481469681/10000000000 : ℝ)|=(5481469681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2307783299/10000000000 : ℝ)|^4489 ≤ (935151928551/6250000000000 : ℝ)^3465
        have hw : |(-2307783299/10000000000 : ℝ)|=(2307783299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4848413681/10000000000 : ℝ)|^4489 ≤ (9786468115967/25000000000000 : ℝ)^3465
        have hw : |(4848413681/10000000000 : ℝ)|=(4848413681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s0_2 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (342591841/625000000 : ℝ)*x 0 + (4848415157/10000000000 : ℝ)*x 1 + (-2307781751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342591841/625000000 : ℝ)^4489 ≤ (45891694224569/100000000000000 : ℝ)^3465 := by
    have hnat : (342591841 : ℕ)^4489*100000000000000^3465 ≤ 45891694224569^3465*625000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342591841 625000000 45891694224569 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4848415157/10000000000 : ℝ)^4489 ≤ (2446617993929/6250000000000 : ℝ)^3465 := by
    have hnat : (4848415157 : ℕ)^4489*6250000000000^3465 ≤ 2446617993929^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4848415157 10000000000 2446617993929 6250000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2307781751/10000000000 : ℝ)^4489 ≤ (14962417854389/100000000000000 : ℝ)^3465 := by
    have hnat : (2307781751 : ℕ)^4489*100000000000000^3465 ≤ 14962417854389^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307781751 10000000000 14962417854389 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342591841/625000000 : ℝ), (4848415157/10000000000 : ℝ), (-2307781751/10000000000 : ℝ)] ![(45891694224569/100000000000000 : ℝ), (2446617993929/6250000000000 : ℝ), (14962417854389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342591841/625000000 : ℝ)|^4489 ≤ (45891694224569/100000000000000 : ℝ)^3465
        have hw : |(342591841/625000000 : ℝ)|=(342591841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4848415157/10000000000 : ℝ)|^4489 ≤ (2446617993929/6250000000000 : ℝ)^3465
        have hw : |(4848415157/10000000000 : ℝ)|=(4848415157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2307781751/10000000000 : ℝ)|^4489 ≤ (14962417854389/100000000000000 : ℝ)^3465
        have hw : |(-2307781751/10000000000 : ℝ)|=(2307781751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s0_3 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (829897187/2000000000 : ℝ)*x 0 + (1545628209/5000000000 : ℝ)*x 1 + (5505576067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829897187/2000000000 : ℝ)^4489 ≤ (499944091073/1562500000000 : ℝ)^3465 := by
    have hnat : (829897187 : ℕ)^4489*1562500000000^3465 ≤ 499944091073^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829897187 2000000000 499944091073 1562500000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545628209/5000000000 : ℝ)^4489 ≤ (10925122768159/50000000000000 : ℝ)^3465 := by
    have hnat : (1545628209 : ℕ)^4489*50000000000000^3465 ≤ 10925122768159^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545628209 5000000000 10925122768159 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505576067/10000000000 : ℝ)^4489 ≤ (46153332608701/100000000000000 : ℝ)^3465 := by
    have hnat : (5505576067 : ℕ)^4489*100000000000000^3465 ≤ 46153332608701^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505576067 10000000000 46153332608701 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(829897187/2000000000 : ℝ), (1545628209/5000000000 : ℝ), (5505576067/10000000000 : ℝ)] ![(499944091073/1562500000000 : ℝ), (10925122768159/50000000000000 : ℝ), (46153332608701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(829897187/2000000000 : ℝ)|^4489 ≤ (499944091073/1562500000000 : ℝ)^3465
        have hw : |(829897187/2000000000 : ℝ)|=(829897187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1545628209/5000000000 : ℝ)|^4489 ≤ (10925122768159/50000000000000 : ℝ)^3465
        have hw : |(1545628209/5000000000 : ℝ)|=(1545628209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505576067/10000000000 : ℝ)|^4489 ≤ (46153332608701/100000000000000 : ℝ)^3465
        have hw : |(5505576067/10000000000 : ℝ)|=(5505576067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s0_4 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1706595409/10000000000 : ℝ)*x 0 + (38093461/78125000 : ℝ)*x 1 + (235868669/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706595409/10000000000 : ℝ)^4489 ≤ (2530140668067/25000000000000 : ℝ)^3465 := by
    have hnat : (1706595409 : ℕ)^4489*25000000000000^3465 ≤ 2530140668067^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706595409 10000000000 2530140668067 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38093461/78125000 : ℝ)^4489 ≤ (19717140353721/50000000000000 : ℝ)^3465 := by
    have hnat : (38093461 : ℕ)^4489*50000000000000^3465 ≤ 19717140353721^3465*78125000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38093461 78125000 19717140353721 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235868669/400000000 : ℝ)^4489 ≤ (25222578303777/50000000000000 : ℝ)^3465 := by
    have hnat : (235868669 : ℕ)^4489*50000000000000^3465 ≤ 25222578303777^3465*400000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235868669 400000000 25222578303777 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1706595409/10000000000 : ℝ), (38093461/78125000 : ℝ), (235868669/400000000 : ℝ)] ![(2530140668067/25000000000000 : ℝ), (19717140353721/50000000000000 : ℝ), (25222578303777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1706595409/10000000000 : ℝ)|^4489 ≤ (2530140668067/25000000000000 : ℝ)^3465
        have hw : |(-1706595409/10000000000 : ℝ)|=(1706595409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38093461/78125000 : ℝ)|^4489 ≤ (19717140353721/50000000000000 : ℝ)^3465
        have hw : |(38093461/78125000 : ℝ)|=(38093461/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235868669/400000000 : ℝ)|^4489 ≤ (25222578303777/50000000000000 : ℝ)^3465
        have hw : |(235868669/400000000 : ℝ)|=(235868669/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s0_5 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187346731/10000000000 : ℝ)*x 0 + (-251895969/2000000000 : ℝ)*x 1 + (589671651/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187346731/10000000000 : ℝ)^4489 ≤ (42727157137683/100000000000000 : ℝ)^3465 := by
    have hnat : (5187346731 : ℕ)^4489*100000000000000^3465 ≤ 42727157137683^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187346731 10000000000 42727157137683 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251895969/2000000000 : ℝ)^4489 ≤ (6827688629223/100000000000000 : ℝ)^3465 := by
    have hnat : (251895969 : ℕ)^4489*100000000000000^3465 ≤ 6827688629223^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251895969 2000000000 6827688629223 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589671651/1000000000 : ℝ)^4489 ≤ (25222577112359/50000000000000 : ℝ)^3465 := by
    have hnat : (589671651 : ℕ)^4489*50000000000000^3465 ≤ 25222577112359^3465*1000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589671651 1000000000 25222577112359 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187346731/10000000000 : ℝ), (-251895969/2000000000 : ℝ), (589671651/1000000000 : ℝ)] ![(42727157137683/100000000000000 : ℝ), (6827688629223/100000000000000 : ℝ), (25222577112359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187346731/10000000000 : ℝ)|^4489 ≤ (42727157137683/100000000000000 : ℝ)^3465
        have hw : |(5187346731/10000000000 : ℝ)|=(5187346731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-251895969/2000000000 : ℝ)|^4489 ≤ (6827688629223/100000000000000 : ℝ)^3465
        have hw : |(-251895969/2000000000 : ℝ)|=(251895969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(589671651/1000000000 : ℝ)|^4489 ≤ (25222577112359/50000000000000 : ℝ)^3465
        have hw : |(589671651/1000000000 : ℝ)|=(589671651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s0_6 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187346793/10000000000 : ℝ)*x 0 + (73708957/125000000 : ℝ)*x 1 + (-157434959/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187346793/10000000000 : ℝ)^4489 ≤ (8545431559857/20000000000000 : ℝ)^3465 := by
    have hnat : (5187346793 : ℕ)^4489*20000000000000^3465 ≤ 8545431559857^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187346793 10000000000 8545431559857 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73708957/125000000 : ℝ)^4489 ≤ (25222577389433/50000000000000 : ℝ)^3465 := by
    have hnat : (73708957 : ℕ)^4489*50000000000000^3465 ≤ 25222577389433^3465*125000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73708957 125000000 25222577389433 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157434959/1250000000 : ℝ)^4489 ≤ (3413843707113/50000000000000 : ℝ)^3465 := by
    have hnat : (157434959 : ℕ)^4489*50000000000000^3465 ≤ 3413843707113^3465*1250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157434959 1250000000 3413843707113 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187346793/10000000000 : ℝ), (73708957/125000000 : ℝ), (-157434959/1250000000 : ℝ)] ![(8545431559857/20000000000000 : ℝ), (25222577389433/50000000000000 : ℝ), (3413843707113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187346793/10000000000 : ℝ)|^4489 ≤ (8545431559857/20000000000000 : ℝ)^3465
        have hw : |(5187346793/10000000000 : ℝ)|=(5187346793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73708957/125000000 : ℝ)|^4489 ≤ (25222577389433/50000000000000 : ℝ)^3465
        have hw : |(73708957/125000000 : ℝ)|=(73708957/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157434959/1250000000 : ℝ)|^4489 ≤ (3413843707113/50000000000000 : ℝ)^3465
        have hw : |(-157434959/1250000000 : ℝ)|=(157434959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s0_7 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33261527/80000000 : ℝ)*x 0 + (5443811587/10000000000 : ℝ)*x 1 + (3155238247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33261527/80000000 : ℝ)^4489 ≤ (32078410850839/100000000000000 : ℝ)^3465 := by
    have hnat : (33261527 : ℕ)^4489*100000000000000^3465 ≤ 32078410850839^3465*80000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33261527 80000000 32078410850839 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443811587/10000000000 : ℝ)^4489 ≤ (45483659247857/100000000000000 : ℝ)^3465 := by
    have hnat : (5443811587 : ℕ)^4489*100000000000000^3465 ≤ 45483659247857^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443811587 10000000000 45483659247857 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3155238247/10000000000 : ℝ)^4489 ≤ (4487585978187/20000000000000 : ℝ)^3465 := by
    have hnat : (3155238247 : ℕ)^4489*20000000000000^3465 ≤ 4487585978187^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3155238247 10000000000 4487585978187 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33261527/80000000 : ℝ), (5443811587/10000000000 : ℝ), (3155238247/10000000000 : ℝ)] ![(32078410850839/100000000000000 : ℝ), (45483659247857/100000000000000 : ℝ), (4487585978187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33261527/80000000 : ℝ)|^4489 ≤ (32078410850839/100000000000000 : ℝ)^3465
        have hw : |(33261527/80000000 : ℝ)|=(33261527/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443811587/10000000000 : ℝ)|^4489 ≤ (45483659247857/100000000000000 : ℝ)^3465
        have hw : |(5443811587/10000000000 : ℝ)|=(5443811587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3155238247/10000000000 : ℝ)|^4489 ≤ (4487585978187/20000000000000 : ℝ)^3465
        have hw : |(3155238247/10000000000 : ℝ)|=(3155238247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1496_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2619/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25693/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4487/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4487 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4487*1^1024 ≤ 0^1024*1^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4487/1024 : ℝ) ≤ (1804231118430389901/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4487 ≤ (1804231118430389901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4487*100000000000000000000^1024 ≤ 1804231118430389901^1024*5^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1804231118430389901 100000000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1804231118430389901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4487 := by
      have hnat : (1 : ℕ)^1024*1^4487 ≤ 1^4487*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101804231118430389901/100000000000000000000 : ℝ) ≤ (10040891571010081/10000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (101804231118430389901/100000000000000000000 : ℝ)^1024 ≤ (10040891571010081/10000000000000000 : ℝ)^4487 := by
      have hnat : (101804231118430389901 : ℕ)^1024*10000000000000000^4487 ≤ 10040891571010081^4487*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101804231118430389901 100000000000000000000 10040891571010081 10000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10040891571010081/10000000000000000 : ℝ)) (X := (101804231118430389901/100000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51804231118430389901/50000000000000000000 : ℝ) ≤ (5040891571010081/5000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (51804231118430389901/50000000000000000000 : ℝ)^1024 ≤ (5040891571010081/5000000000000000 : ℝ)^4487 := by
      have hnat : (51804231118430389901 : ℕ)^1024*5000000000000000^4487 ≤ 5040891571010081^4487*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51804231118430389901 50000000000000000000 5040891571010081 5000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5040891571010081/5000000000000000 : ℝ)) (X := (51804231118430389901/50000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(40891571010081/4000000000000000 : ℝ)*(0 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40891571010081/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1804231118430389901/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(40891571010081/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4487/1024 : ℝ) := by
    rw [show (1 : ℝ)+(40891571010081/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10040891571010081/10000000000000000 : ℝ) by norm_num, show 1+(1804231118430389901/100000000000000000000 : ℝ)+(0 : ℝ)=(101804231118430389901/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1804231118430389901/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(40891571010081/4000000000000000 : ℝ)*(2/5 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40891571010081/4000000000000000 : ℝ)*(2/5 : ℝ)=(5040891571010081/5000000000000000 : ℝ) by norm_num, show 1+2*(1804231118430389901/100000000000000000000 : ℝ)=(51804231118430389901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(40891571010081/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40891571010081/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(40891571010081/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40891571010081/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(40891571010081/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40891571010081/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-340587511/2000000000 : ℝ)*X 0 0+(2962627251/5000000000 : ℝ)*X 0 1+(151512907/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5481469681/10000000000 : ℝ)*X 1 0+(-2307783299/10000000000 : ℝ)*X 1 1+(4848413681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((342591841/625000000 : ℝ)*X 2 0+(4848415157/10000000000 : ℝ)*X 2 1+(-2307781751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((829897187/2000000000 : ℝ)*X 0 0+(1545628209/5000000000 : ℝ)*X 0 1+(5505576067/10000000000 : ℝ)*X 0 2+(829897187/2000000000 : ℝ)*X 1 0+(1545628209/5000000000 : ℝ)*X 1 1+(5505576067/10000000000 : ℝ)*X 1 2+(829897187/2000000000 : ℝ)*X 2 0+(1545628209/5000000000 : ℝ)*X 2 1+(5505576067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1706595409/10000000000 : ℝ)*X 0 0+(38093461/78125000 : ℝ)*X 0 1+(235868669/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5187346731/10000000000 : ℝ)*X 1 0+(-251895969/2000000000 : ℝ)*X 1 1+(589671651/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5187346793/10000000000 : ℝ)*X 2 0+(73708957/125000000 : ℝ)*X 2 1+(-157434959/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33261527/80000000 : ℝ)*X 0 0+(5443811587/10000000000 : ℝ)*X 0 1+(3155238247/10000000000 : ℝ)*X 0 2+(33261527/80000000 : ℝ)*X 1 0+(5443811587/10000000000 : ℝ)*X 1 1+(3155238247/10000000000 : ℝ)*X 1 2+(33261527/80000000 : ℝ)*X 2 0+(5443811587/10000000000 : ℝ)*X 2 1+(3155238247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (158604665955700040612127/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (341247561/25000000000000 : ℝ)*(base19) + (1060269819/100000000000000 : ℝ)*(base23) + (3167013/2500000000000 : ℝ)*(upper3) + (146136937/100000000000000 : ℝ)*(upper4) + (313308031/100000000000000 : ℝ)*(upper5) + (335712688756411/50000000000000 : ℝ)*(major0) + (335712688756411/50000000000000 : ℝ)*(major1) + (335712688756411/50000000000000 : ℝ)*(major2) + (928645638834207/100000000000000 : ℝ)*(sp0) + (116081294409063/12500000000000 : ℝ)*(sp1) + (928650659992929/100000000000000 : ℝ)*(sp2) + (41419733830543/10000000000000 : ℝ)*(sp3) + (6081428541/100000000000000 : ℝ)*(sp4) + (198840127/12500000000000 : ℝ)*(sp7) + (207099464513223/50000000000000 : ℝ)*(f.failure) + (232162930065687/25000000000000 : ℝ)*(f.sum) + (435532644779291/100000000000000000000000000000 : ℝ)*base65 + (184382359579291/200000000000000000000000000000 : ℝ)*base67 + (1054406443379291/200000000000000000000000000000 : ℝ)*base69 + (1885325579579291/200000000000000000000000000000 : ℝ)*base71 + (497458109220709/100000000000000000000000000000 : ℝ)*base74 + (1079573037179291/200000000000000000000000000000 : ℝ)*base75 + (1421220499579291/200000000000000000000000000000 : ℝ)*base77 + (643049637379291/200000000000000000000000000000 : ℝ)*base79 + (38153373920709/100000000000000000000000000000 : ℝ)*base82 + (2405513/625000000000000000000 : ℝ)*base90 + (2405513/625000000000000000000 : ℝ)*base92 + (2405513/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1396798680797240496003147/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1436217393/100000000000000 : ℝ)*(base19) + (1466771933/100000000000000 : ℝ)*(base23) + (22133703/25000000000000 : ℝ)*(base32) + (207802781/100000000000000 : ℝ)*(upper3) + (15538211/10000000000000 : ℝ)*(upper5) + (708310722235757/100000000000000 : ℝ)*(major0) + (708310722235757/100000000000000 : ℝ)*(major1) + (708310722235757/100000000000000 : ℝ)*(major2) + (1719231603/50000000000000 : ℝ)*(sp1) + (1841229/48828125000 : ℝ)*(sp2) + (24491697487961/2500000000000 : ℝ)*(sp4) + (489831512418921/50000000000000 : ℝ)*(sp5) + (244915665477379/25000000000000 : ℝ)*(sp6) + (17478128944739/4000000000000 : ℝ)*(sp7) + (54619164019161/12500000000000 : ℝ)*(f.failure) + (24491697487961/2500000000000 : ℝ)*(f.sum) + (221680372666317/200000000000000000000000000000 : ℝ)*base65 + (2526040167666317/400000000000000000000000000000 : ℝ)*base67 + (956606175666317/400000000000000000000000000000 : ℝ)*base69 + (250188140466317/400000000000000000000000000000 : ℝ)*base71 + (1447059357466317/200000000000000000000000000000 : ℝ)*base73 + (2237707306733683/400000000000000000000000000000 : ℝ)*base76 + (491750560333683/400000000000000000000000000000 : ℝ)*base78 + (15561905933683/400000000000000000000000000000 : ℝ)*base80 + (53070789466317/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (604309/156250000000000000000 : ℝ)*base89 + (604309/156250000000000000000 : ℝ)*base91 + (604309/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1496_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2619/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25693/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1496_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1496_s1_0 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-116310381/625000000 : ℝ)*x 0 + (5581386511/10000000000 : ℝ)*x 1 + (5090782969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116310381/625000000 : ℝ)^4489 ≤ (5661046026217/50000000000000 : ℝ)^3465 := by
    have hnat : (116310381 : ℕ)^4489*50000000000000^3465 ≤ 5661046026217^3465*625000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116310381 625000000 5661046026217 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5581386511/10000000000 : ℝ)^4489 ≤ (1879133431077/4000000000000 : ℝ)^3465 := by
    have hnat : (5581386511 : ℕ)^4489*4000000000000^3465 ≤ 1879133431077^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5581386511 10000000000 1879133431077 4000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5090782969/10000000000 : ℝ)^4489 ≤ (41699572161219/100000000000000 : ℝ)^3465 := by
    have hnat : (5090782969 : ℕ)^4489*100000000000000^3465 ≤ 41699572161219^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5090782969 10000000000 41699572161219 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116310381/625000000 : ℝ), (5581386511/10000000000 : ℝ), (5090782969/10000000000 : ℝ)] ![(5661046026217/50000000000000 : ℝ), (1879133431077/4000000000000 : ℝ), (41699572161219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116310381/625000000 : ℝ)|^4489 ≤ (5661046026217/50000000000000 : ℝ)^3465
        have hw : |(-116310381/625000000 : ℝ)|=(116310381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5581386511/10000000000 : ℝ)|^4489 ≤ (1879133431077/4000000000000 : ℝ)^3465
        have hw : |(5581386511/10000000000 : ℝ)|=(5581386511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5090782969/10000000000 : ℝ)|^4489 ≤ (41699572161219/100000000000000 : ℝ)^3465
        have hw : |(5090782969/10000000000 : ℝ)|=(5090782969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s1_1 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389565061/10000000000 : ℝ)*x 0 + (-2119827671/10000000000 : ℝ)*x 1 + (127269593/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389565061/10000000000 : ℝ)^4489 ≤ (1403042085459/3125000000000 : ℝ)^3465 := by
    have hnat : (5389565061 : ℕ)^4489*3125000000000^3465 ≤ 1403042085459^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389565061 10000000000 1403042085459 3125000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119827671/10000000000 : ℝ)^4489 ≤ (13403073114011/100000000000000 : ℝ)^3465 := by
    have hnat : (2119827671 : ℕ)^4489*100000000000000^3465 ≤ 13403073114011^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119827671 10000000000 13403073114011 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127269593/250000000 : ℝ)^4489 ≤ (41699580130761/100000000000000 : ℝ)^3465 := by
    have hnat : (127269593 : ℕ)^4489*100000000000000^3465 ≤ 41699580130761^3465*250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127269593 250000000 41699580130761 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389565061/10000000000 : ℝ), (-2119827671/10000000000 : ℝ), (127269593/250000000 : ℝ)] ![(1403042085459/3125000000000 : ℝ), (13403073114011/100000000000000 : ℝ), (41699580130761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389565061/10000000000 : ℝ)|^4489 ≤ (1403042085459/3125000000000 : ℝ)^3465
        have hw : |(5389565061/10000000000 : ℝ)|=(5389565061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119827671/10000000000 : ℝ)|^4489 ≤ (13403073114011/100000000000000 : ℝ)^3465
        have hw : |(-2119827671/10000000000 : ℝ)|=(2119827671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127269593/250000000 : ℝ)|^4489 ≤ (41699580130761/100000000000000 : ℝ)^3465
        have hw : |(127269593/250000000 : ℝ)|=(127269593/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s1_2 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389565707/10000000000 : ℝ)*x 0 + (5090783299/10000000000 : ℝ)*x 1 + (-1059913683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389565707/10000000000 : ℝ)^4489 ≤ (44897353706503/100000000000000 : ℝ)^3465 := by
    have hnat : (5389565707 : ℕ)^4489*100000000000000^3465 ≤ 44897353706503^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389565707 10000000000 44897353706503 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5090783299/10000000000 : ℝ)^4489 ≤ (10424893915787/25000000000000 : ℝ)^3465 := by
    have hnat : (5090783299 : ℕ)^4489*25000000000000^3465 ≤ 10424893915787^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5090783299 10000000000 10424893915787 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059913683/5000000000 : ℝ)^4489 ≤ (20942297837/156250000000 : ℝ)^3465 := by
    have hnat : (1059913683 : ℕ)^4489*156250000000^3465 ≤ 20942297837^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059913683 5000000000 20942297837 156250000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389565707/10000000000 : ℝ), (5090783299/10000000000 : ℝ), (-1059913683/5000000000 : ℝ)] ![(44897353706503/100000000000000 : ℝ), (10424893915787/25000000000000 : ℝ), (20942297837/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389565707/10000000000 : ℝ)|^4489 ≤ (44897353706503/100000000000000 : ℝ)^3465
        have hw : |(5389565707/10000000000 : ℝ)|=(5389565707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5090783299/10000000000 : ℝ)|^4489 ≤ (10424893915787/25000000000000 : ℝ)^3465
        have hw : |(5090783299/10000000000 : ℝ)|=(5090783299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059913683/5000000000 : ℝ)|^4489 ≤ (20942297837/156250000000 : ℝ)^3465
        have hw : |(-1059913683/5000000000 : ℝ)|=(1059913683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s1_3 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4255444451/10000000000 : ℝ)*x 0 + (1867935577/5000000000 : ℝ)*x 1 + (241791229/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255444451/10000000000 : ℝ)^4489 ≤ (33058888356349/100000000000000 : ℝ)^3465 := by
    have hnat : (4255444451 : ℕ)^4489*100000000000000^3465 ≤ 33058888356349^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255444451 10000000000 33058888356349 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867935577/5000000000 : ℝ)^4489 ≤ (109089339511/390625000000 : ℝ)^3465 := by
    have hnat : (1867935577 : ℕ)^4489*390625000000^3465 ≤ 109089339511^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867935577 5000000000 109089339511 390625000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241791229/500000000 : ℝ)^4489 ≤ (39014240720849/100000000000000 : ℝ)^3465 := by
    have hnat : (241791229 : ℕ)^4489*100000000000000^3465 ≤ 39014240720849^3465*500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241791229 500000000 39014240720849 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255444451/10000000000 : ℝ), (1867935577/5000000000 : ℝ), (241791229/500000000 : ℝ)] ![(33058888356349/100000000000000 : ℝ), (109089339511/390625000000 : ℝ), (39014240720849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255444451/10000000000 : ℝ)|^4489 ≤ (33058888356349/100000000000000 : ℝ)^3465
        have hw : |(4255444451/10000000000 : ℝ)|=(4255444451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1867935577/5000000000 : ℝ)|^4489 ≤ (109089339511/390625000000 : ℝ)^3465
        have hw : |(1867935577/5000000000 : ℝ)|=(1867935577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241791229/500000000 : ℝ)|^4489 ≤ (39014240720849/100000000000000 : ℝ)^3465
        have hw : |(241791229/500000000 : ℝ)|=(241791229/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s1_4 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-232662459/1250000000 : ℝ)*x 0 + (2548197647/5000000000 : ℝ)*x 1 + (1115136371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (232662459/1250000000 : ℝ)^4489 ≤ (11324721356941/100000000000000 : ℝ)^3465 := by
    have hnat : (232662459 : ℕ)^4489*100000000000000^3465 ≤ 11324721356941^3465*1250000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232662459 1250000000 11324721356941 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548197647/5000000000 : ℝ)^4489 ≤ (41759139324497/100000000000000 : ℝ)^3465 := by
    have hnat : (2548197647 : ℕ)^4489*100000000000000^3465 ≤ 41759139324497^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548197647 5000000000 41759139324497 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115136371/2000000000 : ℝ)^4489 ≤ (46916139305633/100000000000000 : ℝ)^3465 := by
    have hnat : (1115136371 : ℕ)^4489*100000000000000^3465 ≤ 46916139305633^3465*2000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115136371 2000000000 46916139305633 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-232662459/1250000000 : ℝ), (2548197647/5000000000 : ℝ), (1115136371/2000000000 : ℝ)] ![(11324721356941/100000000000000 : ℝ), (41759139324497/100000000000000 : ℝ), (46916139305633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-232662459/1250000000 : ℝ)|^4489 ≤ (11324721356941/100000000000000 : ℝ)^3465
        have hw : |(-232662459/1250000000 : ℝ)|=(232662459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548197647/5000000000 : ℝ)|^4489 ≤ (41759139324497/100000000000000 : ℝ)^3465
        have hw : |(2548197647/5000000000 : ℝ)|=(2548197647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1115136371/2000000000 : ℝ)|^4489 ≤ (46916139305633/100000000000000 : ℝ)^3465
        have hw : |(1115136371/2000000000 : ℝ)|=(1115136371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s1_5 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260597807/10000000000 : ℝ)*x 0 + (-1634929121/10000000000 : ℝ)*x 1 + (5575681961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260597807/10000000000 : ℝ)^4489 ≤ (87020889871/200000000000 : ℝ)^3465 := by
    have hnat : (5260597807 : ℕ)^4489*200000000000^3465 ≤ 87020889871^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260597807 10000000000 87020889871 200000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1634929121/10000000000 : ℝ)^4489 ≤ (149584602971/1562500000000 : ℝ)^3465 := by
    have hnat : (1634929121 : ℕ)^4489*1562500000000^3465 ≤ 149584602971^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634929121 10000000000 149584602971 1562500000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5575681961/10000000000 : ℝ)^4489 ≤ (46916140461151/100000000000000 : ℝ)^3465 := by
    have hnat : (5575681961 : ℕ)^4489*100000000000000^3465 ≤ 46916140461151^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5575681961 10000000000 46916140461151 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260597807/10000000000 : ℝ), (-1634929121/10000000000 : ℝ), (5575681961/10000000000 : ℝ)] ![(87020889871/200000000000 : ℝ), (149584602971/1562500000000 : ℝ), (46916140461151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260597807/10000000000 : ℝ)|^4489 ≤ (87020889871/200000000000 : ℝ)^3465
        have hw : |(5260597807/10000000000 : ℝ)|=(5260597807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1634929121/10000000000 : ℝ)|^4489 ≤ (149584602971/1562500000000 : ℝ)^3465
        have hw : |(-1634929121/10000000000 : ℝ)|=(1634929121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5575681961/10000000000 : ℝ)|^4489 ≤ (46916140461151/100000000000000 : ℝ)^3465
        have hw : |(5575681961/10000000000 : ℝ)|=(5575681961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s1_6 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630298863/5000000000 : ℝ)*x 0 + (223027279/400000000 : ℝ)*x 1 + (-25545769/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630298863/5000000000 : ℝ)^4489 ≤ (1087761101689/2500000000000 : ℝ)^3465 := by
    have hnat : (2630298863 : ℕ)^4489*2500000000000^3465 ≤ 1087761101689^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630298863 5000000000 1087761101689 2500000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223027279/400000000 : ℝ)^4489 ≤ (23458070306883/50000000000000 : ℝ)^3465 := by
    have hnat : (223027279 : ℕ)^4489*50000000000000^3465 ≤ 23458070306883^3465*400000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223027279 400000000 23458070306883 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25545769/156250000 : ℝ)^4489 ≤ (299169228463/3125000000000 : ℝ)^3465 := by
    have hnat : (25545769 : ℕ)^4489*3125000000000^3465 ≤ 299169228463^3465*156250000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25545769 156250000 299169228463 3125000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630298863/5000000000 : ℝ), (223027279/400000000 : ℝ), (-25545769/156250000 : ℝ)] ![(1087761101689/2500000000000 : ℝ), (23458070306883/50000000000000 : ℝ), (299169228463/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630298863/5000000000 : ℝ)|^4489 ≤ (1087761101689/2500000000000 : ℝ)^3465
        have hw : |(2630298863/5000000000 : ℝ)|=(2630298863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223027279/400000000 : ℝ)|^4489 ≤ (23458070306883/50000000000000 : ℝ)^3465
        have hw : |(223027279/400000000 : ℝ)|=(223027279/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25545769/156250000 : ℝ)|^4489 ≤ (299169228463/3125000000000 : ℝ)^3465
        have hw : |(-25545769/156250000 : ℝ)|=(25545769/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s1_7 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4256192897/10000000000 : ℝ)*x 0 + (2411621347/5000000000 : ℝ)*x 1 + (1874330321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256192897/10000000000 : ℝ)^4489 ≤ (33066421243203/100000000000000 : ℝ)^3465 := by
    have hnat : (4256192897 : ℕ)^4489*100000000000000^3465 ≤ 33066421243203^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256192897 10000000000 33066421243203 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2411621347/5000000000 : ℝ)^4489 ≤ (9720696390551/25000000000000 : ℝ)^3465 := by
    have hnat : (2411621347 : ℕ)^4489*25000000000000^3465 ≤ 9720696390551^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411621347 5000000000 9720696390551 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1874330321/5000000000 : ℝ)^4489 ≤ (1402539659417/5000000000000 : ℝ)^3465 := by
    have hnat : (1874330321 : ℕ)^4489*5000000000000^3465 ≤ 1402539659417^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874330321 5000000000 1402539659417 5000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256192897/10000000000 : ℝ), (2411621347/5000000000 : ℝ), (1874330321/5000000000 : ℝ)] ![(33066421243203/100000000000000 : ℝ), (9720696390551/25000000000000 : ℝ), (1402539659417/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256192897/10000000000 : ℝ)|^4489 ≤ (33066421243203/100000000000000 : ℝ)^3465
        have hw : |(4256192897/10000000000 : ℝ)|=(4256192897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2411621347/5000000000 : ℝ)|^4489 ≤ (9720696390551/25000000000000 : ℝ)^3465
        have hw : |(2411621347/5000000000 : ℝ)|=(2411621347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1874330321/5000000000 : ℝ)|^4489 ≤ (1402539659417/5000000000000 : ℝ)^3465
        have hw : |(1874330321/5000000000 : ℝ)|=(1874330321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1496_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2619/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1017/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1851/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2619/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2619/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2619/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2619/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2619/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2619/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2619/100000 : ℝ) ^ (4487/1024 : ℝ) ≤ (11709255397121/100000000000000000000 : ℝ) := by
    have hpowers : (2619/100000 : ℝ)^4487 ≤ (11709255397121/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2619 : ℕ)^4487*100000000000000000000^1024 ≤ 11709255397121^1024*100000^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2619 100000 11709255397121 100000000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2619/100000 : ℝ)) (X := (11709255397121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25693/100000 : ℝ) ^ (4487/1024 : ℝ) ≤ (259361407825881303/100000000000000000000 : ℝ) := by
    have hpowers : (25693/100000 : ℝ)^4487 ≤ (259361407825881303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25693 : ℕ)^4487*100000000000000000000^1024 ≤ 259361407825881303^1024*100000^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25693 100000 259361407825881303 100000000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25693/100000 : ℝ)) (X := (259361407825881303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000011709255397121/50000000000000000000 : ℝ) ≤ (1250000066805641/1250000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (50000011709255397121/50000000000000000000 : ℝ)^1024 ≤ (1250000066805641/1250000000000000 : ℝ)^4487 := by
      have hnat : (50000011709255397121 : ℕ)^1024*1250000000000000^4487 ≤ 1250000066805641^4487*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000011709255397121 50000000000000000000 1250000066805641 1250000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000066805641/1250000000000000 : ℝ)) (X := (50000011709255397121/50000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12532421639635159803/12500000000000000000 : ℝ) ≤ (10005913363959103/10000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (12532421639635159803/12500000000000000000 : ℝ)^1024 ≤ (10005913363959103/10000000000000000 : ℝ)^4487 := by
      have hnat : (12532421639635159803 : ℕ)^1024*10000000000000000^4487 ≤ 10005913363959103^4487*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12532421639635159803 12500000000000000000 10005913363959103 10000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005913363959103/10000000000000000 : ℝ)) (X := (12532421639635159803/12500000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50259361407825881303/50000000000000000000 : ℝ) ≤ (5005913096736539/5000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (50259361407825881303/50000000000000000000 : ℝ)^1024 ≤ (5005913096736539/5000000000000000 : ℝ)^4487 := by
      have hnat : (50259361407825881303 : ℕ)^1024*5000000000000000^4487 ≤ 5005913096736539^4487*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50259361407825881303 50000000000000000000 5005913096736539 5000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005913096736539/5000000000000000 : ℝ)) (X := (50259361407825881303/50000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11709255397121/100000000000000000000 : ℝ) ≤ ((115354520465396341211/115370000000000000000 : ℝ)+2*(236513180559/92296000000000 : ℝ)*(2619/100000 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (115354520465396341211/115370000000000000000 : ℝ)+2*(236513180559/92296000000000 : ℝ)*(2619/100000 : ℝ)=(1250000066805641/1250000000000000 : ℝ) by norm_num, show 1+2*(11709255397121/100000000000000000000 : ℝ)=(50000011709255397121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(259361407825881303/100000000000000000000 : ℝ)+(11709255397121/100000000000000000000 : ℝ) ≤ ((115354520465396341211/115370000000000000000 : ℝ)+(236513180559/92296000000000 : ℝ)*((25693/100000 : ℝ)+(2619/100000 : ℝ)))^(4487/1024 : ℝ) := by
    rw [show (115354520465396341211/115370000000000000000 : ℝ)+(236513180559/92296000000000 : ℝ)*((25693/100000 : ℝ)+(2619/100000 : ℝ))=(10005913363959103/10000000000000000 : ℝ) by norm_num, show 1+(259361407825881303/100000000000000000000 : ℝ)+(11709255397121/100000000000000000000 : ℝ)=(12532421639635159803/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(259361407825881303/100000000000000000000 : ℝ) ≤ ((115354520465396341211/115370000000000000000 : ℝ)+2*(236513180559/92296000000000 : ℝ)*(25693/100000 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (115354520465396341211/115370000000000000000 : ℝ)+2*(236513180559/92296000000000 : ℝ)*(25693/100000 : ℝ)=(5005913096736539/5000000000000000 : ℝ) by norm_num, show 1+2*(259361407825881303/100000000000000000000 : ℝ)=(50259361407825881303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (115354520465396341211/115370000000000000000 : ℝ)*(X 1 0+X 2 0)+(236513180559/92296000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (2619/100000 : ℝ)) (hi := (25693/100000 : ℝ)) (c := (115354520465396341211/115370000000000000000 : ℝ)) (alpha := (236513180559/92296000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (115354520465396341211/115370000000000000000 : ℝ)*(X 0 1+X 2 1)+(236513180559/92296000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (2619/100000 : ℝ)) (hi := (25693/100000 : ℝ)) (c := (115354520465396341211/115370000000000000000 : ℝ)) (alpha := (236513180559/92296000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (115354520465396341211/115370000000000000000 : ℝ)*(X 0 2+X 1 2)+(236513180559/92296000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (2619/100000 : ℝ)) (hi := (25693/100000 : ℝ)) (c := (115354520465396341211/115370000000000000000 : ℝ)) (alpha := (236513180559/92296000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-116310381/625000000 : ℝ)*X 0 0+(5581386511/10000000000 : ℝ)*X 0 1+(5090782969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5389565061/10000000000 : ℝ)*X 1 0+(-2119827671/10000000000 : ℝ)*X 1 1+(127269593/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5389565707/10000000000 : ℝ)*X 2 0+(5090783299/10000000000 : ℝ)*X 2 1+(-1059913683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4255444451/10000000000 : ℝ)*X 0 0+(1867935577/5000000000 : ℝ)*X 0 1+(241791229/500000000 : ℝ)*X 0 2+(4255444451/10000000000 : ℝ)*X 1 0+(1867935577/5000000000 : ℝ)*X 1 1+(241791229/500000000 : ℝ)*X 1 2+(4255444451/10000000000 : ℝ)*X 2 0+(1867935577/5000000000 : ℝ)*X 2 1+(241791229/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-232662459/1250000000 : ℝ)*X 0 0+(2548197647/5000000000 : ℝ)*X 0 1+(1115136371/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260597807/10000000000 : ℝ)*X 1 0+(-1634929121/10000000000 : ℝ)*X 1 1+(5575681961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630298863/5000000000 : ℝ)*X 2 0+(223027279/400000000 : ℝ)*X 2 1+(-25545769/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4256192897/10000000000 : ℝ)*X 0 0+(2411621347/5000000000 : ℝ)*X 0 1+(1874330321/5000000000 : ℝ)*X 0 2+(4256192897/10000000000 : ℝ)*X 1 0+(2411621347/5000000000 : ℝ)*X 1 1+(1874330321/5000000000 : ℝ)*X 1 2+(4256192897/10000000000 : ℝ)*X 2 0+(2411621347/5000000000 : ℝ)*X 2 1+(1874330321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1043207255815260751541923179/144212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (786093913/50000000000000 : ℝ)*(base19) + (1793433627/100000000000000 : ℝ)*(base23) + (109738963/100000000000000 : ℝ)*(upper3) + (12434507/100000000000000 : ℝ)*(upper4) + (7287621/2500000000000 : ℝ)*(upper5) + (73686953587163/5000000000000 : ℝ)*(major0) + (73686953587163/5000000000000 : ℝ)*(major1) + (73686953587163/5000000000000 : ℝ)*(major2) + (2038318890914527/100000000000000 : ℝ)*(sp0) + (2038334129675919/100000000000000 : ℝ)*(sp1) + (2038333908430117/100000000000000 : ℝ)*(sp2) + (909136060704979/100000000000000 : ℝ)*(sp3) + (8405474609/50000000000000 : ℝ)*(sp4) + (6139790459/100000000000000 : ℝ)*(sp7) + (454571100247719/50000000000000 : ℝ)*(f.failure) + (31848995341621/1562500000000 : ℝ)*(f.sum) + (7039675216109/5768500000000000000000000000 : ℝ)*base66 + (1577452162698125607/576850000000000000000000000000000 : ℝ)*base68 + (428523202520625607/576850000000000000000000000000000 : ℝ)*base70 + (4390345592726625607/576850000000000000000000000000000 : ℝ)*base72 + (71184623107819/11537000000000000000000000000 : ℝ)*base73 + (2912386594005575607/576850000000000000000000000000000 : ℝ)*base76 + (1093345299202374393/576850000000000000000000000000000 : ℝ)*base77 + (2265224991847025607/576850000000000000000000000000000 : ℝ)*base80 + (32203669607419/5768500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2126089/625000000000000000000 : ℝ)*base90 + (2126089/625000000000000000000 : ℝ)*base92 + (2126089/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97311438896184166223679/23074000000000000000000000000 : ℝ) := by norm_num
    linear_combination (829293633/100000000000000 : ℝ)*(base19) + (845999201/100000000000000 : ℝ)*(base23) + (127227461/100000000000000 : ℝ)*(upper3) + (19188111/100000000000000 : ℝ)*(lower4) + (51654309/100000000000000 : ℝ)*(upper5) + (1508514002136673/100000000000000 : ℝ)*(major0) + (1508514002136673/100000000000000 : ℝ)*(major1) + (1508514002136673/100000000000000 : ℝ)*(major2) + (2699479871/50000000000000 : ℝ)*(sp1) + (5902939547/100000000000000 : ℝ)*(sp2) + (2086433184028209/100000000000000 : ℝ)*(sp4) + (1043213477887417/50000000000000 : ℝ)*(sp5) + (104321321754473/5000000000000 : ℝ)*(sp6) + (465297339833179/50000000000000 : ℝ)*(sp7) + (465297339833179/50000000000000 : ℝ)*(f.failure) + (2086433184028209/100000000000000 : ℝ)*(f.sum) + (49014772757137/23074000000000000000000000000 : ℝ)*base66 + (109109839966402918997/11537000000000000000000000000000000 : ℝ)*base68 + (23933775326676081003/11537000000000000000000000000000000 : ℝ)*base69 + (61344185602938918997/11537000000000000000000000000000000 : ℝ)*base72 + (13248110959509/23074000000000000000000000000 : ℝ)*base74 + (39417299406526918997/11537000000000000000000000000000000 : ℝ)*base76 + (8651723406168081003/11537000000000000000000000000000000 : ℝ)*base77 + (3977442210638081003/11537000000000000000000000000000000 : ℝ)*base79 + (79619002428759/23074000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1637349/625000000000000000000 : ℝ)*base90 + (1637349/625000000000000000000 : ℝ)*base92 + (1637349/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1496_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2619/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1017/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1851/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1496_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1496_s2_0 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-188738607/1000000000 : ℝ)*x 0 + (1365805653/2500000000 : ℝ)*x 1 + (2595931251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188738607/1000000000 : ℝ)^4489 ≤ (2882692200293/25000000000000 : ℝ)^3465 := by
    have hnat : (188738607 : ℕ)^4489*25000000000000^3465 ≤ 2882692200293^3465*1000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188738607 1000000000 2882692200293 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365805653/2500000000 : ℝ)^4489 ≤ (45693880063509/100000000000000 : ℝ)^3465 := by
    have hnat : (1365805653 : ℕ)^4489*100000000000000^3465 ≤ 45693880063509^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365805653 2500000000 45693880063509 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595931251/5000000000 : ℝ)^4489 ≤ (42775351123593/100000000000000 : ℝ)^3465 := by
    have hnat : (2595931251 : ℕ)^4489*100000000000000^3465 ≤ 42775351123593^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595931251 5000000000 42775351123593 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-188738607/1000000000 : ℝ), (1365805653/2500000000 : ℝ), (2595931251/5000000000 : ℝ)] ![(2882692200293/25000000000000 : ℝ), (45693880063509/100000000000000 : ℝ), (42775351123593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-188738607/1000000000 : ℝ)|^4489 ≤ (2882692200293/25000000000000 : ℝ)^3465
        have hw : |(-188738607/1000000000 : ℝ)|=(188738607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365805653/2500000000 : ℝ)|^4489 ≤ (45693880063509/100000000000000 : ℝ)^3465
        have hw : |(1365805653/2500000000 : ℝ)|=(1365805653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595931251/5000000000 : ℝ)|^4489 ≤ (42775351123593/100000000000000 : ℝ)^3465
        have hw : |(2595931251/5000000000 : ℝ)|=(2595931251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s2_1 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359695191/10000000000 : ℝ)*x 0 + (-2027214961/10000000000 : ℝ)*x 1 + (5191861953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359695191/10000000000 : ℝ)^4489 ≤ (8915049396589/20000000000000 : ℝ)^3465 := by
    have hnat : (5359695191 : ℕ)^4489*20000000000000^3465 ≤ 8915049396589^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359695191 10000000000 8915049396589 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2027214961/10000000000 : ℝ)^4489 ≤ (12649407736483/100000000000000 : ℝ)^3465 := by
    have hnat : (2027214961 : ℕ)^4489*100000000000000^3465 ≤ 12649407736483^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027214961 10000000000 12649407736483 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191861953/10000000000 : ℝ)^4489 ≤ (10693836315927/25000000000000 : ℝ)^3465 := by
    have hnat : (5191861953 : ℕ)^4489*25000000000000^3465 ≤ 10693836315927^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191861953 10000000000 10693836315927 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359695191/10000000000 : ℝ), (-2027214961/10000000000 : ℝ), (5191861953/10000000000 : ℝ)] ![(8915049396589/20000000000000 : ℝ), (12649407736483/100000000000000 : ℝ), (10693836315927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359695191/10000000000 : ℝ)|^4489 ≤ (8915049396589/20000000000000 : ℝ)^3465
        have hw : |(5359695191/10000000000 : ℝ)|=(5359695191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2027214961/10000000000 : ℝ)|^4489 ≤ (12649407736483/100000000000000 : ℝ)^3465
        have hw : |(-2027214961/10000000000 : ℝ)|=(2027214961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5191861953/10000000000 : ℝ)|^4489 ≤ (10693836315927/25000000000000 : ℝ)^3465
        have hw : |(5191861953/10000000000 : ℝ)|=(5191861953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s2_2 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214387807/400000000 : ℝ)*x 0 + (1297965441/2500000000 : ℝ)*x 1 + (-2027215231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214387807/400000000 : ℝ)^4489 ≤ (5571905851319/12500000000000 : ℝ)^3465 := by
    have hnat : (214387807 : ℕ)^4489*12500000000000^3465 ≤ 5571905851319^3465*400000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214387807 400000000 5571905851319 12500000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1297965441/2500000000 : ℝ)^4489 ≤ (42775343246371/100000000000000 : ℝ)^3465 := by
    have hnat : (1297965441 : ℕ)^4489*100000000000000^3465 ≤ 42775343246371^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297965441 2500000000 42775343246371 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2027215231/10000000000 : ℝ)^4489 ≤ (2529881983823/20000000000000 : ℝ)^3465 := by
    have hnat : (2027215231 : ℕ)^4489*20000000000000^3465 ≤ 2529881983823^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027215231 10000000000 2529881983823 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214387807/400000000 : ℝ), (1297965441/2500000000 : ℝ), (-2027215231/10000000000 : ℝ)] ![(5571905851319/12500000000000 : ℝ), (42775343246371/100000000000000 : ℝ), (2529881983823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214387807/400000000 : ℝ)|^4489 ≤ (5571905851319/12500000000000 : ℝ)^3465
        have hw : |(214387807/400000000 : ℝ)|=(214387807/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1297965441/2500000000 : ℝ)|^4489 ≤ (42775343246371/100000000000000 : ℝ)^3465
        have hw : |(1297965441/2500000000 : ℝ)|=(1297965441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2027215231/10000000000 : ℝ)|^4489 ≤ (2529881983823/20000000000000 : ℝ)^3465
        have hw : |(-2027215231/10000000000 : ℝ)|=(2027215231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s2_3 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274354679/10000000000 : ℝ)*x 0 + (3979458161/10000000000 : ℝ)*x 1 + (2293929691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274354679/10000000000 : ℝ)^4489 ≤ (16624667041173/50000000000000 : ℝ)^3465 := by
    have hnat : (4274354679 : ℕ)^4489*50000000000000^3465 ≤ 16624667041173^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274354679 10000000000 16624667041173 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979458161/10000000000 : ℝ)^4489 ≤ (3788534515553/12500000000000 : ℝ)^3465 := by
    have hnat : (3979458161 : ℕ)^4489*12500000000000^3465 ≤ 3788534515553^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979458161 10000000000 3788534515553 12500000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293929691/5000000000 : ℝ)^4489 ≤ (4555298721597/12500000000000 : ℝ)^3465 := by
    have hnat : (2293929691 : ℕ)^4489*12500000000000^3465 ≤ 4555298721597^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293929691 5000000000 4555298721597 12500000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274354679/10000000000 : ℝ), (3979458161/10000000000 : ℝ), (2293929691/5000000000 : ℝ)] ![(16624667041173/50000000000000 : ℝ), (3788534515553/12500000000000 : ℝ), (4555298721597/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274354679/10000000000 : ℝ)|^4489 ≤ (16624667041173/50000000000000 : ℝ)^3465
        have hw : |(4274354679/10000000000 : ℝ)|=(4274354679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979458161/10000000000 : ℝ)|^4489 ≤ (3788534515553/12500000000000 : ℝ)^3465
        have hw : |(3979458161/10000000000 : ℝ)|=(3979458161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2293929691/5000000000 : ℝ)|^4489 ≤ (4555298721597/12500000000000 : ℝ)^3465
        have hw : |(2293929691/5000000000 : ℝ)|=(2293929691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s2_4 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-471860317/2500000000 : ℝ)*x 0 + (1298397443/2500000000 : ℝ)*x 1 + (1365370167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471860317/2500000000 : ℝ)^4489 ≤ (5765602844077/50000000000000 : ℝ)^3465 := by
    have hnat : (471860317 : ℕ)^4489*50000000000000^3465 ≤ 5765602844077^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471860317 2500000000 5765602844077 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298397443/2500000000 : ℝ)^4489 ≤ (8558757693399/20000000000000 : ℝ)^3465 := by
    have hnat : (1298397443 : ℕ)^4489*20000000000000^3465 ≤ 8558757693399^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298397443 2500000000 8558757693399 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365370167/2500000000 : ℝ)^4489 ≤ (11418751458493/25000000000000 : ℝ)^3465 := by
    have hnat : (1365370167 : ℕ)^4489*25000000000000^3465 ≤ 11418751458493^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365370167 2500000000 11418751458493 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471860317/2500000000 : ℝ), (1298397443/2500000000 : ℝ), (1365370167/2500000000 : ℝ)] ![(5765602844077/50000000000000 : ℝ), (8558757693399/20000000000000 : ℝ), (11418751458493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471860317/2500000000 : ℝ)|^4489 ≤ (5765602844077/50000000000000 : ℝ)^3465
        have hw : |(-471860317/2500000000 : ℝ)|=(471860317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298397443/2500000000 : ℝ)|^4489 ≤ (8558757693399/20000000000000 : ℝ)^3465
        have hw : |(1298397443/2500000000 : ℝ)|=(1298397443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365370167/2500000000 : ℝ)|^4489 ≤ (11418751458493/25000000000000 : ℝ)^3465
        have hw : |(1365370167/2500000000 : ℝ)|=(1365370167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s2_5 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288613581/10000000000 : ℝ)*x 0 + (-878797959/5000000000 : ℝ)*x 1 + (2730740661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288613581/10000000000 : ℝ)^4489 ≤ (43810878613111/100000000000000 : ℝ)^3465 := by
    have hnat : (5288613581 : ℕ)^4489*100000000000000^3465 ≤ 43810878613111^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288613581 10000000000 43810878613111 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878797959/5000000000 : ℝ)^4489 ≤ (1051410846401/10000000000000 : ℝ)^3465 := by
    have hnat : (878797959 : ℕ)^4489*10000000000000^3465 ≤ 1051410846401^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878797959 5000000000 1051410846401 10000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730740661/5000000000 : ℝ)^4489 ≤ (11418753229957/25000000000000 : ℝ)^3465 := by
    have hnat : (2730740661 : ℕ)^4489*25000000000000^3465 ≤ 11418753229957^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730740661 5000000000 11418753229957 25000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288613581/10000000000 : ℝ), (-878797959/5000000000 : ℝ), (2730740661/5000000000 : ℝ)] ![(43810878613111/100000000000000 : ℝ), (1051410846401/10000000000000 : ℝ), (11418753229957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288613581/10000000000 : ℝ)|^4489 ≤ (43810878613111/100000000000000 : ℝ)^3465
        have hw : |(5288613581/10000000000 : ℝ)|=(5288613581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878797959/5000000000 : ℝ)|^4489 ≤ (1051410846401/10000000000000 : ℝ)^3465
        have hw : |(-878797959/5000000000 : ℝ)|=(878797959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730740661/5000000000 : ℝ)|^4489 ≤ (11418753229957/25000000000000 : ℝ)^3465
        have hw : |(2730740661/5000000000 : ℝ)|=(2730740661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s2_6 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644306703/5000000000 : ℝ)*x 0 + (2730740113/5000000000 : ℝ)*x 1 + (-1757597691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644306703/5000000000 : ℝ)^4489 ≤ (21905438367493/50000000000000 : ℝ)^3465 := by
    have hnat : (2644306703 : ℕ)^4489*50000000000000^3465 ≤ 21905438367493^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644306703 5000000000 21905438367493 50000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730740113/5000000000 : ℝ)^4489 ≤ (2283750052253/5000000000000 : ℝ)^3465 := by
    have hnat : (2730740113 : ℕ)^4489*5000000000000^3465 ≤ 2283750052253^3465*5000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730740113 5000000000 2283750052253 5000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1757597691/10000000000 : ℝ)^4489 ≤ (10514122204701/100000000000000 : ℝ)^3465 := by
    have hnat : (1757597691 : ℕ)^4489*100000000000000^3465 ≤ 10514122204701^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757597691 10000000000 10514122204701 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644306703/5000000000 : ℝ), (2730740113/5000000000 : ℝ), (-1757597691/10000000000 : ℝ)] ![(21905438367493/50000000000000 : ℝ), (2283750052253/5000000000000 : ℝ), (10514122204701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644306703/5000000000 : ℝ)|^4489 ≤ (21905438367493/50000000000000 : ℝ)^3465
        have hw : |(2644306703/5000000000 : ℝ)|=(2644306703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730740113/5000000000 : ℝ)|^4489 ≤ (2283750052253/5000000000000 : ℝ)^3465
        have hw : |(2730740113/5000000000 : ℝ)|=(2730740113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1757597691/10000000000 : ℝ)|^4489 ≤ (10514122204701/100000000000000 : ℝ)^3465
        have hw : |(-1757597691/10000000000 : ℝ)|=(1757597691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1496_s2_7 (p : ℝ) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068620709/2500000000 : ℝ)*x 0 + (458399049/1000000000 : ℝ)*x 1 + (3983361223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068620709/2500000000 : ℝ)^4489 ≤ (4156328200993/12500000000000 : ℝ)^3465 := by
    have hnat : (1068620709 : ℕ)^4489*12500000000000^3465 ≤ 4156328200993^3465*2500000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068620709 2500000000 4156328200993 12500000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458399049/1000000000 : ℝ)^4489 ≤ (7280516258593/20000000000000 : ℝ)^3465 := by
    have hnat : (458399049 : ℕ)^4489*20000000000000^3465 ≤ 7280516258593^3465*1000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458399049 1000000000 7280516258593 20000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983361223/10000000000 : ℝ)^4489 ≤ (30346793086909/100000000000000 : ℝ)^3465 := by
    have hnat : (3983361223 : ℕ)^4489*100000000000000^3465 ≤ 30346793086909^3465*10000000000^4489 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983361223 10000000000 30346793086909 100000000000000 4489 3465 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4489/1024 : ℝ)) 4489 3465 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068620709/2500000000 : ℝ), (458399049/1000000000 : ℝ), (3983361223/10000000000 : ℝ)] ![(4156328200993/12500000000000 : ℝ), (7280516258593/20000000000000 : ℝ), (30346793086909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068620709/2500000000 : ℝ)|^4489 ≤ (4156328200993/12500000000000 : ℝ)^3465
        have hw : |(1068620709/2500000000 : ℝ)|=(1068620709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458399049/1000000000 : ℝ)|^4489 ≤ (7280516258593/20000000000000 : ℝ)^3465
        have hw : |(458399049/1000000000 : ℝ)|=(458399049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983361223/10000000000 : ℝ)|^4489 ≤ (30346793086909/100000000000000 : ℝ)^3465
        have hw : |(3983361223/10000000000 : ℝ)|=(3983361223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1496_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1851/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1017/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5159/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (803/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1851/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1017/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1851/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1017/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1851/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1017/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1851/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1017/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1851/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1017/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1851/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1017/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1017/12500 : ℝ) ^ (4487/1024 : ℝ) ≤ (1681123036732737/100000000000000000000 : ℝ) := by
    have hpowers : (1017/12500 : ℝ)^4487 ≤ (1681123036732737/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1017 : ℕ)^4487*100000000000000000000^1024 ≤ 1681123036732737^1024*12500^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1017 12500 1681123036732737 100000000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1017/12500 : ℝ)) (X := (1681123036732737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1851/10000 : ℝ) ^ (4487/1024 : ℝ) ≤ (30822305623496919/50000000000000000000 : ℝ) := by
    have hpowers : (1851/10000 : ℝ)^4487 ≤ (30822305623496919/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1851 : ℕ)^4487*50000000000000000000^1024 ≤ 30822305623496919^1024*10000^4487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1851 10000 30822305623496919 50000000000000000000 4487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1851/10000 : ℝ)) (X := (30822305623496919/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001681123036732737/50000000000000000000 : ℝ) ≤ (5000038365225197/5000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (50001681123036732737/50000000000000000000 : ℝ)^1024 ≤ (5000038365225197/5000000000000000 : ℝ)^4487 := by
      have hnat : (50001681123036732737 : ℕ)^1024*5000000000000000^4487 ≤ 5000038365225197^4487*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001681123036732737 50000000000000000000 5000038365225197 5000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038365225197/5000000000000000 : ℝ)) (X := (50001681123036732737/50000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002533029371349063/4000000000000000000 : ℝ) ≤ (10001444834222593/10000000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (4002533029371349063/4000000000000000000 : ℝ)^1024 ≤ (10001444834222593/10000000000000000 : ℝ)^4487 := by
      have hnat : (4002533029371349063 : ℕ)^1024*10000000000000000^4487 ≤ 10001444834222593^4487*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002533029371349063 4000000000000000000 10001444834222593 10000000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001444834222593/10000000000000000 : ℝ)) (X := (4002533029371349063/4000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25030822305623496919/25000000000000000000 : ℝ) ≤ (1250351617249349/1250000000000000 : ℝ) ^ (4487/1024 : ℝ) := by
    have hpowers : (25030822305623496919/25000000000000000000 : ℝ)^1024 ≤ (1250351617249349/1250000000000000 : ℝ)^4487 := by
      have hnat : (25030822305623496919 : ℕ)^1024*1250000000000000^4487 ≤ 1250351617249349^4487*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030822305623496919 25000000000000000000 1250351617249349 1250000000000000 1024 4487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250351617249349/1250000000000000 : ℝ)) (X := (25030822305623496919/25000000000000000000 : ℝ)) (by norm_num) 4487 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1681123036732737/100000000000000000000 : ℝ) ≤ ((8643211184759263769/8645000000000000000 : ℝ)+2*(456034590733/345800000000000 : ℝ)*(1017/12500 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (8643211184759263769/8645000000000000000 : ℝ)+2*(456034590733/345800000000000 : ℝ)*(1017/12500 : ℝ)=(5000038365225197/5000000000000000 : ℝ) by norm_num, show 1+2*(1681123036732737/100000000000000000000 : ℝ)=(50001681123036732737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30822305623496919/50000000000000000000 : ℝ)+(1681123036732737/100000000000000000000 : ℝ) ≤ ((8643211184759263769/8645000000000000000 : ℝ)+(456034590733/345800000000000 : ℝ)*((1851/10000 : ℝ)+(1017/12500 : ℝ)))^(4487/1024 : ℝ) := by
    rw [show (8643211184759263769/8645000000000000000 : ℝ)+(456034590733/345800000000000 : ℝ)*((1851/10000 : ℝ)+(1017/12500 : ℝ))=(10001444834222593/10000000000000000 : ℝ) by norm_num, show 1+(30822305623496919/50000000000000000000 : ℝ)+(1681123036732737/100000000000000000000 : ℝ)=(4002533029371349063/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30822305623496919/50000000000000000000 : ℝ) ≤ ((8643211184759263769/8645000000000000000 : ℝ)+2*(456034590733/345800000000000 : ℝ)*(1851/10000 : ℝ))^(4487/1024 : ℝ) := by
    rw [show (8643211184759263769/8645000000000000000 : ℝ)+2*(456034590733/345800000000000 : ℝ)*(1851/10000 : ℝ)=(1250351617249349/1250000000000000 : ℝ) by norm_num, show 1+2*(30822305623496919/50000000000000000000 : ℝ)=(25030822305623496919/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8643211184759263769/8645000000000000000 : ℝ)*(X 1 0+X 2 0)+(456034590733/345800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (1017/12500 : ℝ)) (hi := (1851/10000 : ℝ)) (c := (8643211184759263769/8645000000000000000 : ℝ)) (alpha := (456034590733/345800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8643211184759263769/8645000000000000000 : ℝ)*(X 0 1+X 2 1)+(456034590733/345800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (1017/12500 : ℝ)) (hi := (1851/10000 : ℝ)) (c := (8643211184759263769/8645000000000000000 : ℝ)) (alpha := (456034590733/345800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8643211184759263769/8645000000000000000 : ℝ)*(X 0 2+X 1 2)+(456034590733/345800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4487/1024 : ℝ)) (lo := (1017/12500 : ℝ)) (hi := (1851/10000 : ℝ)) (c := (8643211184759263769/8645000000000000000 : ℝ)) (alpha := (456034590733/345800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-188738607/1000000000 : ℝ)*X 0 0+(1365805653/2500000000 : ℝ)*X 0 1+(2595931251/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359695191/10000000000 : ℝ)*X 1 0+(-2027214961/10000000000 : ℝ)*X 1 1+(5191861953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214387807/400000000 : ℝ)*X 2 0+(1297965441/2500000000 : ℝ)*X 2 1+(-2027215231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4274354679/10000000000 : ℝ)*X 0 0+(3979458161/10000000000 : ℝ)*X 0 1+(2293929691/5000000000 : ℝ)*X 0 2+(4274354679/10000000000 : ℝ)*X 1 0+(3979458161/10000000000 : ℝ)*X 1 1+(2293929691/5000000000 : ℝ)*X 1 2+(4274354679/10000000000 : ℝ)*X 2 0+(3979458161/10000000000 : ℝ)*X 2 1+(2293929691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-471860317/2500000000 : ℝ)*X 0 0+(1298397443/2500000000 : ℝ)*X 0 1+(1365370167/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288613581/10000000000 : ℝ)*X 1 0+(-878797959/5000000000 : ℝ)*X 1 1+(2730740661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644306703/5000000000 : ℝ)*X 2 0+(2730740113/5000000000 : ℝ)*X 2 1+(-1757597691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1068620709/2500000000 : ℝ)*X 0 0+(458399049/1000000000 : ℝ)*X 0 1+(3983361223/10000000000 : ℝ)*X 0 2+(1068620709/2500000000 : ℝ)*X 1 0+(458399049/1000000000 : ℝ)*X 1 1+(3983361223/10000000000 : ℝ)*X 1 2+(1068620709/2500000000 : ℝ)*X 2 0+(458399049/1000000000 : ℝ)*X 2 1+(3983361223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1496_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1577250780588740200543840203/216125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (192000021/6250000000000 : ℝ)*(base19) + (2713970197/100000000000000 : ℝ)*(base23) + (14027977/100000000000000 : ℝ)*(upper2) + (232819443/50000000000000 : ℝ)*(upper3) + (20002489/10000000000000 : ℝ)*(upper4) + (1332222798188929/50000000000000 : ℝ)*(major0) + (1332222798188929/50000000000000 : ℝ)*(major1) + (1332222798188929/50000000000000 : ℝ)*(major2) + (1842588945048689/50000000000000 : ℝ)*(sp0) + (1842602413663771/50000000000000 : ℝ)*(sp1) + (46065064816971/1250000000000 : ℝ)*(sp2) + (821832546716533/50000000000000 : ℝ)*(sp3) + (60018461/200000000000 : ℝ)*(sp4) + (8978366323/50000000000000 : ℝ)*(sp7) + (102730190635357/6250000000000 : ℝ)*(f.failure) + (1842603949663939/50000000000000 : ℝ)*(f.sum) + (16623208805507/8645000000000000000000000000 : ℝ)*base65 + (1120430314758961599/432250000000000000000000000000000 : ℝ)*base68 + (570549180992038401/432250000000000000000000000000000 : ℝ)*base69 + (1099286758461461599/432250000000000000000000000000000 : ℝ)*base72 + (8918019173123/8645000000000000000000000000 : ℝ)*base74 + (3192669360590461599/432250000000000000000000000000000 : ℝ)*base76 + (670369173173038401/432250000000000000000000000000000 : ℝ)*base77 + (3149321121792961599/432250000000000000000000000000000 : ℝ)*base80 + (14724716837407/8645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (561033/78125000000000000000 : ℝ)*base89 + (561033/78125000000000000000 : ℝ)*base91 + (561033/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24592232246939371837330647/6175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53387321/20000000000000 : ℝ)*(base19) + (908860141/100000000000000 : ℝ)*(base23) + (30890511/6250000000000 : ℝ)*(lower4) + (15531807/50000000000000 : ℝ)*(lower5) + (539778764154153/20000000000000 : ℝ)*(major0) + (539778764154153/20000000000000 : ℝ)*(major1) + (539778764154153/20000000000000 : ℝ)*(major2) + (13547924971/100000000000000 : ℝ)*(sp1) + (241487033/25000000000000 : ℝ)*(sp2) + (510056077/6250000000000 : ℝ)*(sp3) + (933213380684313/25000000000000 : ℝ)*(sp4) + (933209926968919/25000000000000 : ℝ)*(sp5) + (186642582396449/5000000000000 : ℝ)*(sp6) + (832462912577721/50000000000000 : ℝ)*(sp7) + (832466993026337/50000000000000 : ℝ)*(f.failure) + (933213380684313/25000000000000 : ℝ)*(f.sum) + (11344705186683/3458000000000000000000000000 : ℝ)*base66 + (3182988910907107657/172900000000000000000000000000000 : ℝ)*base67 + (1753165206962107657/172900000000000000000000000000000 : ℝ)*base69 + (1652137708672207657/172900000000000000000000000000000 : ℝ)*base71 + (3951275661687/691600000000000000000000000 : ℝ)*base73 + (3557513695805007657/172900000000000000000000000000000 : ℝ)*base75 + (127677387450492343/172900000000000000000000000000000 : ℝ)*base78 + (3316158603053507657/172900000000000000000000000000000 : ℝ)*base79 + (1396368819381/691600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3702847/625000000000000000000 : ℝ)*base90 + (3702847/625000000000000000000 : ℝ)*base92 + (3702847/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1496_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1851/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1017/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (803/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1496_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1496_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (803/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1496_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1496_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1496_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4487/1024 : ℝ) ≤ p) (hpb : p ≤ (4489/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20262769/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (803/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1496_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

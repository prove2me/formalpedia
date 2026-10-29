-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1693_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:32.456566+00:00
-- url     : https://prove2.me/submissions/96669fea-68dc-4c6b-bbbc-3a93164b9a1e

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
theorem support_rectangle_w1693_s3_0 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1475944907/10000000000 : ℝ)*x 0 + (21410853/39062500 : ℝ)*x 1 + (5135815959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1475944907/10000000000 : ℝ)^5167 ≤ (9198018763299/100000000000000 : ℝ)^4143 := by
    have hnat : (1475944907 : ℕ)^5167*100000000000000^4143 ≤ 9198018763299^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475944907 10000000000 9198018763299 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21410853/39062500 : ℝ)^5167 ≤ (23621257022213/50000000000000 : ℝ)^4143 := by
    have hnat : (21410853 : ℕ)^5167*50000000000000^4143 ≤ 23621257022213^4143*39062500^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21410853 39062500 23621257022213 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135815959/10000000000 : ℝ)^5167 ≤ (21779733587147/50000000000000 : ℝ)^4143 := by
    have hnat : (5135815959 : ℕ)^5167*50000000000000^4143 ≤ 21779733587147^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135815959 10000000000 21779733587147 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1475944907/10000000000 : ℝ), (21410853/39062500 : ℝ), (5135815959/10000000000 : ℝ)] ![(9198018763299/100000000000000 : ℝ), (23621257022213/50000000000000 : ℝ), (21779733587147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1475944907/10000000000 : ℝ)|^5167 ≤ (9198018763299/100000000000000 : ℝ)^4143
        have hw : |(-1475944907/10000000000 : ℝ)|=(1475944907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21410853/39062500 : ℝ)|^5167 ≤ (23621257022213/50000000000000 : ℝ)^4143
        have hw : |(21410853/39062500 : ℝ)|=(21410853/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135815959/10000000000 : ℝ)|^5167 ≤ (21779733587147/50000000000000 : ℝ)^4143
        have hw : |(5135815959/10000000000 : ℝ)|=(5135815959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s3_1 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349216883/10000000000 : ℝ)*x 0 + (-827645593/5000000000 : ℝ)*x 1 + (5135816177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349216883/10000000000 : ℝ)^5167 ≤ (45828258795289/100000000000000 : ℝ)^4143 := by
    have hnat : (5349216883 : ℕ)^5167*100000000000000^4143 ≤ 45828258795289^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349216883 10000000000 45828258795289 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827645593/5000000000 : ℝ)^5167 ≤ (663266981489/6250000000000 : ℝ)^4143 := by
    have hnat : (827645593 : ℕ)^5167*6250000000000^4143 ≤ 663266981489^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827645593 5000000000 663266981489 6250000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135816177/10000000000 : ℝ)^5167 ≤ (21779734740131/50000000000000 : ℝ)^4143 := by
    have hnat : (5135816177 : ℕ)^5167*50000000000000^4143 ≤ 21779734740131^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135816177 10000000000 21779734740131 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349216883/10000000000 : ℝ), (-827645593/5000000000 : ℝ), (5135816177/10000000000 : ℝ)] ![(45828258795289/100000000000000 : ℝ), (663266981489/6250000000000 : ℝ), (21779734740131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349216883/10000000000 : ℝ)|^5167 ≤ (45828258795289/100000000000000 : ℝ)^4143
        have hw : |(5349216883/10000000000 : ℝ)|=(5349216883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-827645593/5000000000 : ℝ)|^5167 ≤ (663266981489/6250000000000 : ℝ)^4143
        have hw : |(-827645593/5000000000 : ℝ)|=(827645593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135816177/10000000000 : ℝ)|^5167 ≤ (21779734740131/50000000000000 : ℝ)^4143
        have hw : |(5135816177/10000000000 : ℝ)|=(5135816177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s3_2 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069843391/2000000000 : ℝ)*x 0 + (205432649/400000000 : ℝ)*x 1 + (-1655291027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069843391/2000000000 : ℝ)^5167 ≤ (9165651912919/20000000000000 : ℝ)^4143 := by
    have hnat : (1069843391 : ℕ)^5167*20000000000000^4143 ≤ 9165651912919^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069843391 2000000000 9165651912919 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205432649/400000000 : ℝ)^5167 ≤ (21779734993999/50000000000000 : ℝ)^4143 := by
    have hnat : (205432649 : ℕ)^5167*50000000000000^4143 ≤ 21779734993999^4143*400000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205432649 400000000 21779734993999 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1655291027/10000000000 : ℝ)^5167 ≤ (2122454086501/20000000000000 : ℝ)^4143 := by
    have hnat : (1655291027 : ℕ)^5167*20000000000000^4143 ≤ 2122454086501^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655291027 10000000000 2122454086501 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069843391/2000000000 : ℝ), (205432649/400000000 : ℝ), (-1655291027/10000000000 : ℝ)] ![(9165651912919/20000000000000 : ℝ), (21779734993999/50000000000000 : ℝ), (2122454086501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069843391/2000000000 : ℝ)|^5167 ≤ (9165651912919/20000000000000 : ℝ)^4143
        have hw : |(1069843391/2000000000 : ℝ)|=(1069843391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205432649/400000000 : ℝ)|^5167 ≤ (21779734993999/50000000000000 : ℝ)^4143
        have hw : |(205432649/400000000 : ℝ)|=(205432649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1655291027/10000000000 : ℝ)|^5167 ≤ (2122454086501/20000000000000 : ℝ)^4143
        have hw : |(-1655291027/10000000000 : ℝ)|=(1655291027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s3_3 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4127148573/10000000000 : ℝ)*x 0 + (916112809/2500000000 : ℝ)*x 1 + (925399403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4127148573/10000000000 : ℝ)^5167 ≤ (33162914205209/100000000000000 : ℝ)^4143 := by
    have hnat : (4127148573 : ℕ)^5167*100000000000000^4143 ≤ 33162914205209^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127148573 10000000000 33162914205209 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916112809/2500000000 : ℝ)^5167 ≤ (14296104234473/50000000000000 : ℝ)^4143 := by
    have hnat : (916112809 : ℕ)^5167*50000000000000^4143 ≤ 14296104234473^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916112809 2500000000 14296104234473 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925399403/2000000000 : ℝ)^5167 ≤ (38244877314141/100000000000000 : ℝ)^4143 := by
    have hnat : (925399403 : ℕ)^5167*100000000000000^4143 ≤ 38244877314141^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925399403 2000000000 38244877314141 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4127148573/10000000000 : ℝ), (916112809/2500000000 : ℝ), (925399403/2000000000 : ℝ)] ![(33162914205209/100000000000000 : ℝ), (14296104234473/50000000000000 : ℝ), (38244877314141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4127148573/10000000000 : ℝ)|^5167 ≤ (33162914205209/100000000000000 : ℝ)^4143
        have hw : |(4127148573/10000000000 : ℝ)|=(4127148573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916112809/2500000000 : ℝ)|^5167 ≤ (14296104234473/50000000000000 : ℝ)^4143
        have hw : |(916112809/2500000000 : ℝ)|=(916112809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(925399403/2000000000 : ℝ)|^5167 ≤ (38244877314141/100000000000000 : ℝ)^4143
        have hw : |(925399403/2000000000 : ℝ)|=(925399403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s3_4 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1476104929/10000000000 : ℝ)*x 0 + (5139584383/10000000000 : ℝ)*x 1 + (5477353707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1476104929/10000000000 : ℝ)^5167 ≤ (4599631256781/50000000000000 : ℝ)^4143 := by
    have hnat : (1476104929 : ℕ)^5167*50000000000000^4143 ≤ 4599631256781^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476104929 10000000000 4599631256781 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139584383/10000000000 : ℝ)^5167 ≤ (43599332541407/100000000000000 : ℝ)^4143 := by
    have hnat : (5139584383 : ℕ)^5167*100000000000000^4143 ≤ 43599332541407^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139584383 10000000000 43599332541407 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477353707/10000000000 : ℝ)^5167 ≤ (23600702466829/50000000000000 : ℝ)^4143 := by
    have hnat : (5477353707 : ℕ)^5167*50000000000000^4143 ≤ 23600702466829^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477353707 10000000000 23600702466829 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1476104929/10000000000 : ℝ), (5139584383/10000000000 : ℝ), (5477353707/10000000000 : ℝ)] ![(4599631256781/50000000000000 : ℝ), (43599332541407/100000000000000 : ℝ), (23600702466829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1476104929/10000000000 : ℝ)|^5167 ≤ (4599631256781/50000000000000 : ℝ)^4143
        have hw : |(-1476104929/10000000000 : ℝ)|=(1476104929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139584383/10000000000 : ℝ)|^5167 ≤ (43599332541407/100000000000000 : ℝ)^4143
        have hw : |(5139584383/10000000000 : ℝ)|=(5139584383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477353707/10000000000 : ℝ)|^5167 ≤ (23600702466829/50000000000000 : ℝ)^4143
        have hw : |(5477353707/10000000000 : ℝ)|=(5477353707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s3_5 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328553757/625000000 : ℝ)*x 0 + (-656876493/5000000000 : ℝ)*x 1 + (5477353707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328553757/625000000 : ℝ)^5167 ≤ (8968711857743/20000000000000 : ℝ)^4143 := by
    have hnat : (328553757 : ℕ)^5167*20000000000000^4143 ≤ 8968711857743^4143*625000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328553757 625000000 8968711857743 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656876493/5000000000 : ℝ)^5167 ≤ (7955035763379/100000000000000 : ℝ)^4143 := by
    have hnat : (656876493 : ℕ)^5167*100000000000000^4143 ≤ 7955035763379^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656876493 5000000000 7955035763379 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477353707/10000000000 : ℝ)^5167 ≤ (23600702466829/50000000000000 : ℝ)^4143 := by
    have hnat : (5477353707 : ℕ)^5167*50000000000000^4143 ≤ 23600702466829^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477353707 10000000000 23600702466829 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328553757/625000000 : ℝ), (-656876493/5000000000 : ℝ), (5477353707/10000000000 : ℝ)] ![(8968711857743/20000000000000 : ℝ), (7955035763379/100000000000000 : ℝ), (23600702466829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328553757/625000000 : ℝ)|^5167 ≤ (8968711857743/20000000000000 : ℝ)^4143
        have hw : |(328553757/625000000 : ℝ)|=(328553757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-656876493/5000000000 : ℝ)|^5167 ≤ (7955035763379/100000000000000 : ℝ)^4143
        have hw : |(-656876493/5000000000 : ℝ)|=(656876493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477353707/10000000000 : ℝ)|^5167 ≤ (23600702466829/50000000000000 : ℝ)^4143
        have hw : |(5477353707/10000000000 : ℝ)|=(5477353707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s3_6 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256860111/10000000000 : ℝ)*x 0 + (2738676853/5000000000 : ℝ)*x 1 + (-328438247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256860111/10000000000 : ℝ)^5167 ≤ (11210889819519/25000000000000 : ℝ)^4143 := by
    have hnat : (5256860111 : ℕ)^5167*25000000000000^4143 ≤ 11210889819519^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256860111 10000000000 11210889819519 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738676853/5000000000 : ℝ)^5167 ≤ (4720140492291/10000000000000 : ℝ)^4143 := by
    have hnat : (2738676853 : ℕ)^5167*10000000000000^4143 ≤ 4720140492291^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738676853 5000000000 4720140492291 10000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328438247/2500000000 : ℝ)^5167 ≤ (7955035778483/100000000000000 : ℝ)^4143 := by
    have hnat : (328438247 : ℕ)^5167*100000000000000^4143 ≤ 7955035778483^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328438247 2500000000 7955035778483 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256860111/10000000000 : ℝ), (2738676853/5000000000 : ℝ), (-328438247/2500000000 : ℝ)] ![(11210889819519/25000000000000 : ℝ), (4720140492291/10000000000000 : ℝ), (7955035778483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256860111/10000000000 : ℝ)|^5167 ≤ (11210889819519/25000000000000 : ℝ)^4143
        have hw : |(5256860111/10000000000 : ℝ)|=(5256860111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738676853/5000000000 : ℝ)|^5167 ≤ (4720140492291/10000000000000 : ℝ)^4143
        have hw : |(2738676853/5000000000 : ℝ)|=(2738676853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-328438247/2500000000 : ℝ)|^5167 ≤ (7955035778483/100000000000000 : ℝ)^4143
        have hw : |(-328438247/2500000000 : ℝ)|=(328438247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s3_7 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4127595193/10000000000 : ℝ)*x 0 + (461649431/1000000000 : ℝ)*x 1 + (3675110271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4127595193/10000000000 : ℝ)^5167 ≤ (2072961874949/6250000000000 : ℝ)^4143 := by
    have hnat : (4127595193 : ℕ)^5167*6250000000000^4143 ≤ 2072961874949^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127595193 10000000000 2072961874949 6250000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461649431/1000000000 : ℝ)^5167 ≤ (19068320021389/50000000000000 : ℝ)^4143 := by
    have hnat : (461649431 : ℕ)^5167*50000000000000^4143 ≤ 19068320021389^4143*1000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461649431 1000000000 19068320021389 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3675110271/10000000000 : ℝ)^5167 ≤ (28695969946129/100000000000000 : ℝ)^4143 := by
    have hnat : (3675110271 : ℕ)^5167*100000000000000^4143 ≤ 28695969946129^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3675110271 10000000000 28695969946129 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4127595193/10000000000 : ℝ), (461649431/1000000000 : ℝ), (3675110271/10000000000 : ℝ)] ![(2072961874949/6250000000000 : ℝ), (19068320021389/50000000000000 : ℝ), (28695969946129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4127595193/10000000000 : ℝ)|^5167 ≤ (2072961874949/6250000000000 : ℝ)^4143
        have hw : |(4127595193/10000000000 : ℝ)|=(4127595193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(461649431/1000000000 : ℝ)|^5167 ≤ (19068320021389/50000000000000 : ℝ)^4143
        have hw : |(461649431/1000000000 : ℝ)|=(461649431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3675110271/10000000000 : ℝ)|^5167 ≤ (28695969946129/100000000000000 : ℝ)^4143
        have hw : |(3675110271/10000000000 : ℝ)|=(3675110271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1693_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (493/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8607/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8617/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8617/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8617/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8617/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8617/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8617/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9843/100000 : ℝ) ^ (5159/1024 : ℝ) ≤ (845842965560269/100000000000000000000 : ℝ) := by
    have hpowers : (9843/100000 : ℝ)^5159 ≤ (845842965560269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9843 : ℕ)^5159*100000000000000000000^1024 ≤ 845842965560269^1024*100000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9843 100000 845842965560269 100000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9843/100000 : ℝ)) (X := (845842965560269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8617/50000 : ℝ) ^ (5159/1024 : ℝ) ≤ (7109147019606777/50000000000000000000 : ℝ) := by
    have hpowers : (8617/50000 : ℝ)^5159 ≤ (7109147019606777/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8617 : ℕ)^5159*50000000000000000000^1024 ≤ 7109147019606777^1024*50000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8617 50000 7109147019606777 50000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8617/50000 : ℝ)) (X := (7109147019606777/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000845842965560269/50000000000000000000 : ℝ) ≤ (1250004197215181/1250000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (50000845842965560269/50000000000000000000 : ℝ)^1024 ≤ (1250004197215181/1250000000000000 : ℝ)^5159 := by
      have hnat : (50000845842965560269 : ℕ)^1024*1250000000000000^5159 ≤ 1250004197215181^5159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000845842965560269 50000000000000000000 1250004197215181 1250000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250004197215181/1250000000000000 : ℝ)) (X := (50000845842965560269/50000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015064137004773823/100000000000000000000 : ℝ) ≤ (10000298987112279/10000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (100015064137004773823/100000000000000000000 : ℝ)^1024 ≤ (10000298987112279/10000000000000000 : ℝ)^5159 := by
      have hnat : (100015064137004773823 : ℕ)^1024*10000000000000000^5159 ≤ 10000298987112279^5159*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015064137004773823 100000000000000000000 10000298987112279 10000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000298987112279/10000000000000000 : ℝ)) (X := (100015064137004773823/100000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007109147019606777/25000000000000000000 : ℝ) ≤ (1000056439650311/1000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (25007109147019606777/25000000000000000000 : ℝ)^1024 ≤ (1000056439650311/1000000000000000 : ℝ)^5159 := by
      have hnat : (25007109147019606777 : ℕ)^1024*1000000000000000^5159 ≤ 1000056439650311^5159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007109147019606777 25000000000000000000 1000056439650311 1000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000056439650311/1000000000000000 : ℝ)) (X := (25007109147019606777/25000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(845842965560269/100000000000000000000 : ℝ) ≤ ((36952511661835661551/36955000000000000000 : ℝ)+2*(265409390831/739100000000000 : ℝ)*(9843/100000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (36952511661835661551/36955000000000000000 : ℝ)+2*(265409390831/739100000000000 : ℝ)*(9843/100000 : ℝ)=(1250004197215181/1250000000000000 : ℝ) by norm_num, show 1+2*(845842965560269/100000000000000000000 : ℝ)=(50000845842965560269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7109147019606777/50000000000000000000 : ℝ)+(845842965560269/100000000000000000000 : ℝ) ≤ ((36952511661835661551/36955000000000000000 : ℝ)+(265409390831/739100000000000 : ℝ)*((8617/50000 : ℝ)+(9843/100000 : ℝ)))^(5159/1024 : ℝ) := by
    rw [show (36952511661835661551/36955000000000000000 : ℝ)+(265409390831/739100000000000 : ℝ)*((8617/50000 : ℝ)+(9843/100000 : ℝ))=(10000298987112279/10000000000000000 : ℝ) by norm_num, show 1+(7109147019606777/50000000000000000000 : ℝ)+(845842965560269/100000000000000000000 : ℝ)=(100015064137004773823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7109147019606777/50000000000000000000 : ℝ) ≤ ((36952511661835661551/36955000000000000000 : ℝ)+2*(265409390831/739100000000000 : ℝ)*(8617/50000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (36952511661835661551/36955000000000000000 : ℝ)+2*(265409390831/739100000000000 : ℝ)*(8617/50000 : ℝ)=(1000056439650311/1000000000000000 : ℝ) by norm_num, show 1+2*(7109147019606777/50000000000000000000 : ℝ)=(25007109147019606777/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36952511661835661551/36955000000000000000 : ℝ)*(X 1 0+X 2 0)+(265409390831/739100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9843/100000 : ℝ)) (hi := (8617/50000 : ℝ)) (c := (36952511661835661551/36955000000000000000 : ℝ)) (alpha := (265409390831/739100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36952511661835661551/36955000000000000000 : ℝ)*(X 0 1+X 2 1)+(265409390831/739100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9843/100000 : ℝ)) (hi := (8617/50000 : ℝ)) (c := (36952511661835661551/36955000000000000000 : ℝ)) (alpha := (265409390831/739100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36952511661835661551/36955000000000000000 : ℝ)*(X 0 2+X 1 2)+(265409390831/739100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9843/100000 : ℝ)) (hi := (8617/50000 : ℝ)) (c := (36952511661835661551/36955000000000000000 : ℝ)) (alpha := (265409390831/739100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1475944907/10000000000 : ℝ)*X 0 0+(21410853/39062500 : ℝ)*X 0 1+(5135815959/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349216883/10000000000 : ℝ)*X 1 0+(-827645593/5000000000 : ℝ)*X 1 1+(5135816177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069843391/2000000000 : ℝ)*X 2 0+(205432649/400000000 : ℝ)*X 2 1+(-1655291027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4127148573/10000000000 : ℝ)*X 0 0+(916112809/2500000000 : ℝ)*X 0 1+(925399403/2000000000 : ℝ)*X 0 2+(4127148573/10000000000 : ℝ)*X 1 0+(916112809/2500000000 : ℝ)*X 1 1+(925399403/2000000000 : ℝ)*X 1 2+(4127148573/10000000000 : ℝ)*X 2 0+(916112809/2500000000 : ℝ)*X 2 1+(925399403/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1476104929/10000000000 : ℝ)*X 0 0+(5139584383/10000000000 : ℝ)*X 0 1+(5477353707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328553757/625000000 : ℝ)*X 1 0+(-656876493/5000000000 : ℝ)*X 1 1+(5477353707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256860111/10000000000 : ℝ)*X 2 0+(2738676853/5000000000 : ℝ)*X 2 1+(-328438247/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4127595193/10000000000 : ℝ)*X 0 0+(461649431/1000000000 : ℝ)*X 0 1+(3675110271/10000000000 : ℝ)*X 0 2+(4127595193/10000000000 : ℝ)*X 1 0+(461649431/1000000000 : ℝ)*X 1 1+(3675110271/10000000000 : ℝ)*X 1 2+(4127595193/10000000000 : ℝ)*X 2 0+(461649431/1000000000 : ℝ)*X 2 1+(3675110271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4947715149090733501031980071/461937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29591259/3125000000000 : ℝ)*(base19) + (192444621/20000000000000 : ℝ)*(base23) + (40327417/25000000000000 : ℝ)*(upper3) + (12661987/100000000000000 : ℝ)*(upper4) + (248418159/100000000000000 : ℝ)*(upper5) + (983611608999993/50000000000000 : ℝ)*(major0) + (983611608999993/50000000000000 : ℝ)*(major1) + (983611608999993/50000000000000 : ℝ)*(major2) + (1447758789624737/50000000000000 : ℝ)*(sp0) + (1447763621760879/50000000000000 : ℝ)*(sp1) + (2895527228218941/100000000000000 : ℝ)*(sp2) + (1038914924678549/100000000000000 : ℝ)*(sp3) + (2652798143/25000000000000 : ℝ)*(sp4) + (296385307/10000000000000 : ℝ)*(sp7) + (1038917888531619/100000000000000 : ℝ)*(f.failure) + (1447764095221023/50000000000000 : ℝ)*(f.sum) + (59717618713489/36955000000000000000000000000 : ℝ)*base66 + (15704810234705519143/1847750000000000000000000000000000 : ℝ)*base67 + (1983854623187730857/1847750000000000000000000000000000 : ℝ)*base70 + (10449359069220769143/1847750000000000000000000000000000 : ℝ)*base71 + (59740315881893/18477500000000000000000000000 : ℝ)*base73 + (2744058697403269143/1847750000000000000000000000000000 : ℝ)*base75 + (4207836323138019143/1847750000000000000000000000000000 : ℝ)*base77 + (7539351289743769143/1847750000000000000000000000000000 : ℝ)*base79 + (3578990702931/9238750000000000000000000000 : ℝ)*base82 + (17137281/10000000000000000000000 : ℝ)*base89 + (17137281/10000000000000000000000 : ℝ)*base91 + (17137281/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12581017103498405149127636007/1847750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96405381/10000000000000 : ℝ)*(base19) + (519004671/50000000000000 : ℝ)*(base23) + (58125431/20000000000000 : ℝ)*(lower1) + (145380283/100000000000000 : ℝ)*(upper3) + (16753033/50000000000000 : ℝ)*(lower4) + (28365861/20000000000000 : ℝ)*(upper5) + (2011427060149219/100000000000000 : ℝ)*(major0) + (2011427060149219/100000000000000 : ℝ)*(major1) + (2011427060149219/100000000000000 : ℝ)*(major2) + (38352481/6250000000000 : ℝ)*(sp2) + (37007391777143/1250000000000 : ℝ)*(sp4) + (296059037811763/10000000000000 : ℝ)*(sp5) + (1480294845261201/50000000000000 : ℝ)*(sp6) + (1062262551165967/100000000000000 : ℝ)*(sp7) + (1062262551165967/100000000000000 : ℝ)*(f.failure) + (37007391777143/1250000000000 : ℝ)*(f.sum) + (1912591638551/2309687500000000000000000000 : ℝ)*base66 + (12137826365004571331/3695500000000000000000000000000000 : ℝ)*base68 + (9827834477406928669/3695500000000000000000000000000000 : ℝ)*base69 + (9073227959849928669/3695500000000000000000000000000000 : ℝ)*base71 + (77239996212461/36955000000000000000000000000 : ℝ)*base74 + (27308342325108071331/3695500000000000000000000000000000 : ℝ)*base76 + (24699864285711071331/3695500000000000000000000000000000 : ℝ)*base78 + (35637392209890571331/3695500000000000000000000000000000 : ℝ)*base80 + (150040866355997/18477500000000000000000000000 : ℝ)*base81 + (14781733/10000000000000000000000 : ℝ)*base89 + (14781733/10000000000000000000000 : ℝ)*base91 + (14781733/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1693_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (493/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8607/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1693_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1693_s4_0 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1475956471/10000000000 : ℝ)*x 0 + (5481134649/10000000000 : ℝ)*x 1 + (513585189/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1475956471/10000000000 : ℝ)^5167 ≤ (4599054320937/50000000000000 : ℝ)^4143 := by
    have hnat : (1475956471 : ℕ)^5167*50000000000000^4143 ≤ 4599054320937^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475956471 10000000000 4599054320937 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481134649/10000000000 : ℝ)^5167 ≤ (9448408818727/20000000000000 : ℝ)^4143 := by
    have hnat : (5481134649 : ℕ)^5167*20000000000000^4143 ≤ 9448408818727^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481134649 10000000000 9448408818727 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513585189/1000000000 : ℝ)^5167 ≤ (21779923623339/50000000000000 : ℝ)^4143 := by
    have hnat : (513585189 : ℕ)^5167*50000000000000^4143 ≤ 21779923623339^4143*1000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513585189 1000000000 21779923623339 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1475956471/10000000000 : ℝ), (5481134649/10000000000 : ℝ), (513585189/1000000000 : ℝ)] ![(4599054320937/50000000000000 : ℝ), (9448408818727/20000000000000 : ℝ), (21779923623339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1475956471/10000000000 : ℝ)|^5167 ≤ (4599054320937/50000000000000 : ℝ)^4143
        have hw : |(-1475956471/10000000000 : ℝ)|=(1475956471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5481134649/10000000000 : ℝ)|^5167 ≤ (9448408818727/20000000000000 : ℝ)^4143
        have hw : |(5481134649/10000000000 : ℝ)|=(5481134649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513585189/1000000000 : ℝ)|^5167 ≤ (21779923623339/50000000000000 : ℝ)^4143
        have hw : |(513585189/1000000000 : ℝ)|=(513585189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s4_1 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349206421/10000000000 : ℝ)*x 0 + (-10345377/62500000 : ℝ)*x 1 + (5135850077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349206421/10000000000 : ℝ)^5167 ≤ (22914073505433/50000000000000 : ℝ)^4143 := by
    have hnat : (5349206421 : ℕ)^5167*50000000000000^4143 ≤ 22914073505433^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349206421 10000000000 22914073505433 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10345377/62500000 : ℝ)^5167 ≤ (10612024908551/100000000000000 : ℝ)^4143 := by
    have hnat : (10345377 : ℕ)^5167*100000000000000^4143 ≤ 10612024908551^4143*62500000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10345377 62500000 10612024908551 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135850077/10000000000 : ℝ)^5167 ≤ (43559828069037/100000000000000 : ℝ)^4143 := by
    have hnat : (5135850077 : ℕ)^5167*100000000000000^4143 ≤ 43559828069037^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135850077 10000000000 43559828069037 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349206421/10000000000 : ℝ), (-10345377/62500000 : ℝ), (5135850077/10000000000 : ℝ)] ![(22914073505433/50000000000000 : ℝ), (10612024908551/100000000000000 : ℝ), (43559828069037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349206421/10000000000 : ℝ)|^5167 ≤ (22914073505433/50000000000000 : ℝ)^4143
        have hw : |(5349206421/10000000000 : ℝ)|=(5349206421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10345377/62500000 : ℝ)|^5167 ≤ (10612024908551/100000000000000 : ℝ)^4143
        have hw : |(-10345377/62500000 : ℝ)|=(10345377/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135850077/10000000000 : ℝ)|^5167 ≤ (43559828069037/100000000000000 : ℝ)^4143
        have hw : |(5135850077/10000000000 : ℝ)|=(5135850077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s4_2 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674602199/5000000000 : ℝ)*x 0 + (160495357/312500000 : ℝ)*x 1 + (-1655261241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674602199/5000000000 : ℝ)^5167 ≤ (45828125395513/100000000000000 : ℝ)^4143 := by
    have hnat : (2674602199 : ℕ)^5167*100000000000000^4143 ≤ 45828125395513^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674602199 5000000000 45828125395513 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160495357/312500000 : ℝ)^5167 ≤ (217799211587/500000000000 : ℝ)^4143 := by
    have hnat : (160495357 : ℕ)^5167*500000000000^4143 ≤ 217799211587^4143*312500000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160495357 312500000 217799211587 500000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1655261241/10000000000 : ℝ)^5167 ≤ (5306016136287/50000000000000 : ℝ)^4143 := by
    have hnat : (1655261241 : ℕ)^5167*50000000000000^4143 ≤ 5306016136287^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655261241 10000000000 5306016136287 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674602199/5000000000 : ℝ), (160495357/312500000 : ℝ), (-1655261241/10000000000 : ℝ)] ![(45828125395513/100000000000000 : ℝ), (217799211587/500000000000 : ℝ), (5306016136287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674602199/5000000000 : ℝ)|^5167 ≤ (45828125395513/100000000000000 : ℝ)^4143
        have hw : |(2674602199/5000000000 : ℝ)|=(2674602199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160495357/312500000 : ℝ)|^5167 ≤ (217799211587/500000000000 : ℝ)^4143
        have hw : |(160495357/312500000 : ℝ)|=(160495357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1655261241/10000000000 : ℝ)|^5167 ≤ (5306016136287/50000000000000 : ℝ)^4143
        have hw : |(-1655261241/10000000000 : ℝ)|=(1655261241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s4_3 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1031789051/2500000000 : ℝ)*x 0 + (1832280009/5000000000 : ℝ)*x 1 + (4626886907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031789051/2500000000 : ℝ)^5167 ≤ (33162990678127/100000000000000 : ℝ)^4143 := by
    have hnat : (1031789051 : ℕ)^5167*100000000000000^4143 ≤ 33162990678127^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031789051 2500000000 33162990678127 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1832280009/5000000000 : ℝ)^5167 ≤ (28593267042197/100000000000000 : ℝ)^4143 := by
    have hnat : (1832280009 : ℕ)^5167*100000000000000^4143 ≤ 28593267042197^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832280009 5000000000 28593267042197 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4626886907/10000000000 : ℝ)^5167 ≤ (38243742263657/100000000000000 : ℝ)^4143 := by
    have hnat : (4626886907 : ℕ)^5167*100000000000000^4143 ≤ 38243742263657^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4626886907 10000000000 38243742263657 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031789051/2500000000 : ℝ), (1832280009/5000000000 : ℝ), (4626886907/10000000000 : ℝ)] ![(33162990678127/100000000000000 : ℝ), (28593267042197/100000000000000 : ℝ), (38243742263657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031789051/2500000000 : ℝ)|^5167 ≤ (33162990678127/100000000000000 : ℝ)^4143
        have hw : |(1031789051/2500000000 : ℝ)|=(1031789051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1832280009/5000000000 : ℝ)|^5167 ≤ (28593267042197/100000000000000 : ℝ)^4143
        have hw : |(1832280009/5000000000 : ℝ)|=(1832280009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4626886907/10000000000 : ℝ)|^5167 ≤ (38243742263657/100000000000000 : ℝ)^4143
        have hw : |(4626886907/10000000000 : ℝ)|=(4626886907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s4_4 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1476116179/10000000000 : ℝ)*x 0 + (2569808943/5000000000 : ℝ)*x 1 + (547731259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1476116179/10000000000 : ℝ)^5167 ≤ (9199349953983/100000000000000 : ℝ)^4143 := by
    have hnat : (1476116179 : ℕ)^5167*100000000000000^4143 ≤ 9199349953983^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476116179 10000000000 9199349953983 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569808943/5000000000 : ℝ)^5167 ≤ (43599686995027/100000000000000 : ℝ)^4143 := by
    have hnat : (2569808943 : ℕ)^5167*100000000000000^4143 ≤ 43599686995027^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569808943 5000000000 43599686995027 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547731259/1000000000 : ℝ)^5167 ≤ (47200963028893/100000000000000 : ℝ)^4143 := by
    have hnat : (547731259 : ℕ)^5167*100000000000000^4143 ≤ 47200963028893^4143*1000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547731259 1000000000 47200963028893 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1476116179/10000000000 : ℝ), (2569808943/5000000000 : ℝ), (547731259/1000000000 : ℝ)] ![(9199349953983/100000000000000 : ℝ), (43599686995027/100000000000000 : ℝ), (47200963028893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1476116179/10000000000 : ℝ)|^5167 ≤ (9199349953983/100000000000000 : ℝ)^4143
        have hw : |(-1476116179/10000000000 : ℝ)|=(1476116179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569808943/5000000000 : ℝ)|^5167 ≤ (43599686995027/100000000000000 : ℝ)^4143
        have hw : |(2569808943/5000000000 : ℝ)|=(2569808943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547731259/1000000000 : ℝ)|^5167 ≤ (47200963028893/100000000000000 : ℝ)^4143
        have hw : |(547731259/1000000000 : ℝ)|=(547731259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s4_5 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051373847/2000000000 : ℝ)*x 0 + (-1313798769/10000000000 : ℝ)*x 1 + (2738656253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051373847/2000000000 : ℝ)^5167 ≤ (44843656347523/100000000000000 : ℝ)^4143 := by
    have hnat : (1051373847 : ℕ)^5167*100000000000000^4143 ≤ 44843656347523^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051373847 2000000000 44843656347523 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313798769/10000000000 : ℝ)^5167 ≤ (7955381510097/100000000000000 : ℝ)^4143 := by
    have hnat : (1313798769 : ℕ)^5167*100000000000000^4143 ≤ 7955381510097^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313798769 10000000000 7955381510097 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2738656253/5000000000 : ℝ)^5167 ≤ (9440192425221/20000000000000 : ℝ)^4143 := by
    have hnat : (2738656253 : ℕ)^5167*20000000000000^4143 ≤ 9440192425221^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738656253 5000000000 9440192425221 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051373847/2000000000 : ℝ), (-1313798769/10000000000 : ℝ), (2738656253/5000000000 : ℝ)] ![(44843656347523/100000000000000 : ℝ), (7955381510097/100000000000000 : ℝ), (9440192425221/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051373847/2000000000 : ℝ)|^5167 ≤ (44843656347523/100000000000000 : ℝ)^4143
        have hw : |(1051373847/2000000000 : ℝ)|=(1051373847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1313798769/10000000000 : ℝ)|^5167 ≤ (7955381510097/100000000000000 : ℝ)^4143
        have hw : |(-1313798769/10000000000 : ℝ)|=(1313798769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2738656253/5000000000 : ℝ)|^5167 ≤ (9440192425221/20000000000000 : ℝ)^4143
        have hw : |(2738656253/5000000000 : ℝ)|=(2738656253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s4_6 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256869429/10000000000 : ℝ)*x 0 + (684664051/1250000000 : ℝ)*x 1 + (-328449659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256869429/10000000000 : ℝ)^5167 ≤ (2802728650717/6250000000000 : ℝ)^4143 := by
    have hnat : (5256869429 : ℕ)^5167*6250000000000^4143 ≤ 2802728650717^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256869429 10000000000 2802728650717 6250000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684664051/1250000000 : ℝ)^5167 ≤ (47200961072851/100000000000000 : ℝ)^4143 := by
    have hnat : (684664051 : ℕ)^5167*100000000000000^4143 ≤ 47200961072851^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684664051 1250000000 47200961072851 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328449659/2500000000 : ℝ)^5167 ≤ (1591076101139/20000000000000 : ℝ)^4143 := by
    have hnat : (328449659 : ℕ)^5167*20000000000000^4143 ≤ 1591076101139^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328449659 2500000000 1591076101139 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256869429/10000000000 : ℝ), (684664051/1250000000 : ℝ), (-328449659/2500000000 : ℝ)] ![(2802728650717/6250000000000 : ℝ), (47200961072851/100000000000000 : ℝ), (1591076101139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256869429/10000000000 : ℝ)|^5167 ≤ (2802728650717/6250000000000 : ℝ)^4143
        have hw : |(5256869429/10000000000 : ℝ)|=(5256869429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684664051/1250000000 : ℝ)|^5167 ≤ (47200961072851/100000000000000 : ℝ)^4143
        have hw : |(684664051/1250000000 : ℝ)|=(684664051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-328449659/2500000000 : ℝ)|^5167 ≤ (1591076101139/20000000000000 : ℝ)^4143
        have hw : |(-328449659/2500000000 : ℝ)|=(328449659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_s4_7 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4127602739/10000000000 : ℝ)*x 0 + (4616389603/10000000000 : ℝ)*x 1 + (3675213283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4127602739/10000000000 : ℝ)^5167 ≤ (3316746562231/10000000000000 : ℝ)^4143 := by
    have hnat : (4127602739 : ℕ)^5167*10000000000000^4143 ≤ 3316746562231^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127602739 10000000000 3316746562231 10000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4616389603/10000000000 : ℝ)^5167 ≤ (38135561274541/100000000000000 : ℝ)^4143 := by
    have hnat : (4616389603 : ℕ)^5167*100000000000000^4143 ≤ 38135561274541^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616389603 10000000000 38135561274541 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3675213283/10000000000 : ℝ)^5167 ≤ (229575784723/800000000000 : ℝ)^4143 := by
    have hnat : (3675213283 : ℕ)^5167*800000000000^4143 ≤ 229575784723^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3675213283 10000000000 229575784723 800000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4127602739/10000000000 : ℝ), (4616389603/10000000000 : ℝ), (3675213283/10000000000 : ℝ)] ![(3316746562231/10000000000000 : ℝ), (38135561274541/100000000000000 : ℝ), (229575784723/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4127602739/10000000000 : ℝ)|^5167 ≤ (3316746562231/10000000000000 : ℝ)^4143
        have hw : |(4127602739/10000000000 : ℝ)|=(4127602739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4616389603/10000000000 : ℝ)|^5167 ≤ (38135561274541/100000000000000 : ℝ)^4143
        have hw : |(4616389603/10000000000 : ℝ)|=(4616389603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3675213283/10000000000 : ℝ)|^5167 ≤ (229575784723/800000000000 : ℝ)^4143
        have hw : |(3675213283/10000000000 : ℝ)|=(3675213283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1693_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8607/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (493/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (9861/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17213/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8607/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (493/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8607/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (493/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8607/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (493/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8607/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (493/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8607/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (493/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8607/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (493/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (493/5000 : ℝ) ^ (5159/1024 : ℝ) ≤ (426614328793767/50000000000000000000 : ℝ) := by
    have hpowers : (493/5000 : ℝ)^5159 ≤ (426614328793767/50000000000000000000 : ℝ)^1024 := by
      have hnat : (493 : ℕ)^5159*50000000000000000000^1024 ≤ 426614328793767^1024*5000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        493 5000 426614328793767 50000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (493/5000 : ℝ)) (X := (426614328793767/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8607/50000 : ℝ) ^ (5159/1024 : ℝ) ≤ (2827071749315911/20000000000000000000 : ℝ) := by
    have hpowers : (8607/50000 : ℝ)^5159 ≤ (2827071749315911/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8607 : ℕ)^5159*20000000000000000000^1024 ≤ 2827071749315911^1024*50000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8607 50000 2827071749315911 20000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8607/50000 : ℝ)) (X := (2827071749315911/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000426614328793767/25000000000000000000 : ℝ) ≤ (500001693545591/500000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (25000426614328793767/25000000000000000000 : ℝ)^1024 ≤ (500001693545591/500000000000000 : ℝ)^5159 := by
      have hnat : (25000426614328793767 : ℕ)^1024*500000000000000^5159 ≤ 500001693545591^5159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000426614328793767 25000000000000000000 500001693545591 500000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500001693545591/500000000000000 : ℝ)) (X := (25000426614328793767/25000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014988587404167089/100000000000000000000 : ℝ) ≤ (200005949754467/200000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (100014988587404167089/100000000000000000000 : ℝ)^1024 ≤ (200005949754467/200000000000000 : ℝ)^5159 := by
      have hnat : (100014988587404167089 : ℕ)^1024*200000000000000^5159 ≤ 200005949754467^5159*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014988587404167089 100000000000000000000 200005949754467 200000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200005949754467/200000000000000 : ℝ)) (X := (100014988587404167089/100000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002827071749315911/10000000000000000000 : ℝ) ≤ (62503506903343/62500000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (10002827071749315911/10000000000000000000 : ℝ)^1024 ≤ (62503506903343/62500000000000 : ℝ)^5159 := by
      have hnat : (10002827071749315911 : ℕ)^1024*62500000000000^5159 ≤ 62503506903343^5159*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002827071749315911 10000000000000000000 62503506903343 62500000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62503506903343/62500000000000 : ℝ)) (X := (10002827071749315911/10000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(426614328793767/50000000000000000000 : ℝ) ≤ ((1838376264079053817/1838500000000000000 : ℝ)+2*(26361681153/73540000000000 : ℝ)*(493/5000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (1838376264079053817/1838500000000000000 : ℝ)+2*(26361681153/73540000000000 : ℝ)*(493/5000 : ℝ)=(500001693545591/500000000000000 : ℝ) by norm_num, show 1+2*(426614328793767/50000000000000000000 : ℝ)=(25000426614328793767/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2827071749315911/20000000000000000000 : ℝ)+(426614328793767/50000000000000000000 : ℝ) ≤ ((1838376264079053817/1838500000000000000 : ℝ)+(26361681153/73540000000000 : ℝ)*((8607/50000 : ℝ)+(493/5000 : ℝ)))^(5159/1024 : ℝ) := by
    rw [show (1838376264079053817/1838500000000000000 : ℝ)+(26361681153/73540000000000 : ℝ)*((8607/50000 : ℝ)+(493/5000 : ℝ))=(200005949754467/200000000000000 : ℝ) by norm_num, show 1+(2827071749315911/20000000000000000000 : ℝ)+(426614328793767/50000000000000000000 : ℝ)=(100014988587404167089/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2827071749315911/20000000000000000000 : ℝ) ≤ ((1838376264079053817/1838500000000000000 : ℝ)+2*(26361681153/73540000000000 : ℝ)*(8607/50000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (1838376264079053817/1838500000000000000 : ℝ)+2*(26361681153/73540000000000 : ℝ)*(8607/50000 : ℝ)=(62503506903343/62500000000000 : ℝ) by norm_num, show 1+2*(2827071749315911/20000000000000000000 : ℝ)=(10002827071749315911/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1838376264079053817/1838500000000000000 : ℝ)*(X 1 0+X 2 0)+(26361681153/73540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (493/5000 : ℝ)) (hi := (8607/50000 : ℝ)) (c := (1838376264079053817/1838500000000000000 : ℝ)) (alpha := (26361681153/73540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1838376264079053817/1838500000000000000 : ℝ)*(X 0 1+X 2 1)+(26361681153/73540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (493/5000 : ℝ)) (hi := (8607/50000 : ℝ)) (c := (1838376264079053817/1838500000000000000 : ℝ)) (alpha := (26361681153/73540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1838376264079053817/1838500000000000000 : ℝ)*(X 0 2+X 1 2)+(26361681153/73540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (493/5000 : ℝ)) (hi := (8607/50000 : ℝ)) (c := (1838376264079053817/1838500000000000000 : ℝ)) (alpha := (26361681153/73540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1475956471/10000000000 : ℝ)*X 0 0+(5481134649/10000000000 : ℝ)*X 0 1+(513585189/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349206421/10000000000 : ℝ)*X 1 0+(-10345377/62500000 : ℝ)*X 1 1+(5135850077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674602199/5000000000 : ℝ)*X 2 0+(160495357/312500000 : ℝ)*X 2 1+(-1655261241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1031789051/2500000000 : ℝ)*X 0 0+(1832280009/5000000000 : ℝ)*X 0 1+(4626886907/10000000000 : ℝ)*X 0 2+(1031789051/2500000000 : ℝ)*X 1 0+(1832280009/5000000000 : ℝ)*X 1 1+(4626886907/10000000000 : ℝ)*X 1 2+(1031789051/2500000000 : ℝ)*X 2 0+(1832280009/5000000000 : ℝ)*X 2 1+(4626886907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1476116179/10000000000 : ℝ)*X 0 0+(2569808943/5000000000 : ℝ)*X 0 1+(547731259/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051373847/2000000000 : ℝ)*X 1 0+(-1313798769/10000000000 : ℝ)*X 1 1+(2738656253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256869429/10000000000 : ℝ)*X 2 0+(684664051/1250000000 : ℝ)*X 2 1+(-328449659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4127602739/10000000000 : ℝ)*X 0 0+(4616389603/10000000000 : ℝ)*X 0 1+(3675213283/10000000000 : ℝ)*X 0 2+(4127602739/10000000000 : ℝ)*X 1 0+(4616389603/10000000000 : ℝ)*X 1 1+(3675213283/10000000000 : ℝ)*X 1 2+(4127602739/10000000000 : ℝ)*X 2 0+(4616389603/10000000000 : ℝ)*X 2 1+(3675213283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (165075895100784942667032273/22981250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1347902097/100000000000000 : ℝ)*(base19) + (285442169/100000000000000 : ℝ)*(base23) + (51782303/50000000000000 : ℝ)*(upper2) + (32640549/25000000000000 : ℝ)*(upper3) + (94845517/50000000000000 : ℝ)*(upper5) + (983833285261077/50000000000000 : ℝ)*(major0) + (983833285261077/50000000000000 : ℝ)*(major1) + (983833285261077/50000000000000 : ℝ)*(major2) + (2896180872455913/100000000000000 : ℝ)*(sp0) + (362022440569227/12500000000000 : ℝ)*(sp1) + (1448085636602777/50000000000000 : ℝ)*(sp2) + (1039150924656933/100000000000000 : ℝ)*(sp3) + (931380819/10000000000000 : ℝ)*(sp6) + (1104495837/100000000000000 : ℝ)*(sp7) + (103915202915277/10000000000000 : ℝ)*(f.failure) + (2896180872455913/100000000000000 : ℝ)*(f.sum) + (3400485880621/1838500000000000000000000000 : ℝ)*base66 + (111145706437055909/91925000000000000000000000000000 : ℝ)*base67 + (231393936049305909/91925000000000000000000000000000 : ℝ)*base69 + (451562792141730909/91925000000000000000000000000000 : ℝ)*base71 + (3231375214083/3677000000000000000000000000 : ℝ)*base74 + (270782119814955909/91925000000000000000000000000000 : ℝ)*base75 + (549353144920319091/91925000000000000000000000000000 : ℝ)*base78 + (303691730634980909/91925000000000000000000000000000 : ℝ)*base79 + (1357513702083/1838500000000000000000000000 : ℝ)*base81 + (5606577/1000000000000000000000 : ℝ)*base90 + (5606577/1000000000000000000000 : ℝ)*base92 + (5606577/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (975203477974049536161309/179541015625000000000000000000 : ℝ) := by norm_num
    linear_combination (30870347/4000000000000 : ℝ)*(base19) + (123488391/12500000000000 : ℝ)*(base23) + (91695071/50000000000000 : ℝ)*(lower1) + (140777699/100000000000000 : ℝ)*(upper3) + (35408853/100000000000000 : ℝ)*(lower4) + (23182343/20000000000000 : ℝ)*(upper5) + (502968406974549/25000000000000 : ℝ)*(major0) + (502968406974549/25000000000000 : ℝ)*(major1) + (502968406974549/25000000000000 : ℝ)*(major2) + (1124674553/50000000000000 : ℝ)*(sp2) + (59224973698969/2000000000000 : ℝ)*(sp4) + (118449916527591/4000000000000 : ℝ)*(sp5) + (370155680961527/12500000000000 : ℝ)*(sp6) + (1062498389793027/100000000000000 : ℝ)*(sp7) + (1062498389793027/100000000000000 : ℝ)*(f.failure) + (59224973698969/2000000000000 : ℝ)*(f.sum) + (2150314362157/3677000000000000000000000000 : ℝ)*base65 + (229664111581016033/45962500000000000000000000000000 : ℝ)*base67 + (78903059527016033/45962500000000000000000000000000 : ℝ)*base69 + (500829160297653533/45962500000000000000000000000000 : ℝ)*base71 + (3200494613913/1838500000000000000000000000 : ℝ)*base73 + (301337378848608967/45962500000000000000000000000000 : ℝ)*base76 + (21432897882916033/45962500000000000000000000000000 : ℝ)*base77 + (405375698457966033/45962500000000000000000000000000 : ℝ)*base79 + (211152463471/147080000000000000000000000 : ℝ)*base82 + (31040673/10000000000000000000000 : ℝ)*base89 + (31040673/10000000000000000000000 : ℝ)*base91 + (31040673/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1693_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8607/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (493/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17213/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1693_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1693_box_0 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-228713193/2000000000 : ℝ)*x 0 + (271320207/500000000 : ℝ)*x 1 + (5426403353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228713193/2000000000 : ℝ)^5167 ≤ (1672774537911/25000000000000 : ℝ)^4143 := by
    have hnat : (228713193 : ℕ)^5167*25000000000000^4143 ≤ 1672774537911^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228713193 2000000000 1672774537911 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271320207/500000000 : ℝ)^5167 ≤ (46654455136073/100000000000000 : ℝ)^4143 := by
    have hnat : (271320207 : ℕ)^5167*100000000000000^4143 ≤ 46654455136073^4143*500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271320207 500000000 46654455136073 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426403353/10000000000 : ℝ)^5167 ≤ (46654446697301/100000000000000 : ℝ)^4143 := by
    have hnat : (5426403353 : ℕ)^5167*100000000000000^4143 ≤ 46654446697301^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426403353 10000000000 46654446697301 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228713193/2000000000 : ℝ), (271320207/500000000 : ℝ), (5426403353/10000000000 : ℝ)] ![(1672774537911/25000000000000 : ℝ), (46654455136073/100000000000000 : ℝ), (46654446697301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228713193/2000000000 : ℝ)|^5167 ≤ (1672774537911/25000000000000 : ℝ)^4143
        have hw : |(-228713193/2000000000 : ℝ)|=(228713193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271320207/500000000 : ℝ)|^5167 ≤ (46654455136073/100000000000000 : ℝ)^4143
        have hw : |(271320207/500000000 : ℝ)|=(271320207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426403353/10000000000 : ℝ)|^5167 ≤ (46654446697301/100000000000000 : ℝ)^4143
        have hw : |(5426403353/10000000000 : ℝ)|=(5426403353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_1 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612995033/5000000000 : ℝ)*x 0 + (-35710643/250000000 : ℝ)*x 1 + (678300541/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612995033/5000000000 : ℝ)^5167 ≤ (44515374304811/100000000000000 : ℝ)^4143 := by
    have hnat : (2612995033 : ℕ)^5167*100000000000000^4143 ≤ 44515374304811^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612995033 5000000000 44515374304811 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35710643/250000000 : ℝ)^5167 ≤ (4415084266899/50000000000000 : ℝ)^4143 := by
    have hnat : (35710643 : ℕ)^5167*50000000000000^4143 ≤ 4415084266899^4143*250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35710643 250000000 4415084266899 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678300541/1250000000 : ℝ)^5167 ≤ (23327228575971/50000000000000 : ℝ)^4143 := by
    have hnat : (678300541 : ℕ)^5167*50000000000000^4143 ≤ 23327228575971^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678300541 1250000000 23327228575971 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612995033/5000000000 : ℝ), (-35710643/250000000 : ℝ), (678300541/1250000000 : ℝ)] ![(44515374304811/100000000000000 : ℝ), (4415084266899/50000000000000 : ℝ), (23327228575971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612995033/5000000000 : ℝ)|^5167 ≤ (44515374304811/100000000000000 : ℝ)^4143
        have hw : |(2612995033/5000000000 : ℝ)|=(2612995033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35710643/250000000 : ℝ)|^5167 ≤ (4415084266899/50000000000000 : ℝ)^4143
        have hw : |(-35710643/250000000 : ℝ)|=(35710643/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678300541/1250000000 : ℝ)|^5167 ≤ (23327228575971/50000000000000 : ℝ)^4143
        have hw : |(678300541/1250000000 : ℝ)|=(678300541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_2 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225990969/10000000000 : ℝ)*x 0 + (678300433/1250000000 : ℝ)*x 1 + (-357106419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225990969/10000000000 : ℝ)^5167 ≤ (22257691948887/50000000000000 : ℝ)^4143 := by
    have hnat : (5225990969 : ℕ)^5167*50000000000000^4143 ≤ 22257691948887^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225990969 10000000000 22257691948887 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678300433/1250000000 : ℝ)^5167 ≤ (23327223943761/50000000000000 : ℝ)^4143 := by
    have hnat : (678300433 : ℕ)^5167*50000000000000^4143 ≤ 23327223943761^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678300433 1250000000 23327223943761 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357106419/2500000000 : ℝ)^5167 ≤ (8830168194573/100000000000000 : ℝ)^4143 := by
    have hnat : (357106419 : ℕ)^5167*100000000000000^4143 ≤ 8830168194573^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357106419 2500000000 8830168194573 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225990969/10000000000 : ℝ), (678300433/1250000000 : ℝ), (-357106419/2500000000 : ℝ)] ![(22257691948887/50000000000000 : ℝ), (23327223943761/50000000000000 : ℝ), (8830168194573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225990969/10000000000 : ℝ)|^5167 ≤ (22257691948887/50000000000000 : ℝ)^4143
        have hw : |(5225990969/10000000000 : ℝ)|=(5225990969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678300433/1250000000 : ℝ)|^5167 ≤ (23327223943761/50000000000000 : ℝ)^4143
        have hw : |(678300433/1250000000 : ℝ)|=(678300433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-357106419/2500000000 : ℝ)|^5167 ≤ (8830168194573/100000000000000 : ℝ)^4143
        have hw : |(-357106419/2500000000 : ℝ)|=(357106419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_3 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (902210373/2000000000 : ℝ)*x 0 + (3957679529/10000000000 : ℝ)*x 1 + (197883951/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (902210373/2000000000 : ℝ)^5167 ≤ (37053375810813/100000000000000 : ℝ)^4143 := by
    have hnat : (902210373 : ℕ)^5167*100000000000000^4143 ≤ 37053375810813^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902210373 2000000000 37053375810813 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3957679529/10000000000 : ℝ)^5167 ≤ (31473314606609/100000000000000 : ℝ)^4143 := by
    have hnat : (3957679529 : ℕ)^5167*100000000000000^4143 ≤ 31473314606609^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3957679529 10000000000 31473314606609 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197883951/500000000 : ℝ)^5167 ≤ (7868327389583/25000000000000 : ℝ)^4143 := by
    have hnat : (197883951 : ℕ)^5167*25000000000000^4143 ≤ 7868327389583^4143*500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197883951 500000000 7868327389583 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(902210373/2000000000 : ℝ), (3957679529/10000000000 : ℝ), (197883951/500000000 : ℝ)] ![(37053375810813/100000000000000 : ℝ), (31473314606609/100000000000000 : ℝ), (7868327389583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(902210373/2000000000 : ℝ)|^5167 ≤ (37053375810813/100000000000000 : ℝ)^4143
        have hw : |(902210373/2000000000 : ℝ)|=(902210373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3957679529/10000000000 : ℝ)|^5167 ≤ (31473314606609/100000000000000 : ℝ)^4143
        have hw : |(3957679529/10000000000 : ℝ)|=(3957679529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197883951/500000000 : ℝ)|^5167 ≤ (7868327389583/25000000000000 : ℝ)^4143
        have hw : |(197883951/500000000 : ℝ)|=(197883951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_4 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-914626549/5000000000 : ℝ)*x 0 + (5176438413/10000000000 : ℝ)*x 1 + (5176438461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914626549/5000000000 : ℝ)^5167 ≤ (601041590879/5000000000000 : ℝ)^4143 := by
    have hnat : (914626549 : ℕ)^5167*5000000000000^4143 ≤ 601041590879^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914626549 5000000000 601041590879 5000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176438413/10000000000 : ℝ)^5167 ≤ (10997395957853/25000000000000 : ℝ)^4143 := by
    have hnat : (5176438413 : ℕ)^5167*25000000000000^4143 ≤ 10997395957853^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176438413 10000000000 10997395957853 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176438461/10000000000 : ℝ)^5167 ≤ (21994792170069/50000000000000 : ℝ)^4143 := by
    have hnat : (5176438461 : ℕ)^5167*50000000000000^4143 ≤ 21994792170069^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176438461 10000000000 21994792170069 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914626549/5000000000 : ℝ), (5176438413/10000000000 : ℝ), (5176438461/10000000000 : ℝ)] ![(601041590879/5000000000000 : ℝ), (10997395957853/25000000000000 : ℝ), (21994792170069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914626549/5000000000 : ℝ)|^5167 ≤ (601041590879/5000000000000 : ℝ)^4143
        have hw : |(-914626549/5000000000 : ℝ)|=(914626549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176438413/10000000000 : ℝ)|^5167 ≤ (10997395957853/25000000000000 : ℝ)^4143
        have hw : |(5176438413/10000000000 : ℝ)|=(5176438413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176438461/10000000000 : ℝ)|^5167 ≤ (21994792170069/50000000000000 : ℝ)^4143
        have hw : |(5176438461/10000000000 : ℝ)|=(5176438461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_5 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396216519/10000000000 : ℝ)*x 0 + (-768784911/5000000000 : ℝ)*x 1 + (517643853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396216519/10000000000 : ℝ)^5167 ≤ (46330984914607/100000000000000 : ℝ)^4143 := by
    have hnat : (5396216519 : ℕ)^5167*100000000000000^4143 ≤ 46330984914607^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396216519 10000000000 46330984914607 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (768784911/5000000000 : ℝ)^5167 ≤ (604964374663/6250000000000 : ℝ)^4143 := by
    have hnat : (768784911 : ℕ)^5167*6250000000000^4143 ≤ 604964374663^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768784911 5000000000 604964374663 6250000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517643853/1000000000 : ℝ)^5167 ≤ (43989585071431/100000000000000 : ℝ)^4143 := by
    have hnat : (517643853 : ℕ)^5167*100000000000000^4143 ≤ 43989585071431^4143*1000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517643853 1000000000 43989585071431 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396216519/10000000000 : ℝ), (-768784911/5000000000 : ℝ), (517643853/1000000000 : ℝ)] ![(46330984914607/100000000000000 : ℝ), (604964374663/6250000000000 : ℝ), (43989585071431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396216519/10000000000 : ℝ)|^5167 ≤ (46330984914607/100000000000000 : ℝ)^4143
        have hw : |(5396216519/10000000000 : ℝ)|=(5396216519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-768784911/5000000000 : ℝ)|^5167 ≤ (604964374663/6250000000000 : ℝ)^4143
        have hw : |(-768784911/5000000000 : ℝ)|=(768784911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517643853/1000000000 : ℝ)|^5167 ≤ (43989585071431/100000000000000 : ℝ)^4143
        have hw : |(517643853/1000000000 : ℝ)|=(517643853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_6 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396216461/10000000000 : ℝ)*x 0 + (1035287727/2000000000 : ℝ)*x 1 + (-1537569761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396216461/10000000000 : ℝ)^5167 ≤ (23165492146773/50000000000000 : ℝ)^4143 := by
    have hnat : (5396216461 : ℕ)^5167*50000000000000^4143 ≤ 23165492146773^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396216461 10000000000 23165492146773 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035287727/2000000000 : ℝ)^5167 ≤ (10997396546067/25000000000000 : ℝ)^4143 := by
    have hnat : (1035287727 : ℕ)^5167*25000000000000^4143 ≤ 10997396546067^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035287727 2000000000 10997396546067 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1537569761/10000000000 : ℝ)^5167 ≤ (4839714757841/50000000000000 : ℝ)^4143 := by
    have hnat : (1537569761 : ℕ)^5167*50000000000000^4143 ≤ 4839714757841^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537569761 10000000000 4839714757841 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396216461/10000000000 : ℝ), (1035287727/2000000000 : ℝ), (-1537569761/10000000000 : ℝ)] ![(23165492146773/50000000000000 : ℝ), (10997396546067/25000000000000 : ℝ), (4839714757841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396216461/10000000000 : ℝ)|^5167 ≤ (23165492146773/50000000000000 : ℝ)^4143
        have hw : |(5396216461/10000000000 : ℝ)|=(5396216461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035287727/2000000000 : ℝ)|^5167 ≤ (10997396546067/25000000000000 : ℝ)^4143
        have hw : |(1035287727/2000000000 : ℝ)|=(1035287727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1537569761/10000000000 : ℝ)|^5167 ≤ (4839714757841/50000000000000 : ℝ)^4143
        have hw : |(-1537569761/10000000000 : ℝ)|=(1537569761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_7 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (932130541/2500000000 : ℝ)*x 0 + (4348088559/10000000000 : ℝ)*x 1 + (543511027/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932130541/2500000000 : ℝ)^5167 ≤ (14608515452031/50000000000000 : ℝ)^4143 := by
    have hnat : (932130541 : ℕ)^5167*50000000000000^4143 ≤ 14608515452031^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932130541 2500000000 14608515452031 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4348088559/10000000000 : ℝ)^5167 ≤ (35391486281427/100000000000000 : ℝ)^4143 := by
    have hnat : (4348088559 : ℕ)^5167*100000000000000^4143 ≤ 35391486281427^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348088559 10000000000 35391486281427 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543511027/1250000000 : ℝ)^5167 ≤ (35391482799513/100000000000000 : ℝ)^4143 := by
    have hnat : (543511027 : ℕ)^5167*100000000000000^4143 ≤ 35391482799513^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543511027 1250000000 35391482799513 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(932130541/2500000000 : ℝ), (4348088559/10000000000 : ℝ), (543511027/1250000000 : ℝ)] ![(14608515452031/50000000000000 : ℝ), (35391486281427/100000000000000 : ℝ), (35391482799513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(932130541/2500000000 : ℝ)|^5167 ≤ (14608515452031/50000000000000 : ℝ)^4143
        have hw : |(932130541/2500000000 : ℝ)|=(932130541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4348088559/10000000000 : ℝ)|^5167 ≤ (35391486281427/100000000000000 : ℝ)^4143
        have hw : |(4348088559/10000000000 : ℝ)|=(4348088559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543511027/1250000000 : ℝ)|^5167 ≤ (35391482799513/100000000000000 : ℝ)^4143
        have hw : |(543511027/1250000000 : ℝ)|=(543511027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_8 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-841033131/5000000000 : ℝ)*x 0 + (124821187/250000000 : ℝ)*x 1 + (1367463279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841033131/5000000000 : ℝ)^5167 ≤ (10826783901129/100000000000000 : ℝ)^4143 := by
    have hnat : (841033131 : ℕ)^5167*100000000000000^4143 ≤ 10826783901129^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841033131 5000000000 10826783901129 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124821187/250000000 : ℝ)^5167 ≤ (21026205075699/50000000000000 : ℝ)^4143 := by
    have hnat : (124821187 : ℕ)^5167*50000000000000^4143 ≤ 21026205075699^4143*250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124821187 250000000 21026205075699 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367463279/2500000000 : ℝ)^5167 ≤ (23560402969599/50000000000000 : ℝ)^4143 := by
    have hnat : (1367463279 : ℕ)^5167*50000000000000^4143 ≤ 23560402969599^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367463279 2500000000 23560402969599 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-841033131/5000000000 : ℝ), (124821187/250000000 : ℝ), (1367463279/2500000000 : ℝ)] ![(10826783901129/100000000000000 : ℝ), (21026205075699/50000000000000 : ℝ), (23560402969599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-841033131/5000000000 : ℝ)|^5167 ≤ (10826783901129/100000000000000 : ℝ)^4143
        have hw : |(-841033131/5000000000 : ℝ)|=(841033131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124821187/250000000 : ℝ)|^5167 ≤ (21026205075699/50000000000000 : ℝ)^4143
        have hw : |(124821187/250000000 : ℝ)|=(124821187/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367463279/2500000000 : ℝ)|^5167 ≤ (23560402969599/50000000000000 : ℝ)^4143
        have hw : |(1367463279/2500000000 : ℝ)|=(1367463279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_9 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039282889/2000000000 : ℝ)*x 0 + (-1408627371/10000000000 : ℝ)*x 1 + (1367463323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039282889/2000000000 : ℝ)^5167 ≤ (44201399666157/100000000000000 : ℝ)^4143 := by
    have hnat : (1039282889 : ℕ)^5167*100000000000000^4143 ≤ 44201399666157^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039282889 2000000000 44201399666157 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1408627371/10000000000 : ℝ)^5167 ≤ (8677792489073/100000000000000 : ℝ)^4143 := by
    have hnat : (1408627371 : ℕ)^5167*100000000000000^4143 ≤ 8677792489073^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408627371 10000000000 8677792489073 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367463323/2500000000 : ℝ)^5167 ≤ (23560403915059/50000000000000 : ℝ)^4143 := by
    have hnat : (1367463323 : ℕ)^5167*50000000000000^4143 ≤ 23560403915059^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367463323 2500000000 23560403915059 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039282889/2000000000 : ℝ), (-1408627371/10000000000 : ℝ), (1367463323/2500000000 : ℝ)] ![(44201399666157/100000000000000 : ℝ), (8677792489073/100000000000000 : ℝ), (23560403915059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039282889/2000000000 : ℝ)|^5167 ≤ (44201399666157/100000000000000 : ℝ)^4143
        have hw : |(1039282889/2000000000 : ℝ)|=(1039282889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1408627371/10000000000 : ℝ)|^5167 ≤ (8677792489073/100000000000000 : ℝ)^4143
        have hw : |(-1408627371/10000000000 : ℝ)|=(1408627371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367463323/2500000000 : ℝ)|^5167 ≤ (23560403915059/50000000000000 : ℝ)^4143
        have hw : |(1367463323/2500000000 : ℝ)|=(1367463323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_10 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196413147/10000000000 : ℝ)*x 0 + (5469854407/10000000000 : ℝ)*x 1 + (-281725521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196413147/10000000000 : ℝ)^5167 ≤ (11050346474067/25000000000000 : ℝ)^4143 := by
    have hnat : (5196413147 : ℕ)^5167*25000000000000^4143 ≤ 11050346474067^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196413147 10000000000 11050346474067 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469854407/10000000000 : ℝ)^5167 ≤ (47120819809529/100000000000000 : ℝ)^4143 := by
    have hnat : (5469854407 : ℕ)^5167*100000000000000^4143 ≤ 47120819809529^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469854407 10000000000 47120819809529 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281725521/2000000000 : ℝ)^5167 ≤ (8677794286919/100000000000000 : ℝ)^4143 := by
    have hnat : (281725521 : ℕ)^5167*100000000000000^4143 ≤ 8677794286919^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281725521 2000000000 8677794286919 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196413147/10000000000 : ℝ), (5469854407/10000000000 : ℝ), (-281725521/2000000000 : ℝ)] ![(11050346474067/25000000000000 : ℝ), (47120819809529/100000000000000 : ℝ), (8677794286919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196413147/10000000000 : ℝ)|^5167 ≤ (11050346474067/25000000000000 : ℝ)^4143
        have hw : |(5196413147/10000000000 : ℝ)|=(5196413147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469854407/10000000000 : ℝ)|^5167 ≤ (47120819809529/100000000000000 : ℝ)^4143
        have hw : |(5469854407/10000000000 : ℝ)|=(5469854407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281725521/2000000000 : ℝ)|^5167 ≤ (8677794286919/100000000000000 : ℝ)^4143
        have hw : |(-281725521/2000000000 : ℝ)|=(281725521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_11 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4642049077/10000000000 : ℝ)*x 0 + (194482073/500000000 : ℝ)*x 1 + (3889640807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4642049077/10000000000 : ℝ)^5167 ≤ (38400104576759/100000000000000 : ℝ)^4143 := by
    have hnat : (4642049077 : ℕ)^5167*100000000000000^4143 ≤ 38400104576759^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4642049077 10000000000 38400104576759 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194482073/500000000 : ℝ)^5167 ≤ (3849993866143/12500000000000 : ℝ)^4143 := by
    have hnat : (194482073 : ℕ)^5167*12500000000000^4143 ≤ 3849993866143^4143*500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194482073 500000000 3849993866143 12500000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3889640807/10000000000 : ℝ)^5167 ≤ (3079994448037/10000000000000 : ℝ)^4143 := by
    have hnat : (3889640807 : ℕ)^5167*10000000000000^4143 ≤ 3079994448037^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3889640807 10000000000 3079994448037 10000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4642049077/10000000000 : ℝ), (194482073/500000000 : ℝ), (3889640807/10000000000 : ℝ)] ![(38400104576759/100000000000000 : ℝ), (3849993866143/12500000000000 : ℝ), (3079994448037/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4642049077/10000000000 : ℝ)|^5167 ≤ (38400104576759/100000000000000 : ℝ)^4143
        have hw : |(4642049077/10000000000 : ℝ)|=(4642049077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194482073/500000000 : ℝ)|^5167 ≤ (3849993866143/12500000000000 : ℝ)^4143
        have hw : |(194482073/500000000 : ℝ)|=(194482073/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3889640807/10000000000 : ℝ)|^5167 ≤ (3079994448037/10000000000000 : ℝ)^4143
        have hw : |(3889640807/10000000000 : ℝ)|=(3889640807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_12 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-257167113/2000000000 : ℝ)*x 0 + (1400237353/2500000000 : ℝ)*x 1 + (2575578463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257167113/2000000000 : ℝ)^5167 ≤ (3872382455799/50000000000000 : ℝ)^4143 := by
    have hnat : (257167113 : ℕ)^5167*50000000000000^4143 ≤ 3872382455799^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257167113 2000000000 3872382455799 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400237353/2500000000 : ℝ)^5167 ≤ (48533433890133/100000000000000 : ℝ)^4143 := by
    have hnat : (1400237353 : ℕ)^5167*100000000000000^4143 ≤ 48533433890133^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400237353 2500000000 48533433890133 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575578463/5000000000 : ℝ)^5167 ≤ (43721801192529/100000000000000 : ℝ)^4143 := by
    have hnat : (2575578463 : ℕ)^5167*100000000000000^4143 ≤ 43721801192529^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575578463 5000000000 43721801192529 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257167113/2000000000 : ℝ), (1400237353/2500000000 : ℝ), (2575578463/5000000000 : ℝ)] ![(3872382455799/50000000000000 : ℝ), (48533433890133/100000000000000 : ℝ), (43721801192529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257167113/2000000000 : ℝ)|^5167 ≤ (3872382455799/50000000000000 : ℝ)^4143
        have hw : |(-257167113/2000000000 : ℝ)|=(257167113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400237353/2500000000 : ℝ)|^5167 ≤ (48533433890133/100000000000000 : ℝ)^4143
        have hw : |(1400237353/2500000000 : ℝ)|=(1400237353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575578463/5000000000 : ℝ)|^5167 ≤ (43721801192529/100000000000000 : ℝ)^4143
        have hw : |(2575578463/5000000000 : ℝ)|=(2575578463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_13 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5413460401/10000000000 : ℝ)*x 0 + (-309627961/2000000000 : ℝ)*x 1 + (2575578783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413460401/10000000000 : ℝ)^5167 ≤ (46515704129149/100000000000000 : ℝ)^4143 := by
    have hnat : (5413460401 : ℕ)^5167*100000000000000^4143 ≤ 46515704129149^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413460401 10000000000 46515704129149 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309627961/2000000000 : ℝ)^5167 ≤ (2440621972517/25000000000000 : ℝ)^4143 := by
    have hnat : (309627961 : ℕ)^5167*25000000000000^4143 ≤ 2440621972517^4143*2000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309627961 2000000000 2440621972517 25000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575578783/5000000000 : ℝ)^5167 ≤ (21860903983667/50000000000000 : ℝ)^4143 := by
    have hnat : (2575578783 : ℕ)^5167*50000000000000^4143 ≤ 21860903983667^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575578783 5000000000 21860903983667 50000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413460401/10000000000 : ℝ), (-309627961/2000000000 : ℝ), (2575578783/5000000000 : ℝ)] ![(46515704129149/100000000000000 : ℝ), (2440621972517/25000000000000 : ℝ), (21860903983667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413460401/10000000000 : ℝ)|^5167 ≤ (46515704129149/100000000000000 : ℝ)^4143
        have hw : |(5413460401/10000000000 : ℝ)|=(5413460401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-309627961/2000000000 : ℝ)|^5167 ≤ (2440621972517/25000000000000 : ℝ)^4143
        have hw : |(-309627961/2000000000 : ℝ)|=(309627961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575578783/5000000000 : ℝ)|^5167 ≤ (21860903983667/50000000000000 : ℝ)^4143
        have hw : |(2575578783/5000000000 : ℝ)|=(2575578783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_14 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2706730743/5000000000 : ℝ)*x 0 + (515115571/1000000000 : ℝ)*x 1 + (-193517603/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706730743/5000000000 : ℝ)^5167 ≤ (46515715756423/100000000000000 : ℝ)^4143 := by
    have hnat : (2706730743 : ℕ)^5167*100000000000000^4143 ≤ 46515715756423^4143*5000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706730743 5000000000 46515715756423 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515115571/1000000000 : ℝ)^5167 ≤ (43721788320401/100000000000000 : ℝ)^4143 := by
    have hnat : (515115571 : ℕ)^5167*100000000000000^4143 ≤ 43721788320401^4143*1000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515115571 1000000000 43721788320401 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193517603/1250000000 : ℝ)^5167 ≤ (1952499180809/20000000000000 : ℝ)^4143 := by
    have hnat : (193517603 : ℕ)^5167*20000000000000^4143 ≤ 1952499180809^4143*1250000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193517603 1250000000 1952499180809 20000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706730743/5000000000 : ℝ), (515115571/1000000000 : ℝ), (-193517603/1250000000 : ℝ)] ![(46515715756423/100000000000000 : ℝ), (43721788320401/100000000000000 : ℝ), (1952499180809/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706730743/5000000000 : ℝ)|^5167 ≤ (46515715756423/100000000000000 : ℝ)^4143
        have hw : |(2706730743/5000000000 : ℝ)|=(2706730743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515115571/1000000000 : ℝ)|^5167 ≤ (43721788320401/100000000000000 : ℝ)^4143
        have hw : |(515115571/1000000000 : ℝ)|=(515115571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193517603/1250000000 : ℝ)|^5167 ≤ (1952499180809/20000000000000 : ℝ)^4143
        have hw : |(-193517603/1250000000 : ℝ)|=(193517603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1693_box_15 (p : ℝ) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (911598337/2500000000 : ℝ)*x 0 + (4387470647/10000000000 : ℝ)*x 1 + (1096867149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (911598337/2500000000 : ℝ)^5167 ≤ (1420829618071/5000000000000 : ℝ)^4143 := by
    have hnat : (911598337 : ℕ)^5167*5000000000000^4143 ≤ 1420829618071^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911598337 2500000000 1420829618071 5000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387470647/10000000000 : ℝ)^5167 ≤ (3579171424729/10000000000000 : ℝ)^4143 := by
    have hnat : (4387470647 : ℕ)^5167*10000000000000^4143 ≤ 3579171424729^4143*10000000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387470647 10000000000 3579171424729 10000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096867149/2500000000 : ℝ)^5167 ≤ (35791693380413/100000000000000 : ℝ)^4143 := by
    have hnat : (1096867149 : ℕ)^5167*100000000000000^4143 ≤ 35791693380413^4143*2500000000^5167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096867149 2500000000 35791693380413 100000000000000 5167 4143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5167/1024 : ℝ)) 5167 4143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(911598337/2500000000 : ℝ), (4387470647/10000000000 : ℝ), (1096867149/2500000000 : ℝ)] ![(1420829618071/5000000000000 : ℝ), (3579171424729/10000000000000 : ℝ), (35791693380413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(911598337/2500000000 : ℝ)|^5167 ≤ (1420829618071/5000000000000 : ℝ)^4143
        have hw : |(911598337/2500000000 : ℝ)|=(911598337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4387470647/10000000000 : ℝ)|^5167 ≤ (3579171424729/10000000000000 : ℝ)^4143
        have hw : |(4387470647/10000000000 : ℝ)|=(4387470647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096867149/2500000000 : ℝ)|^5167 ≤ (35791693380413/100000000000000 : ℝ)^4143
        have hw : |(1096867149/2500000000 : ℝ)|=(1096867149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1693_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17213/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66597/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58001/100000 : ℝ) ∧ (8091/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2818/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17213/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17213/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17213/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17213/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17213/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17213/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9861/100000 : ℝ) ^ (5159/1024 : ℝ) ≤ (853664714345013/100000000000000000000 : ℝ) := by
    have hpowers : (9861/100000 : ℝ)^5159 ≤ (853664714345013/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9861 : ℕ)^5159*100000000000000000000^1024 ≤ 853664714345013^1024*100000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9861 100000 853664714345013 100000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9861/100000 : ℝ)) (X := (853664714345013/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17213/100000 : ℝ) ^ (5159/1024 : ℝ) ≤ (7065611091666231/50000000000000000000 : ℝ) := by
    have hpowers : (17213/100000 : ℝ)^5159 ≤ (7065611091666231/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17213 : ℕ)^5159*50000000000000000000^1024 ≤ 7065611091666231^1024*100000^5159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17213 100000 7065611091666231 50000000000000000000 5159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17213/100000 : ℝ)) (X := (7065611091666231/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000853664714345013/50000000000000000000 : ℝ) ≤ (10000033888221997/10000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (50000853664714345013/50000000000000000000 : ℝ)^1024 ≤ (10000033888221997/10000000000000000 : ℝ)^5159 := by
      have hnat : (50000853664714345013 : ℕ)^1024*10000000000000000^5159 ≤ 10000033888221997^5159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000853664714345013 50000000000000000000 10000033888221997 10000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000033888221997/10000000000000000 : ℝ)) (X := (50000853664714345013/50000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000599395475907099/4000000000000000000 : ℝ) ≤ (10000297414281529/10000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (4000599395475907099/4000000000000000000 : ℝ)^1024 ≤ (10000297414281529/10000000000000000 : ℝ)^5159 := by
      have hnat : (4000599395475907099 : ℕ)^1024*10000000000000000^5159 ≤ 10000297414281529^5159*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000599395475907099 4000000000000000000 10000297414281529 10000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000297414281529/10000000000000000 : ℝ)) (X := (4000599395475907099/4000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007065611091666231/25000000000000000000 : ℝ) ≤ (10000560940341061/10000000000000000 : ℝ) ^ (5159/1024 : ℝ) := by
    have hpowers : (25007065611091666231/25000000000000000000 : ℝ)^1024 ≤ (10000560940341061/10000000000000000 : ℝ)^5159 := by
      have hnat : (25007065611091666231 : ℕ)^1024*10000000000000000^5159 ≤ 10000560940341061^5159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007065611091666231 25000000000000000000 10000560940341061 10000000000000000 1024 5159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000560940341061/10000000000000000 : ℝ)) (X := (25007065611091666231/25000000000000000000 : ℝ)) (by norm_num) 5159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(853664714345013/100000000000000000000 : ℝ) ≤ ((459469074282887699/459500000000000000 : ℝ)+2*(65881514883/183800000000000 : ℝ)*(9861/100000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (459469074282887699/459500000000000000 : ℝ)+2*(65881514883/183800000000000 : ℝ)*(9861/100000 : ℝ)=(10000033888221997/10000000000000000 : ℝ) by norm_num, show 1+2*(853664714345013/100000000000000000000 : ℝ)=(50000853664714345013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7065611091666231/50000000000000000000 : ℝ)+(853664714345013/100000000000000000000 : ℝ) ≤ ((459469074282887699/459500000000000000 : ℝ)+(65881514883/183800000000000 : ℝ)*((17213/100000 : ℝ)+(9861/100000 : ℝ)))^(5159/1024 : ℝ) := by
    rw [show (459469074282887699/459500000000000000 : ℝ)+(65881514883/183800000000000 : ℝ)*((17213/100000 : ℝ)+(9861/100000 : ℝ))=(10000297414281529/10000000000000000 : ℝ) by norm_num, show 1+(7065611091666231/50000000000000000000 : ℝ)+(853664714345013/100000000000000000000 : ℝ)=(4000599395475907099/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7065611091666231/50000000000000000000 : ℝ) ≤ ((459469074282887699/459500000000000000 : ℝ)+2*(65881514883/183800000000000 : ℝ)*(17213/100000 : ℝ))^(5159/1024 : ℝ) := by
    rw [show (459469074282887699/459500000000000000 : ℝ)+2*(65881514883/183800000000000 : ℝ)*(17213/100000 : ℝ)=(10000560940341061/10000000000000000 : ℝ) by norm_num, show 1+2*(7065611091666231/50000000000000000000 : ℝ)=(25007065611091666231/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (459469074282887699/459500000000000000 : ℝ)*(X 1 0+X 2 0)+(65881514883/183800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9861/100000 : ℝ)) (hi := (17213/100000 : ℝ)) (c := (459469074282887699/459500000000000000 : ℝ)) (alpha := (65881514883/183800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (459469074282887699/459500000000000000 : ℝ)*(X 0 1+X 2 1)+(65881514883/183800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9861/100000 : ℝ)) (hi := (17213/100000 : ℝ)) (c := (459469074282887699/459500000000000000 : ℝ)) (alpha := (65881514883/183800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (459469074282887699/459500000000000000 : ℝ)*(X 0 2+X 1 2)+(65881514883/183800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5159/1024 : ℝ)) (lo := (9861/100000 : ℝ)) (hi := (17213/100000 : ℝ)) (c := (459469074282887699/459500000000000000 : ℝ)) (alpha := (65881514883/183800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-228713193/2000000000 : ℝ)*X 0 0+(271320207/500000000 : ℝ)*X 0 1+(5426403353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612995033/5000000000 : ℝ)*X 1 0+(-35710643/250000000 : ℝ)*X 1 1+(678300541/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225990969/10000000000 : ℝ)*X 2 0+(678300433/1250000000 : ℝ)*X 2 1+(-357106419/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((902210373/2000000000 : ℝ)*X 0 0+(3957679529/10000000000 : ℝ)*X 0 1+(197883951/500000000 : ℝ)*X 0 2+(902210373/2000000000 : ℝ)*X 1 0+(3957679529/10000000000 : ℝ)*X 1 1+(197883951/500000000 : ℝ)*X 1 2+(902210373/2000000000 : ℝ)*X 2 0+(3957679529/10000000000 : ℝ)*X 2 1+(197883951/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-914626549/5000000000 : ℝ)*X 0 0+(5176438413/10000000000 : ℝ)*X 0 1+(5176438461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5396216519/10000000000 : ℝ)*X 1 0+(-768784911/5000000000 : ℝ)*X 1 1+(517643853/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5396216461/10000000000 : ℝ)*X 2 0+(1035287727/2000000000 : ℝ)*X 2 1+(-1537569761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((932130541/2500000000 : ℝ)*X 0 0+(4348088559/10000000000 : ℝ)*X 0 1+(543511027/1250000000 : ℝ)*X 0 2+(932130541/2500000000 : ℝ)*X 1 0+(4348088559/10000000000 : ℝ)*X 1 1+(543511027/1250000000 : ℝ)*X 1 2+(932130541/2500000000 : ℝ)*X 2 0+(4348088559/10000000000 : ℝ)*X 2 1+(543511027/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-841033131/5000000000 : ℝ)*X 0 0+(124821187/250000000 : ℝ)*X 0 1+(1367463279/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1039282889/2000000000 : ℝ)*X 1 0+(-1408627371/10000000000 : ℝ)*X 1 1+(1367463323/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196413147/10000000000 : ℝ)*X 2 0+(5469854407/10000000000 : ℝ)*X 2 1+(-281725521/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4642049077/10000000000 : ℝ)*X 0 0+(194482073/500000000 : ℝ)*X 0 1+(3889640807/10000000000 : ℝ)*X 0 2+(4642049077/10000000000 : ℝ)*X 1 0+(194482073/500000000 : ℝ)*X 1 1+(3889640807/10000000000 : ℝ)*X 1 2+(4642049077/10000000000 : ℝ)*X 2 0+(194482073/500000000 : ℝ)*X 2 1+(3889640807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-257167113/2000000000 : ℝ)*X 0 0+(1400237353/2500000000 : ℝ)*X 0 1+(2575578463/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5413460401/10000000000 : ℝ)*X 1 0+(-309627961/2000000000 : ℝ)*X 1 1+(2575578783/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2706730743/5000000000 : ℝ)*X 2 0+(515115571/1000000000 : ℝ)*X 2 1+(-193517603/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((911598337/2500000000 : ℝ)*X 0 0+(4387470647/10000000000 : ℝ)*X 0 1+(1096867149/2500000000 : ℝ)*X 0 2+(911598337/2500000000 : ℝ)*X 1 0+(4387470647/10000000000 : ℝ)*X 1 1+(1096867149/2500000000 : ℝ)*X 1 2+(911598337/2500000000 : ℝ)*X 2 0+(4387470647/10000000000 : ℝ)*X 2 1+(1096867149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1693_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66597/100000 : ℝ) ≤ (-15300089564844511136731482336837/22975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2695447/12500000000000 : ℝ)*(lower0) + (6479953/6250000000000 : ℝ)*(lower2) + (99196057/100000000000000 : ℝ)*(lower4) + (1313268832649421/100000000000000 : ℝ)*(major0) + (1313268832649421/100000000000000 : ℝ)*(major1) + (1313268832649421/100000000000000 : ℝ)*(major2) + (977590012630893/50000000000000 : ℝ)*(sp4) + (1955178612868647/100000000000000 : ℝ)*(sp5) + (122198089840243/6250000000000 : ℝ)*(sp6) + (43346619897431/6250000000000 : ℝ)*(sp7) + (311271249/100000000000000 : ℝ)*(sp8) + (1723664389/100000000000000 : ℝ)*(sp13) + (2724772287/25000000000000 : ℝ)*(sp14) + (239542539/2500000000000 : ℝ)*(sp15) + (86694437507557/12500000000000 : ℝ)*(f.failure) + (488795084133259/25000000000000 : ℝ)*(f.sum) + (31277911305277/9190000000000000000000000000 : ℝ)*base66 + (357666547466329779/45950000000000000000000000000000 : ℝ)*base67 + (146378145292529779/45950000000000000000000000000000 : ℝ)*base69 + (761683517666529779/45950000000000000000000000000000 : ℝ)*base71 + (56525869998793/9190000000000000000000000000 : ℝ)*base73 + (78504502348770221/45950000000000000000000000000000 : ℝ)*base76 + (616083787251770221/45950000000000000000000000000000 : ℝ)*base78 + (109097273645429779/45950000000000000000000000000000 : ℝ)*base79 + (22294724839303/9190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (8630857/1250000000000000000000 : ℝ)*base90 + (8630857/1250000000000000000000 : ℝ)*base92 + (8630857/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58001/100000 : ℝ) ≤ (3331598225036496261568173136167/5743750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8472161/50000000000000 : ℝ)*(lower1) + (22387457/100000000000000 : ℝ)*(lower2) + (92160747/100000000000000 : ℝ)*(upper4) + (706589067878061/50000000000000 : ℝ)*(major0) + (706589067878061/50000000000000 : ℝ)*(major1) + (706589067878061/50000000000000 : ℝ)*(major2) + (2060698077716507/100000000000000 : ℝ)*(sp0) + (2060696088122323/100000000000000 : ℝ)*(sp1) + (64396884073413/3125000000000 : ℝ)*(sp2) + (746316870265849/100000000000000 : ℝ)*(sp3) + (6564714061/100000000000000 : ℝ)*(sp5) + (18456931/781250000000 : ℝ)*(sp6) + (2119610373/100000000000000 : ℝ)*(sp7) + (4575119877/100000000000000 : ℝ)*(sp8) + (373159494938111/50000000000000 : ℝ)*(f.failure) + (2060702652836383/100000000000000 : ℝ)*(f.sum) + (22356504110703/4595000000000000000000000000 : ℝ)*base65 + (123493657706270861/22975000000000000000000000000000 : ℝ)*base68 + (132482871898195861/22975000000000000000000000000000 : ℝ)*base70 + (15813968974879139/22975000000000000000000000000000 : ℝ)*base71 + (164608213107/4595000000000000000000000000 : ℝ)*base74 + (207462923291920861/22975000000000000000000000000000 : ℝ)*base76 + (132707591705745861/22975000000000000000000000000000 : ℝ)*base78 + (93408376854170861/22975000000000000000000000000000 : ℝ)*base80 + (16394804186117/4595000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (31055989/5000000000000000000000 : ℝ)*base89 + (31055989/5000000000000000000000 : ℝ)*base91 + (31055989/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8091/10000 : ℝ) ≤ (9294828672231873324719789263599/11487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11819601/10000000000000 : ℝ)*(upper1) + (45946391/25000000000000 : ℝ)*(upper2) + (3972467/10000000000000 : ℝ)*(lower5) + (721313926381211/50000000000000 : ℝ)*(major0) + (721313926381211/50000000000000 : ℝ)*(major1) + (721313926381211/50000000000000 : ℝ)*(major2) + (51291015349/100000000000000 : ℝ)*(sp1) + (40575201101/50000000000000 : ℝ)*(sp2) + (948824821/100000000000000 : ℝ)*(sp3) + (1154701493/50000000000000 : ℝ)*(sp4) + (20964107533789/1000000000000 : ℝ)*(sp8) + (2096361771766537/100000000000000 : ℝ)*(sp9) + (524082978094921/25000000000000 : ℝ)*(sp10) + (47616927837197/6250000000000 : ℝ)*(sp11) + (761871794219973/100000000000000 : ℝ)*(f.failure) + (1048206531390943/50000000000000 : ℝ)*(f.sum) + (11069079399041/2297500000000000000000000000 : ℝ)*base66 + (44986369665080989/22975000000000000000000000000000 : ℝ)*base67 + (146072795145655989/22975000000000000000000000000000 : ℝ)*base69 + (194877534517605989/22975000000000000000000000000000 : ℝ)*base71 + (17570440604277/4595000000000000000000000000 : ℝ)*base74 + (145598974138905989/22975000000000000000000000000000 : ℝ)*base75 + (70787967648780989/22975000000000000000000000000000 : ℝ)*base77 + (133825596558530989/22975000000000000000000000000000 : ℝ)*base79 + (496693373327/4595000000000000000000000000 : ℝ)*base82 + (24753673/10000000000000000000000 : ℝ)*base90 + (24753673/10000000000000000000000 : ℝ)*base92 + (24753673/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-2818/3125 : ℝ) ≤ (-20717453087176101336382473262491/22975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73792991/100000000000000 : ℝ)*(upper1) + (26146623/12500000000000 : ℝ)*(upper3) + (42890261/100000000000000 : ℝ)*(upper5) + (1490056666420603/100000000000000 : ℝ)*(major0) + (1490056666420603/100000000000000 : ℝ)*(major1) + (1490056666420603/100000000000000 : ℝ)*(major2) + (3489273153/100000000000000 : ℝ)*(sp4) + (189204143/25000000000000 : ℝ)*(sp5) + (140636417677/100000000000000 : ℝ)*(sp6) + (9244585419/50000000000000 : ℝ)*(sp7) + (1111624100262669/50000000000000 : ℝ)*(sp12) + (2223250932981919/100000000000000 : ℝ)*(sp13) + (1111555526690407/50000000000000 : ℝ)*(sp14) + (19672527997583/2500000000000 : ℝ)*(sp15) + (393459804537079/50000000000000 : ℝ)*(f.failure) + (2223251689798491/100000000000000 : ℝ)*(f.sum) + (5838939634871/9190000000000000000000000000 : ℝ)*base66 + (138348134039334997/45950000000000000000000000000000 : ℝ)*base67 + (524663829943434997/45950000000000000000000000000000 : ℝ)*base69 + (128276204109934997/45950000000000000000000000000000 : ℝ)*base71 + (9810071051879/9190000000000000000000000000 : ℝ)*base73 + (515655188544915003/45950000000000000000000000000000 : ℝ)*base76 + (112457075081634997/45950000000000000000000000000000 : ℝ)*base77 + (20605386331165003/45950000000000000000000000000000 : ℝ)*base80 + (196466401701601/9190000000000000000000000000 : ℝ)*base82 + (19057821/5000000000000000000000 : ℝ)*base89 + (19057821/5000000000000000000000 : ℝ)*base91 + (19057821/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1693_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17213/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66597/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58001/100000 : ℝ) else (8091/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2818/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1693_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1693_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66597/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58001/100000 : ℝ) else (8091/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2818/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1693_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1693_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1693_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5159/1024 : ℝ) ≤ p) (hpb : p ≤ (5167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (189353099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66597/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58001/100000 : ℝ) else (8091/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2818/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1693_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

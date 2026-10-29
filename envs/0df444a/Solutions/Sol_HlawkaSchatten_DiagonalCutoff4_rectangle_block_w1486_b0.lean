-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1486_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:14.013056+00:00
-- url     : https://prove2.me/submissions/96488622-f421-48b6-a56c-236236641f87

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
theorem support_rectangle_w1486_s0_0 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1713760793/10000000000 : ℝ)*x 0 + (2966564917/5000000000 : ℝ)*x 1 + (4844039853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1713760793/10000000000 : ℝ)^4469 ≤ (10144899237743/100000000000000 : ℝ)^3445 := by
    have hnat : (1713760793 : ℕ)^4469*100000000000000^3445 ≤ 10144899237743^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713760793 10000000000 10144899237743 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2966564917/5000000000 : ℝ)^4469 ≤ (50803566851737/100000000000000 : ℝ)^3445 := by
    have hnat : (2966564917 : ℕ)^4469*100000000000000^3445 ≤ 50803566851737^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966564917 5000000000 50803566851737 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4844039853/10000000000 : ℝ)^4469 ≤ (7810306781377/20000000000000 : ℝ)^3445 := by
    have hnat : (4844039853 : ℕ)^4469*20000000000000^3445 ≤ 7810306781377^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844039853 10000000000 7810306781377 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1713760793/10000000000 : ℝ), (2966564917/5000000000 : ℝ), (4844039853/10000000000 : ℝ)] ![(10144899237743/100000000000000 : ℝ), (50803566851737/100000000000000 : ℝ), (7810306781377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1713760793/10000000000 : ℝ)|^4469 ≤ (10144899237743/100000000000000 : ℝ)^3445
        have hw : |(-1713760793/10000000000 : ℝ)|=(1713760793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2966564917/5000000000 : ℝ)|^4469 ≤ (50803566851737/100000000000000 : ℝ)^3445
        have hw : |(2966564917/5000000000 : ℝ)|=(2966564917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4844039853/10000000000 : ℝ)|^4469 ≤ (7810306781377/20000000000000 : ℝ)^3445
        have hw : |(4844039853/10000000000 : ℝ)|=(4844039853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s0_1 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1370914823/2500000000 : ℝ)*x 0 + (-1163147391/5000000000 : ℝ)*x 1 + (2422019943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370914823/2500000000 : ℝ)^4469 ≤ (22934070934627/50000000000000 : ℝ)^3445 := by
    have hnat : (1370914823 : ℕ)^4469*50000000000000^3445 ≤ 22934070934627^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370914823 2500000000 22934070934627 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163147391/5000000000 : ℝ)^4469 ≤ (15080323856661/100000000000000 : ℝ)^3445 := by
    have hnat : (1163147391 : ℕ)^4469*100000000000000^3445 ≤ 15080323856661^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163147391 5000000000 15080323856661 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2422019943/5000000000 : ℝ)^4469 ≤ (39051534252001/100000000000000 : ℝ)^3445 := by
    have hnat : (2422019943 : ℕ)^4469*100000000000000^3445 ≤ 39051534252001^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422019943 5000000000 39051534252001 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1370914823/2500000000 : ℝ), (-1163147391/5000000000 : ℝ), (2422019943/5000000000 : ℝ)] ![(22934070934627/50000000000000 : ℝ), (15080323856661/100000000000000 : ℝ), (39051534252001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1370914823/2500000000 : ℝ)|^4469 ≤ (22934070934627/50000000000000 : ℝ)^3445
        have hw : |(1370914823/2500000000 : ℝ)|=(1370914823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1163147391/5000000000 : ℝ)|^4469 ≤ (15080323856661/100000000000000 : ℝ)^3445
        have hw : |(-1163147391/5000000000 : ℝ)|=(1163147391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2422019943/5000000000 : ℝ)|^4469 ≤ (39051534252001/100000000000000 : ℝ)^3445
        have hw : |(2422019943/5000000000 : ℝ)|=(2422019943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s0_2 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5483659361/10000000000 : ℝ)*x 0 + (1211009981/2500000000 : ℝ)*x 1 + (-2326294647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5483659361/10000000000 : ℝ)^4469 ≤ (1146703565449/2500000000000 : ℝ)^3445 := by
    have hnat : (5483659361 : ℕ)^4469*2500000000000^3445 ≤ 1146703565449^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483659361 10000000000 1146703565449 2500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1211009981/2500000000 : ℝ)^4469 ≤ (610180228897/1562500000000 : ℝ)^3445 := by
    have hnat : (1211009981 : ℕ)^4469*1562500000000^3445 ≤ 610180228897^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211009981 2500000000 610180228897 1562500000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2326294647/10000000000 : ℝ)^4469 ≤ (7540161360693/50000000000000 : ℝ)^3445 := by
    have hnat : (2326294647 : ℕ)^4469*50000000000000^3445 ≤ 7540161360693^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2326294647 10000000000 7540161360693 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5483659361/10000000000 : ℝ), (1211009981/2500000000 : ℝ), (-2326294647/10000000000 : ℝ)] ![(1146703565449/2500000000000 : ℝ), (610180228897/1562500000000 : ℝ), (7540161360693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5483659361/10000000000 : ℝ)|^4469 ≤ (1146703565449/2500000000000 : ℝ)^3445
        have hw : |(5483659361/10000000000 : ℝ)|=(5483659361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1211009981/2500000000 : ℝ)|^4469 ≤ (610180228897/1562500000000 : ℝ)^3445
        have hw : |(1211009981/2500000000 : ℝ)|=(1211009981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2326294647/10000000000 : ℝ)|^4469 ≤ (7540161360693/50000000000000 : ℝ)^3445
        have hw : |(-2326294647/10000000000 : ℝ)|=(2326294647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s0_3 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4152229797/10000000000 : ℝ)*x 0 + (3091367001/10000000000 : ℝ)*x 1 + (5515793739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152229797/10000000000 : ℝ)^4469 ≤ (31975579916251/100000000000000 : ℝ)^3445 := by
    have hnat : (4152229797 : ℕ)^4469*100000000000000^3445 ≤ 31975579916251^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152229797 10000000000 31975579916251 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091367001/10000000000 : ℝ)^4469 ≤ (4361458086239/20000000000000 : ℝ)^3445 := by
    have hnat : (3091367001 : ℕ)^4469*20000000000000^3445 ≤ 4361458086239^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091367001 10000000000 4361458086239 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515793739/10000000000 : ℝ)^4469 ≤ (9243425926389/20000000000000 : ℝ)^3445 := by
    have hnat : (5515793739 : ℕ)^4469*20000000000000^3445 ≤ 9243425926389^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515793739 10000000000 9243425926389 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152229797/10000000000 : ℝ), (3091367001/10000000000 : ℝ), (5515793739/10000000000 : ℝ)] ![(31975579916251/100000000000000 : ℝ), (4361458086239/20000000000000 : ℝ), (9243425926389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152229797/10000000000 : ℝ)|^4469 ≤ (31975579916251/100000000000000 : ℝ)^3445
        have hw : |(4152229797/10000000000 : ℝ)|=(4152229797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091367001/10000000000 : ℝ)|^4469 ≤ (4361458086239/20000000000000 : ℝ)^3445
        have hw : |(3091367001/10000000000 : ℝ)|=(3091367001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515793739/10000000000 : ℝ)|^4469 ≤ (9243425926389/20000000000000 : ℝ)^3445
        have hw : |(5515793739/10000000000 : ℝ)|=(5515793739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s0_4 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1717509551/10000000000 : ℝ)*x 0 + (2435975649/5000000000 : ℝ)*x 1 + (5904215303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1717509551/10000000000 : ℝ)^4469 ≤ (317928007257/3125000000000 : ℝ)^3445 := by
    have hnat : (1717509551 : ℕ)^4469*3125000000000^3445 ≤ 317928007257^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717509551 10000000000 317928007257 3125000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2435975649/5000000000 : ℝ)^4469 ≤ (1229490105281/3125000000000 : ℝ)^3445 := by
    have hnat : (2435975649 : ℕ)^4469*3125000000000^3445 ≤ 1229490105281^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435975649 5000000000 1229490105281 3125000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5904215303/10000000000 : ℝ)^4469 ≤ (25241310190751/50000000000000 : ℝ)^3445 := by
    have hnat : (5904215303 : ℕ)^4469*50000000000000^3445 ≤ 25241310190751^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5904215303 10000000000 25241310190751 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1717509551/10000000000 : ℝ), (2435975649/5000000000 : ℝ), (5904215303/10000000000 : ℝ)] ![(317928007257/3125000000000 : ℝ), (1229490105281/3125000000000 : ℝ), (25241310190751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1717509551/10000000000 : ℝ)|^4469 ≤ (317928007257/3125000000000 : ℝ)^3445
        have hw : |(-1717509551/10000000000 : ℝ)|=(1717509551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2435975649/5000000000 : ℝ)|^4469 ≤ (1229490105281/3125000000000 : ℝ)^3445
        have hw : |(2435975649/5000000000 : ℝ)|=(2435975649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5904215303/10000000000 : ℝ)|^4469 ≤ (25241310190751/50000000000000 : ℝ)^3445
        have hw : |(5904215303/10000000000 : ℝ)|=(5904215303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s0_5 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5186249397/10000000000 : ℝ)*x 0 + (-1266119103/10000000000 : ℝ)*x 1 + (2952107677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5186249397/10000000000 : ℝ)^4469 ≤ (42667357080977/100000000000000 : ℝ)^3445 := by
    have hnat : (5186249397 : ℕ)^4469*100000000000000^3445 ≤ 42667357080977^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186249397 10000000000 42667357080977 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266119103/10000000000 : ℝ)^4469 ≤ (6850021958737/100000000000000 : ℝ)^3445 := by
    have hnat : (1266119103 : ℕ)^4469*100000000000000^3445 ≤ 6850021958737^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266119103 10000000000 6850021958737 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2952107677/5000000000 : ℝ)^4469 ≤ (25241310473591/50000000000000 : ℝ)^3445 := by
    have hnat : (2952107677 : ℕ)^4469*50000000000000^3445 ≤ 25241310473591^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2952107677 5000000000 25241310473591 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5186249397/10000000000 : ℝ), (-1266119103/10000000000 : ℝ), (2952107677/5000000000 : ℝ)] ![(42667357080977/100000000000000 : ℝ), (6850021958737/100000000000000 : ℝ), (25241310473591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5186249397/10000000000 : ℝ)|^4469 ≤ (42667357080977/100000000000000 : ℝ)^3445
        have hw : |(5186249397/10000000000 : ℝ)|=(5186249397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1266119103/10000000000 : ℝ)|^4469 ≤ (6850021958737/100000000000000 : ℝ)^3445
        have hw : |(-1266119103/10000000000 : ℝ)|=(1266119103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2952107677/5000000000 : ℝ)|^4469 ≤ (25241310473591/50000000000000 : ℝ)^3445
        have hw : |(2952107677/5000000000 : ℝ)|=(2952107677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s0_6 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324140591/625000000 : ℝ)*x 0 + (5904215227/10000000000 : ℝ)*x 1 + (-1266119213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324140591/625000000 : ℝ)^4469 ≤ (42667357710651/100000000000000 : ℝ)^3445 := by
    have hnat : (324140591 : ℕ)^4469*100000000000000^3445 ≤ 42667357710651^3445*625000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324140591 625000000 42667357710651 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5904215227/10000000000 : ℝ)^4469 ≤ (50482619538527/100000000000000 : ℝ)^3445 := by
    have hnat : (5904215227 : ℕ)^4469*100000000000000^3445 ≤ 50482619538527^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5904215227 10000000000 50482619538527 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1266119213/10000000000 : ℝ)^4469 ≤ (3425011365381/50000000000000 : ℝ)^3445 := by
    have hnat : (1266119213 : ℕ)^4469*50000000000000^3445 ≤ 3425011365381^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266119213 10000000000 3425011365381 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324140591/625000000 : ℝ), (5904215227/10000000000 : ℝ), (-1266119213/10000000000 : ℝ)] ![(42667357710651/100000000000000 : ℝ), (50482619538527/100000000000000 : ℝ), (3425011365381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324140591/625000000 : ℝ)|^4469 ≤ (42667357710651/100000000000000 : ℝ)^3445
        have hw : |(324140591/625000000 : ℝ)|=(324140591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5904215227/10000000000 : ℝ)|^4469 ≤ (50482619538527/100000000000000 : ℝ)^3445
        have hw : |(5904215227/10000000000 : ℝ)|=(5904215227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1266119213/10000000000 : ℝ)|^4469 ≤ (3425011365381/50000000000000 : ℝ)^3445
        have hw : |(-1266119213/10000000000 : ℝ)|=(1266119213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s0_7 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (832115123/2000000000 : ℝ)*x 0 + (109073203/200000000 : ℝ)*x 1 + (788933443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832115123/2000000000 : ℝ)^4469 ≤ (16029489064181/50000000000000 : ℝ)^3445 := by
    have hnat : (832115123 : ℕ)^4469*50000000000000^3445 ≤ 16029489064181^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832115123 2000000000 16029489064181 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109073203/200000000 : ℝ)^4469 ≤ (1423215379381/3125000000000 : ℝ)^3445 := by
    have hnat : (109073203 : ℕ)^4469*3125000000000^3445 ≤ 1423215379381^3445*200000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109073203 200000000 1423215379381 3125000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788933443/2500000000 : ℝ)^4469 ≤ (1399883107633/6250000000000 : ℝ)^3445 := by
    have hnat : (788933443 : ℕ)^4469*6250000000000^3445 ≤ 1399883107633^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788933443 2500000000 1399883107633 6250000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(832115123/2000000000 : ℝ), (109073203/200000000 : ℝ), (788933443/2500000000 : ℝ)] ![(16029489064181/50000000000000 : ℝ), (1423215379381/3125000000000 : ℝ), (1399883107633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(832115123/2000000000 : ℝ)|^4469 ≤ (16029489064181/50000000000000 : ℝ)^3445
        have hw : |(832115123/2000000000 : ℝ)|=(832115123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109073203/200000000 : ℝ)|^4469 ≤ (1423215379381/3125000000000 : ℝ)^3445
        have hw : |(109073203/200000000 : ℝ)|=(109073203/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788933443/2500000000 : ℝ)|^4469 ≤ (1399883107633/6250000000000 : ℝ)^3445
        have hw : |(788933443/2500000000 : ℝ)|=(788933443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1486_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1243/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1033/4000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4467/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4467 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4467*1^1024 ≤ 0^1024*1^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4467/1024 : ℝ) ≤ (1836810844641655477/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4467 ≤ (1836810844641655477/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4467*100000000000000000000^1024 ≤ 1836810844641655477^1024*5^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1836810844641655477 100000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1836810844641655477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4467 := by
      have hnat : (1 : ℕ)^1024*1^4467 ≤ 1^4467*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101836810844641655477/100000000000000000000 : ℝ) ≤ (200836231250369/200000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (101836810844641655477/100000000000000000000 : ℝ)^1024 ≤ (200836231250369/200000000000000 : ℝ)^4467 := by
      have hnat : (101836810844641655477 : ℕ)^1024*200000000000000^4467 ≤ 200836231250369^4467*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101836810844641655477 100000000000000000000 200836231250369 200000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200836231250369/200000000000000 : ℝ)) (X := (101836810844641655477/100000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51836810844641655477/50000000000000000000 : ℝ) ≤ (100836231250369/100000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (51836810844641655477/50000000000000000000 : ℝ)^1024 ≤ (100836231250369/100000000000000 : ℝ)^4467 := by
      have hnat : (51836810844641655477 : ℕ)^1024*100000000000000^4467 ≤ 100836231250369^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51836810844641655477 50000000000000000000 100836231250369 100000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100836231250369/100000000000000 : ℝ)) (X := (51836810844641655477/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(836231250369/80000000000000 : ℝ)*(0 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(836231250369/80000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1836810844641655477/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(836231250369/80000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4467/1024 : ℝ) := by
    rw [show (1 : ℝ)+(836231250369/80000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(200836231250369/200000000000000 : ℝ) by norm_num, show 1+(1836810844641655477/100000000000000000000 : ℝ)+(0 : ℝ)=(101836810844641655477/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1836810844641655477/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(836231250369/80000000000000 : ℝ)*(2/5 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(836231250369/80000000000000 : ℝ)*(2/5 : ℝ)=(100836231250369/100000000000000 : ℝ) by norm_num, show 1+2*(1836810844641655477/100000000000000000000 : ℝ)=(51836810844641655477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(836231250369/80000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (836231250369/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(836231250369/80000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (836231250369/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(836231250369/80000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (836231250369/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1713760793/10000000000 : ℝ)*X 0 0+(2966564917/5000000000 : ℝ)*X 0 1+(4844039853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1370914823/2500000000 : ℝ)*X 1 0+(-1163147391/5000000000 : ℝ)*X 1 1+(2422019943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5483659361/10000000000 : ℝ)*X 2 0+(1211009981/2500000000 : ℝ)*X 2 1+(-2326294647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4152229797/10000000000 : ℝ)*X 0 0+(3091367001/10000000000 : ℝ)*X 0 1+(5515793739/10000000000 : ℝ)*X 0 2+(4152229797/10000000000 : ℝ)*X 1 0+(3091367001/10000000000 : ℝ)*X 1 1+(5515793739/10000000000 : ℝ)*X 1 2+(4152229797/10000000000 : ℝ)*X 2 0+(3091367001/10000000000 : ℝ)*X 2 1+(5515793739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1717509551/10000000000 : ℝ)*X 0 0+(2435975649/5000000000 : ℝ)*X 0 1+(5904215303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5186249397/10000000000 : ℝ)*X 1 0+(-1266119103/10000000000 : ℝ)*X 1 1+(2952107677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((324140591/625000000 : ℝ)*X 2 0+(5904215227/10000000000 : ℝ)*X 2 1+(-1266119213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((832115123/2000000000 : ℝ)*X 0 0+(109073203/200000000 : ℝ)*X 0 1+(788933443/2500000000 : ℝ)*X 0 2+(832115123/2000000000 : ℝ)*X 1 0+(109073203/200000000 : ℝ)*X 1 1+(788933443/2500000000 : ℝ)*X 1 2+(832115123/2000000000 : ℝ)*X 2 0+(109073203/200000000 : ℝ)*X 2 1+(788933443/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3500389184360375133687/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22799937/50000000000000 : ℝ)*(base1) + (392897217/25000000000000 : ℝ)*(base19) + (1583142519/100000000000000 : ℝ)*(base23) + (1479319/800000000000 : ℝ)*(upper3) + (28224717/12500000000000 : ℝ)*(upper5) + (332670588266941/50000000000000 : ℝ)*(major0) + (332670588266941/50000000000000 : ℝ)*(major1) + (332670588266941/50000000000000 : ℝ)*(major2) + (918202909551343/100000000000000 : ℝ)*(sp0) + (459103505761783/50000000000000 : ℝ)*(sp1) + (229551749992479/25000000000000 : ℝ)*(sp2) + (412471055283813/100000000000000 : ℝ)*(sp3) + (2859580483/50000000000000 : ℝ)*(sp4) + (2435712359/100000000000000 : ℝ)*(sp7) + (206236768298023/50000000000000 : ℝ)*(f.failure) + (183641716622487/20000000000000 : ℝ)*(f.sum) + (3096064210771/2000000000000000000000000000 : ℝ)*base66 + (431421620771/4000000000000000000000000000 : ℝ)*base68 + (26773504176771/4000000000000000000000000000 : ℝ)*base70 + (5202068679229/4000000000000000000000000000 : ℝ)*base71 + (4912055350771/2000000000000000000000000000 : ℝ)*base74 + (14371223027229/4000000000000000000000000000 : ℝ)*base75 + (6073564936771/4000000000000000000000000000 : ℝ)*base78 + (6112323436771/4000000000000000000000000000 : ℝ)*base80 + (13218213854771/2000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (25361117/5000000000000000000000 : ℝ)*base89 + (25361117/5000000000000000000000 : ℝ)*base91 + (25361117/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10687375921377190059/2000000000000000000000000 : ℝ) := by norm_num
    linear_combination (294772351/25000000000000 : ℝ)*(base19) + (598850777/50000000000000 : ℝ)*(base23) + (22571971/20000000000000 : ℝ)*(base32) + (177736669/100000000000000 : ℝ)*(upper3) + (109321953/100000000000000 : ℝ)*(upper5) + (1403918895393/200000000000 : ℝ)*(major0) + (1403918895393/200000000000 : ℝ)*(major1) + (1403918895393/200000000000 : ℝ)*(major2) + (2925303987/100000000000000 : ℝ)*(sp1) + (1528842463/50000000000000 : ℝ)*(sp2) + (968743943559601/100000000000000 : ℝ)*(sp4) + (96873983916621/10000000000000 : ℝ)*(sp5) + (968739688173121/100000000000000 : ℝ)*(sp6) + (435174660850603/100000000000000 : ℝ)*(sp7) + (217587386855229/50000000000000 : ℝ)*(f.failure) + (968743943559601/100000000000000 : ℝ)*(f.sum) + (210624707/1600000000000000000000000 : ℝ)*base66 + (121433529249/16000000000000000000000000 : ℝ)*base67 + (167296632113/16000000000000000000000000 : ℝ)*base69 + (148386555313/16000000000000000000000000 : ℝ)*base71 + (18587130129/8000000000000000000000000 : ℝ)*base73 + (90079996609/16000000000000000000000000 : ℝ)*base75 + (23161817021/3200000000000000000000000 : ℝ)*base77 + (80713737361/16000000000000000000000000 : ℝ)*base79 + (24111653049/8000000000000000000000000 : ℝ)*base81 + (39069009/5000000000000000000000 : ℝ)*base90 + (39069009/5000000000000000000000 : ℝ)*base92 + (39069009/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1486_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1243/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1033/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1486_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1486_s1_0 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1874520239/10000000000 : ℝ)*x 0 + (5588425817/10000000000 : ℝ)*x 1 + (1271383283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1874520239/10000000000 : ℝ)^4469 ≤ (11396257837389/100000000000000 : ℝ)^3445 := by
    have hnat : (1874520239 : ℕ)^4469*100000000000000^3445 ≤ 11396257837389^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874520239 10000000000 11396257837389 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5588425817/10000000000 : ℝ)^4469 ≤ (47008156166479/100000000000000 : ℝ)^3445 := by
    have hnat : (5588425817 : ℕ)^4469*100000000000000^3445 ≤ 47008156166479^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588425817 10000000000 47008156166479 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271383283/2500000000 : ℝ)^4469 ≤ (2079779298801/5000000000000 : ℝ)^3445 := by
    have hnat : (1271383283 : ℕ)^4469*5000000000000^3445 ≤ 2079779298801^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271383283 2500000000 2079779298801 5000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1874520239/10000000000 : ℝ), (5588425817/10000000000 : ℝ), (1271383283/2500000000 : ℝ)] ![(11396257837389/100000000000000 : ℝ), (47008156166479/100000000000000 : ℝ), (2079779298801/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1874520239/10000000000 : ℝ)|^4469 ≤ (11396257837389/100000000000000 : ℝ)^3445
        have hw : |(-1874520239/10000000000 : ℝ)|=(1874520239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5588425817/10000000000 : ℝ)|^4469 ≤ (47008156166479/100000000000000 : ℝ)^3445
        have hw : |(5588425817/10000000000 : ℝ)|=(5588425817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271383283/2500000000 : ℝ)|^4469 ≤ (2079779298801/5000000000000 : ℝ)^3445
        have hw : |(1271383283/2500000000 : ℝ)|=(1271383283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s1_1 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347857861/2500000000 : ℝ)*x 0 + (-26752693/125000000 : ℝ)*x 1 + (2542768549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347857861/2500000000 : ℝ)^4469 ≤ (22434953607747/50000000000000 : ℝ)^3445 := by
    have hnat : (1347857861 : ℕ)^4469*50000000000000^3445 ≤ 22434953607747^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347857861 2500000000 22434953607747 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26752693/125000000 : ℝ)^4469 ≤ (676723235933/5000000000000 : ℝ)^3445 := by
    have hnat : (26752693 : ℕ)^4469*5000000000000^3445 ≤ 676723235933^3445*125000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26752693 125000000 676723235933 5000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542768549/5000000000 : ℝ)^4469 ≤ (41595628056883/100000000000000 : ℝ)^3445 := by
    have hnat : (2542768549 : ℕ)^4469*100000000000000^3445 ≤ 41595628056883^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542768549 5000000000 41595628056883 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347857861/2500000000 : ℝ), (-26752693/125000000 : ℝ), (2542768549/5000000000 : ℝ)] ![(22434953607747/50000000000000 : ℝ), (676723235933/5000000000000 : ℝ), (41595628056883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347857861/2500000000 : ℝ)|^4469 ≤ (22434953607747/50000000000000 : ℝ)^3445
        have hw : |(1347857861/2500000000 : ℝ)|=(1347857861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26752693/125000000 : ℝ)|^4469 ≤ (676723235933/5000000000000 : ℝ)^3445
        have hw : |(-26752693/125000000 : ℝ)|=(26752693/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542768549/5000000000 : ℝ)|^4469 ≤ (41595628056883/100000000000000 : ℝ)^3445
        have hw : |(2542768549/5000000000 : ℝ)|=(2542768549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s1_2 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391434397/10000000000 : ℝ)*x 0 + (5085533807/10000000000 : ℝ)*x 1 + (-214021581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391434397/10000000000 : ℝ)^4469 ≤ (4486993909677/10000000000000 : ℝ)^3445 := by
    have hnat : (5391434397 : ℕ)^4469*10000000000000^3445 ≤ 4486993909677^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391434397 10000000000 4486993909677 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085533807/10000000000 : ℝ)^4469 ≤ (20797796569021/50000000000000 : ℝ)^3445 := by
    have hnat : (5085533807 : ℕ)^4469*50000000000000^3445 ≤ 20797796569021^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085533807 10000000000 20797796569021 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214021581/1000000000 : ℝ)^4469 ≤ (6767233876997/50000000000000 : ℝ)^3445 := by
    have hnat : (214021581 : ℕ)^4469*50000000000000^3445 ≤ 6767233876997^3445*1000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214021581 1000000000 6767233876997 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391434397/10000000000 : ℝ), (5085533807/10000000000 : ℝ), (-214021581/1000000000 : ℝ)] ![(4486993909677/10000000000000 : ℝ), (20797796569021/50000000000000 : ℝ), (6767233876997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391434397/10000000000 : ℝ)|^4469 ≤ (4486993909677/10000000000000 : ℝ)^3445
        have hw : |(5391434397/10000000000 : ℝ)|=(5391434397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085533807/10000000000 : ℝ)|^4469 ≤ (20797796569021/50000000000000 : ℝ)^3445
        have hw : |(5085533807/10000000000 : ℝ)|=(5085533807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214021581/1000000000 : ℝ)|^4469 ≤ (6767233876997/50000000000000 : ℝ)^3445
        have hw : |(-214021581/1000000000 : ℝ)|=(214021581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s1_3 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259082017/10000000000 : ℝ)*x 0 + (74621407/200000000 : ℝ)*x 1 + (4850552667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259082017/10000000000 : ℝ)^4469 ≤ (3304707376619/10000000000000 : ℝ)^3445 := by
    have hnat : (4259082017 : ℕ)^4469*10000000000000^3445 ≤ 3304707376619^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259082017 10000000000 3304707376619 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74621407/200000000 : ℝ)^4469 ≤ (3479158406961/12500000000000 : ℝ)^3445 := by
    have hnat : (74621407 : ℕ)^4469*12500000000000^3445 ≤ 3479158406961^3445*200000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74621407 200000000 3479158406961 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4850552667/10000000000 : ℝ)^4469 ≤ (4889957371663/12500000000000 : ℝ)^3445 := by
    have hnat : (4850552667 : ℕ)^4469*12500000000000^3445 ≤ 4889957371663^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4850552667 10000000000 4889957371663 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259082017/10000000000 : ℝ), (74621407/200000000 : ℝ), (4850552667/10000000000 : ℝ)] ![(3304707376619/10000000000000 : ℝ), (3479158406961/12500000000000 : ℝ), (4889957371663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259082017/10000000000 : ℝ)|^4469 ≤ (3304707376619/10000000000000 : ℝ)^3445
        have hw : |(4259082017/10000000000 : ℝ)|=(4259082017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(74621407/200000000 : ℝ)|^4469 ≤ (3479158406961/12500000000000 : ℝ)^3445
        have hw : |(74621407/200000000 : ℝ)|=(74621407/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4850552667/10000000000 : ℝ)|^4469 ≤ (4889957371663/12500000000000 : ℝ)^3445
        have hw : |(4850552667/10000000000 : ℝ)|=(4850552667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s1_4 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-93743787/500000000 : ℝ)*x 0 + (2545684767/5000000000 : ℝ)*x 1 + (1395622971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93743787/500000000 : ℝ)^4469 ≤ (712441352053/6250000000000 : ℝ)^3445 := by
    have hnat : (93743787 : ℕ)^4469*6250000000000^3445 ≤ 712441352053^3445*500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93743787 500000000 712441352053 6250000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545684767/5000000000 : ℝ)^4469 ≤ (10414380778517/25000000000000 : ℝ)^3445 := by
    have hnat : (2545684767 : ℕ)^4469*25000000000000^3445 ≤ 10414380778517^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545684767 5000000000 10414380778517 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1395622971/2500000000 : ℝ)^4469 ≤ (733490863067/1562500000000 : ℝ)^3445 := by
    have hnat : (1395622971 : ℕ)^4469*1562500000000^3445 ≤ 733490863067^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395622971 2500000000 733490863067 1562500000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93743787/500000000 : ℝ), (2545684767/5000000000 : ℝ), (1395622971/2500000000 : ℝ)] ![(712441352053/6250000000000 : ℝ), (10414380778517/25000000000000 : ℝ), (733490863067/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93743787/500000000 : ℝ)|^4469 ≤ (712441352053/6250000000000 : ℝ)^3445
        have hw : |(-93743787/500000000 : ℝ)|=(93743787/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2545684767/5000000000 : ℝ)|^4469 ≤ (10414380778517/25000000000000 : ℝ)^3445
        have hw : |(2545684767/5000000000 : ℝ)|=(2545684767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1395622971/2500000000 : ℝ)|^4469 ≤ (733490863067/1562500000000 : ℝ)^3445
        have hw : |(1395622971/2500000000 : ℝ)|=(1395622971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s1_5 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262970261/500000000 : ℝ)*x 0 + (-3286519/20000000 : ℝ)*x 1 + (2791245971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262970261/500000000 : ℝ)^4469 ≤ (4344973916351/10000000000000 : ℝ)^3445 := by
    have hnat : (262970261 : ℕ)^4469*10000000000000^3445 ≤ 4344973916351^3445*500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262970261 500000000 4344973916351 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3286519/20000000 : ℝ)^4469 ≤ (1200855618637/12500000000000 : ℝ)^3445 := by
    have hnat : (3286519 : ℕ)^4469*12500000000000^3445 ≤ 1200855618637^3445*20000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3286519 20000000 1200855618637 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2791245971/5000000000 : ℝ)^4469 ≤ (9388683173797/20000000000000 : ℝ)^3445 := by
    have hnat : (2791245971 : ℕ)^4469*20000000000000^3445 ≤ 9388683173797^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791245971 5000000000 9388683173797 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262970261/500000000 : ℝ), (-3286519/20000000 : ℝ), (2791245971/5000000000 : ℝ)] ![(4344973916351/10000000000000 : ℝ), (1200855618637/12500000000000 : ℝ), (9388683173797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262970261/500000000 : ℝ)|^4469 ≤ (4344973916351/10000000000000 : ℝ)^3445
        have hw : |(262970261/500000000 : ℝ)|=(262970261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3286519/20000000 : ℝ)|^4469 ≤ (1200855618637/12500000000000 : ℝ)^3445
        have hw : |(-3286519/20000000 : ℝ)|=(3286519/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2791245971/5000000000 : ℝ)|^4469 ≤ (9388683173797/20000000000000 : ℝ)^3445
        have hw : |(2791245971/5000000000 : ℝ)|=(2791245971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s1_6 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525940521/1000000000 : ℝ)*x 0 + (1395622981/2500000000 : ℝ)*x 1 + (-82162977/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525940521/1000000000 : ℝ)^4469 ≤ (2172486952817/5000000000000 : ℝ)^3445 := by
    have hnat : (525940521 : ℕ)^4469*5000000000000^3445 ≤ 2172486952817^3445*1000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525940521 1000000000 2172486952817 5000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395622981/2500000000 : ℝ)^4469 ≤ (46943415672631/100000000000000 : ℝ)^3445 := by
    have hnat : (1395622981 : ℕ)^4469*100000000000000^3445 ≤ 46943415672631^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395622981 2500000000 46943415672631 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82162977/500000000 : ℝ)^4469 ≤ (4803422626227/50000000000000 : ℝ)^3445 := by
    have hnat : (82162977 : ℕ)^4469*50000000000000^3445 ≤ 4803422626227^3445*500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82162977 500000000 4803422626227 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525940521/1000000000 : ℝ), (1395622981/2500000000 : ℝ), (-82162977/500000000 : ℝ)] ![(2172486952817/5000000000000 : ℝ), (46943415672631/100000000000000 : ℝ), (4803422626227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525940521/1000000000 : ℝ)|^4469 ≤ (2172486952817/5000000000000 : ℝ)^3445
        have hw : |(525940521/1000000000 : ℝ)|=(525940521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1395622981/2500000000 : ℝ)|^4469 ≤ (46943415672631/100000000000000 : ℝ)^3445
        have hw : |(1395622981/2500000000 : ℝ)|=(1395622981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82162977/500000000 : ℝ)|^4469 ≤ (4803422626227/50000000000000 : ℝ)^3445
        have hw : |(-82162977/500000000 : ℝ)|=(82162977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s1_7 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259875879/10000000000 : ℝ)*x 0 + (2418782049/5000000000 : ℝ)*x 1 + (1872137127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259875879/10000000000 : ℝ)^4469 ≤ (826376616417/2500000000000 : ℝ)^3445 := by
    have hnat : (4259875879 : ℕ)^4469*2500000000000^3445 ≤ 826376616417^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259875879 10000000000 826376616417 2500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418782049/5000000000 : ℝ)^4469 ≤ (1949191173589/5000000000000 : ℝ)^3445 := by
    have hnat : (2418782049 : ℕ)^4469*5000000000000^3445 ≤ 1949191173589^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418782049 5000000000 1949191173589 5000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872137127/5000000000 : ℝ)^4469 ≤ (27961111861763/100000000000000 : ℝ)^3445 := by
    have hnat : (1872137127 : ℕ)^4469*100000000000000^3445 ≤ 27961111861763^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872137127 5000000000 27961111861763 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259875879/10000000000 : ℝ), (2418782049/5000000000 : ℝ), (1872137127/5000000000 : ℝ)] ![(826376616417/2500000000000 : ℝ), (1949191173589/5000000000000 : ℝ), (27961111861763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259875879/10000000000 : ℝ)|^4469 ≤ (826376616417/2500000000000 : ℝ)^3445
        have hw : |(4259875879/10000000000 : ℝ)|=(4259875879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418782049/5000000000 : ℝ)|^4469 ≤ (1949191173589/5000000000000 : ℝ)^3445
        have hw : |(2418782049/5000000000 : ℝ)|=(2418782049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1872137127/5000000000 : ℝ)|^4469 ≤ (27961111861763/100000000000000 : ℝ)^3445
        have hw : |(1872137127/5000000000 : ℝ)|=(1872137127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1486_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1033/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1243/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7993/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9313/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1033/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1243/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1033/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1243/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1033/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1243/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1033/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1243/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1033/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1243/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1033/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1243/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1243/50000 : ℝ) ^ (4467/1024 : ℝ) ≤ (10015832049741/100000000000000000000 : ℝ) := by
    have hpowers : (1243/50000 : ℝ)^4467 ≤ (10015832049741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1243 : ℕ)^4467*100000000000000000000^1024 ≤ 10015832049741^1024*50000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1243 50000 10015832049741 100000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1243/50000 : ℝ)) (X := (10015832049741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1033/4000 : ℝ) ^ (4467/1024 : ℝ) ≤ (10894336053481849/4000000000000000000 : ℝ) := by
    have hpowers : (1033/4000 : ℝ)^4467 ≤ (10894336053481849/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1033 : ℕ)^4467*4000000000000000000^1024 ≤ 10894336053481849^1024*4000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1033 4000 10894336053481849 4000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1033/4000 : ℝ)) (X := (10894336053481849/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000010015832049741/50000000000000000000 : ℝ) ≤ (1000000045919907/1000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (50000010015832049741/50000000000000000000 : ℝ)^1024 ≤ (1000000045919907/1000000000000000 : ℝ)^4467 := by
      have hnat : (50000010015832049741 : ℕ)^1024*1000000000000000^4467 ≤ 1000000045919907^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000010015832049741 50000000000000000000 1000000045919907 1000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000045919907/1000000000000000 : ℝ)) (X := (50000010015832049741/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50136184208584547983/50000000000000000000 : ℝ) ≤ (10006237138433181/10000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (50136184208584547983/50000000000000000000 : ℝ)^1024 ≤ (10006237138433181/10000000000000000 : ℝ)^4467 := by
      have hnat : (50136184208584547983 : ℕ)^1024*10000000000000000^4467 ≤ 10006237138433181^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50136184208584547983 50000000000000000000 10006237138433181 10000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006237138433181/10000000000000000 : ℝ)) (X := (50136184208584547983/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2010894336053481849/2000000000000000000 : ℝ) ≤ (2503118454416823/2500000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (2010894336053481849/2000000000000000000 : ℝ)^1024 ≤ (2503118454416823/2500000000000000 : ℝ)^4467 := by
      have hnat : (2010894336053481849 : ℕ)^1024*2500000000000000^4467 ≤ 2503118454416823^4467*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2010894336053481849 2000000000000000000 2503118454416823 2500000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503118454416823/2500000000000000 : ℝ)) (X := (2010894336053481849/2000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10015832049741/100000000000000000000 : ℝ) ≤ ((116679500974047547419/116695000000000000000 : ℝ)+2*(6236679234111/2333900000000000 : ℝ)*(1243/50000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (116679500974047547419/116695000000000000000 : ℝ)+2*(6236679234111/2333900000000000 : ℝ)*(1243/50000 : ℝ)=(1000000045919907/1000000000000000 : ℝ) by norm_num, show 1+2*(10015832049741/100000000000000000000 : ℝ)=(50000010015832049741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10894336053481849/4000000000000000000 : ℝ)+(10015832049741/100000000000000000000 : ℝ) ≤ ((116679500974047547419/116695000000000000000 : ℝ)+(6236679234111/2333900000000000 : ℝ)*((1033/4000 : ℝ)+(1243/50000 : ℝ)))^(4467/1024 : ℝ) := by
    rw [show (116679500974047547419/116695000000000000000 : ℝ)+(6236679234111/2333900000000000 : ℝ)*((1033/4000 : ℝ)+(1243/50000 : ℝ))=(10006237138433181/10000000000000000 : ℝ) by norm_num, show 1+(10894336053481849/4000000000000000000 : ℝ)+(10015832049741/100000000000000000000 : ℝ)=(50136184208584547983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10894336053481849/4000000000000000000 : ℝ) ≤ ((116679500974047547419/116695000000000000000 : ℝ)+2*(6236679234111/2333900000000000 : ℝ)*(1033/4000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (116679500974047547419/116695000000000000000 : ℝ)+2*(6236679234111/2333900000000000 : ℝ)*(1033/4000 : ℝ)=(2503118454416823/2500000000000000 : ℝ) by norm_num, show 1+2*(10894336053481849/4000000000000000000 : ℝ)=(2010894336053481849/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (116679500974047547419/116695000000000000000 : ℝ)*(X 1 0+X 2 0)+(6236679234111/2333900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (1243/50000 : ℝ)) (hi := (1033/4000 : ℝ)) (c := (116679500974047547419/116695000000000000000 : ℝ)) (alpha := (6236679234111/2333900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (116679500974047547419/116695000000000000000 : ℝ)*(X 0 1+X 2 1)+(6236679234111/2333900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (1243/50000 : ℝ)) (hi := (1033/4000 : ℝ)) (c := (116679500974047547419/116695000000000000000 : ℝ)) (alpha := (6236679234111/2333900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (116679500974047547419/116695000000000000000 : ℝ)*(X 0 2+X 1 2)+(6236679234111/2333900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (1243/50000 : ℝ)) (hi := (1033/4000 : ℝ)) (c := (116679500974047547419/116695000000000000000 : ℝ)) (alpha := (6236679234111/2333900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1874520239/10000000000 : ℝ)*X 0 0+(5588425817/10000000000 : ℝ)*X 0 1+(1271383283/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1347857861/2500000000 : ℝ)*X 1 0+(-26752693/125000000 : ℝ)*X 1 1+(2542768549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5391434397/10000000000 : ℝ)*X 2 0+(5085533807/10000000000 : ℝ)*X 2 1+(-214021581/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4259082017/10000000000 : ℝ)*X 0 0+(74621407/200000000 : ℝ)*X 0 1+(4850552667/10000000000 : ℝ)*X 0 2+(4259082017/10000000000 : ℝ)*X 1 0+(74621407/200000000 : ℝ)*X 1 1+(4850552667/10000000000 : ℝ)*X 1 2+(4259082017/10000000000 : ℝ)*X 2 0+(74621407/200000000 : ℝ)*X 2 1+(4850552667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-93743787/500000000 : ℝ)*X 0 0+(2545684767/5000000000 : ℝ)*X 0 1+(1395622971/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262970261/500000000 : ℝ)*X 1 0+(-3286519/20000000 : ℝ)*X 1 1+(2791245971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525940521/1000000000 : ℝ)*X 2 0+(1395622981/2500000000 : ℝ)*X 2 1+(-82162977/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4259875879/10000000000 : ℝ)*X 0 0+(2418782049/5000000000 : ℝ)*X 0 1+(1872137127/5000000000 : ℝ)*X 0 2+(4259875879/10000000000 : ℝ)*X 1 0+(2418782049/5000000000 : ℝ)*X 1 1+(1872137127/5000000000 : ℝ)*X 1 2+(4259875879/10000000000 : ℝ)*X 2 0+(2418782049/5000000000 : ℝ)*X 2 1+(1872137127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33140239421146555038608463/3646718750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1413885307/100000000000000 : ℝ)*(base19) + (2181310141/100000000000000 : ℝ)*(base23) + (14457307/6250000000000 : ℝ)*(upper3) + (86732267/50000000000000 : ℝ)*(upper4) + (40128001/100000000000000 : ℝ)*(upper5) + (7204572213711/500000000000 : ℝ)*(major0) + (7204572213711/500000000000 : ℝ)*(major1) + (7204572213711/500000000000 : ℝ)*(major2) + (248564838913421/12500000000000 : ℝ)*(sp0) + (1988542494448699/100000000000000 : ℝ)*(sp1) + (994270863511933/50000000000000 : ℝ)*(sp2) + (446637995178257/50000000000000 : ℝ)*(sp3) + (12598513319/50000000000000 : ℝ)*(sp4) + (1736774193/20000000000000 : ℝ)*(sp7) + (446642337113739/50000000000000 : ℝ)*(f.failure) + (1988543908334007/100000000000000 : ℝ)*(f.sum) + (35207037333599/23339000000000000000000000000 : ℝ)*base66 + (436230035507743091/58347500000000000000000000000000 : ℝ)*base68 + (99193852786798091/58347500000000000000000000000000 : ℝ)*base70 + (220642587743315591/58347500000000000000000000000000 : ℝ)*base72 + (3604376989613/466780000000000000000000000 : ℝ)*base74 + (60922602046636909/58347500000000000000000000000000 : ℝ)*base75 + (474969272148800591/58347500000000000000000000000000 : ℝ)*base78 + (365377004170858091/58347500000000000000000000000000 : ℝ)*base80 + (3875388822287/1458687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (12754281/5000000000000000000000 : ℝ)*base89 + (12754281/5000000000000000000000 : ℝ)*base91 + (12754281/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (651608238522609314218143/58347500000000000000000000000 : ℝ) := by norm_num
    linear_combination (425117819/20000000000000 : ℝ)*(base19) + (2267129031/100000000000000 : ℝ)*(base23) + (4541139/1562500000000 : ℝ)*(upper3) + (61078391/100000000000000 : ℝ)*(lower4) + (1812981/781250000000 : ℝ)*(upper5) + (737705583151561/50000000000000 : ℝ)*(major0) + (737705583151561/50000000000000 : ℝ)*(major1) + (737705583151561/50000000000000 : ℝ)*(major2) + (2656810717/20000000000000 : ℝ)*(sp1) + (722505733/5000000000000 : ℝ)*(sp2) + (2036151287373899/100000000000000 : ℝ)*(sp4) + (2036135877731219/100000000000000 : ℝ)*(sp5) + (63629205316569/3125000000000 : ℝ)*(sp6) + (457335336487591/50000000000000 : ℝ)*(sp7) + (457335336487591/50000000000000 : ℝ)*(f.failure) + (2036151287373899/100000000000000 : ℝ)*(f.sum) + (73236327693117/29173750000000000000000000000 : ℝ)*base66 + (13816079824530421059/5834750000000000000000000000000000 : ℝ)*base67 + (17828634532779078941/5834750000000000000000000000000000 : ℝ)*base70 + (34491659183130578941/5834750000000000000000000000000000 : ℝ)*base72 + (239063806114011/58347500000000000000000000000 : ℝ)*base73 + (24147736100178921059/5834750000000000000000000000000000 : ℝ)*base75 + (22449048975985578941/5834750000000000000000000000000000 : ℝ)*base78 + (25430979716056921059/5834750000000000000000000000000000 : ℝ)*base79 + (96146804111259/58347500000000000000000000000 : ℝ)*base82 + (2466211/5000000000000000000000 : ℝ)*base90 + (2466211/5000000000000000000000 : ℝ)*base92 + (2466211/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1486_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1033/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1243/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7993/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9313/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1486_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1486_s2_0 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1902187339/10000000000 : ℝ)*x 0 + (1093348199/2000000000 : ℝ)*x 1 + (5189346631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1902187339/10000000000 : ℝ)^4469 ≤ (11614935917729/100000000000000 : ℝ)^3445 := by
    have hnat : (1902187339 : ℕ)^4469*100000000000000^3445 ≤ 11614935917729^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902187339 10000000000 11614935917729 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093348199/2000000000 : ℝ)^4469 ≤ (45684649026023/100000000000000 : ℝ)^3445 := by
    have hnat : (1093348199 : ℕ)^4469*100000000000000^3445 ≤ 45684649026023^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093348199 2000000000 45684649026023 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5189346631/10000000000 : ℝ)^4469 ≤ (854008300791/2000000000000 : ℝ)^3445 := by
    have hnat : (5189346631 : ℕ)^4469*2000000000000^3445 ≤ 854008300791^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189346631 10000000000 854008300791 2000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1902187339/10000000000 : ℝ), (1093348199/2000000000 : ℝ), (5189346631/10000000000 : ℝ)] ![(11614935917729/100000000000000 : ℝ), (45684649026023/100000000000000 : ℝ), (854008300791/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1902187339/10000000000 : ℝ)|^4469 ≤ (11614935917729/100000000000000 : ℝ)^3445
        have hw : |(-1902187339/10000000000 : ℝ)|=(1902187339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093348199/2000000000 : ℝ)|^4469 ≤ (45684649026023/100000000000000 : ℝ)^3445
        have hw : |(1093348199/2000000000 : ℝ)|=(1093348199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5189346631/10000000000 : ℝ)|^4469 ≤ (854008300791/2000000000000 : ℝ)^3445
        have hw : |(5189346631/10000000000 : ℝ)|=(5189346631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s2_1 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360775337/10000000000 : ℝ)*x 0 + (-1022610739/5000000000 : ℝ)*x 1 + (2594673369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360775337/10000000000 : ℝ)^4469 ≤ (2783701052263/6250000000000 : ℝ)^3445 := by
    have hnat : (5360775337 : ℕ)^4469*6250000000000^3445 ≤ 2783701052263^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360775337 10000000000 2783701052263 6250000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022610739/5000000000 : ℝ)^4469 ≤ (2552073394423/20000000000000 : ℝ)^3445 := by
    have hnat : (1022610739 : ℕ)^4469*20000000000000^3445 ≤ 2552073394423^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022610739 5000000000 2552073394423 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594673369/5000000000 : ℝ)^4469 ≤ (42700416181703/100000000000000 : ℝ)^3445 := by
    have hnat : (2594673369 : ℕ)^4469*100000000000000^3445 ≤ 42700416181703^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594673369 5000000000 42700416181703 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360775337/10000000000 : ℝ), (-1022610739/5000000000 : ℝ), (2594673369/5000000000 : ℝ)] ![(2783701052263/6250000000000 : ℝ), (2552073394423/20000000000000 : ℝ), (42700416181703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360775337/10000000000 : ℝ)|^4469 ≤ (2783701052263/6250000000000 : ℝ)^3445
        have hw : |(5360775337/10000000000 : ℝ)|=(5360775337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1022610739/5000000000 : ℝ)|^4469 ≤ (2552073394423/20000000000000 : ℝ)^3445
        have hw : |(-1022610739/5000000000 : ℝ)|=(1022610739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594673369/5000000000 : ℝ)|^4469 ≤ (42700416181703/100000000000000 : ℝ)^3445
        have hw : |(2594673369/5000000000 : ℝ)|=(2594673369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s2_2 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360775453/10000000000 : ℝ)*x 0 + (5189346687/10000000000 : ℝ)*x 1 + (-2045221389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360775453/10000000000 : ℝ)^4469 ≤ (890784361729/2000000000000 : ℝ)^3445 := by
    have hnat : (5360775453 : ℕ)^4469*2000000000000^3445 ≤ 890784361729^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360775453 10000000000 890784361729 2000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5189346687/10000000000 : ℝ)^4469 ≤ (667193994333/1562500000000 : ℝ)^3445 := by
    have hnat : (5189346687 : ℕ)^4469*1562500000000^3445 ≤ 667193994333^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189346687 10000000000 667193994333 1562500000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045221389/10000000000 : ℝ)^4469 ≤ (12760366251781/100000000000000 : ℝ)^3445 := by
    have hnat : (2045221389 : ℕ)^4469*100000000000000^3445 ≤ 12760366251781^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045221389 10000000000 12760366251781 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360775453/10000000000 : ℝ), (5189346687/10000000000 : ℝ), (-2045221389/10000000000 : ℝ)] ![(890784361729/2000000000000 : ℝ), (667193994333/1562500000000 : ℝ), (12760366251781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360775453/10000000000 : ℝ)|^4469 ≤ (890784361729/2000000000000 : ℝ)^3445
        have hw : |(5360775453/10000000000 : ℝ)|=(5360775453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5189346687/10000000000 : ℝ)|^4469 ≤ (667193994333/1562500000000 : ℝ)^3445
        have hw : |(5189346687/10000000000 : ℝ)|=(5189346687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045221389/10000000000 : ℝ)|^4469 ≤ (12760366251781/100000000000000 : ℝ)^3445
        have hw : |(-2045221389/10000000000 : ℝ)|=(2045221389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s2_3 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278852659/10000000000 : ℝ)*x 0 + (3979752307/10000000000 : ℝ)*x 1 + (4597261243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278852659/10000000000 : ℝ)^4469 ≤ (6649242716127/20000000000000 : ℝ)^3445 := by
    have hnat : (4278852659 : ℕ)^4469*20000000000000^3445 ≤ 6649242716127^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278852659 10000000000 6649242716127 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979752307/10000000000 : ℝ)^4469 ≤ (7565825312921/25000000000000 : ℝ)^3445 := by
    have hnat : (3979752307 : ℕ)^4469*25000000000000^3445 ≤ 7565825312921^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979752307 10000000000 7565825312921 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4597261243/10000000000 : ℝ)^4469 ≤ (9122621289807/25000000000000 : ℝ)^3445 := by
    have hnat : (4597261243 : ℕ)^4469*25000000000000^3445 ≤ 9122621289807^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4597261243 10000000000 9122621289807 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278852659/10000000000 : ℝ), (3979752307/10000000000 : ℝ), (4597261243/10000000000 : ℝ)] ![(6649242716127/20000000000000 : ℝ), (7565825312921/25000000000000 : ℝ), (9122621289807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278852659/10000000000 : ℝ)|^4469 ≤ (6649242716127/20000000000000 : ℝ)^3445
        have hw : |(4278852659/10000000000 : ℝ)|=(4278852659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979752307/10000000000 : ℝ)|^4469 ≤ (7565825312921/25000000000000 : ℝ)^3445
        have hw : |(3979752307/10000000000 : ℝ)|=(3979752307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4597261243/10000000000 : ℝ)|^4469 ≤ (9122621289807/25000000000000 : ℝ)^3445
        have hw : |(4597261243/10000000000 : ℝ)|=(4597261243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s2_4 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1902247267/10000000000 : ℝ)*x 0 + (5191130941/10000000000 : ℝ)*x 1 + (2732470063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1902247267/10000000000 : ℝ)^4469 ≤ (11615410614719/100000000000000 : ℝ)^3445 := by
    have hnat : (1902247267 : ℕ)^4469*100000000000000^3445 ≤ 11615410614719^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902247267 10000000000 11615410614719 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191130941/10000000000 : ℝ)^4469 ≤ (4271946232297/10000000000000 : ℝ)^3445 := by
    have hnat : (5191130941 : ℕ)^4469*10000000000000^3445 ≤ 4271946232297^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191130941 10000000000 4271946232297 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732470063/5000000000 : ℝ)^4469 ≤ (45665127049763/100000000000000 : ℝ)^3445 := by
    have hnat : (2732470063 : ℕ)^4469*100000000000000^3445 ≤ 45665127049763^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732470063 5000000000 45665127049763 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1902247267/10000000000 : ℝ), (5191130941/10000000000 : ℝ), (2732470063/5000000000 : ℝ)] ![(11615410614719/100000000000000 : ℝ), (4271946232297/10000000000000 : ℝ), (45665127049763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1902247267/10000000000 : ℝ)|^4469 ≤ (11615410614719/100000000000000 : ℝ)^3445
        have hw : |(-1902247267/10000000000 : ℝ)|=(1902247267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191130941/10000000000 : ℝ)|^4469 ≤ (4271946232297/10000000000000 : ℝ)^3445
        have hw : |(5191130941/10000000000 : ℝ)|=(5191130941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732470063/5000000000 : ℝ)|^4469 ≤ (45665127049763/100000000000000 : ℝ)^3445
        have hw : |(2732470063/5000000000 : ℝ)|=(2732470063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s2_5 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211529149/400000000 : ℝ)*x 0 + (-1769628263/10000000000 : ℝ)*x 1 + (5464940109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211529149/400000000 : ℝ)^4469 ≤ (5469861354099/12500000000000 : ℝ)^3445 := by
    have hnat : (211529149 : ℕ)^4469*12500000000000^3445 ≤ 5469861354099^3445*400000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211529149 400000000 5469861354099 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769628263/10000000000 : ℝ)^4469 ≤ (2115196458209/20000000000000 : ℝ)^3445 := by
    have hnat : (1769628263 : ℕ)^4469*20000000000000^3445 ≤ 2115196458209^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769628263 10000000000 2115196458209 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464940109/10000000000 : ℝ)^4469 ≤ (45665126865487/100000000000000 : ℝ)^3445 := by
    have hnat : (5464940109 : ℕ)^4469*100000000000000^3445 ≤ 45665126865487^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464940109 10000000000 45665126865487 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211529149/400000000 : ℝ), (-1769628263/10000000000 : ℝ), (5464940109/10000000000 : ℝ)] ![(5469861354099/12500000000000 : ℝ), (2115196458209/20000000000000 : ℝ), (45665126865487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211529149/400000000 : ℝ)|^4469 ≤ (5469861354099/12500000000000 : ℝ)^3445
        have hw : |(211529149/400000000 : ℝ)|=(211529149/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1769628263/10000000000 : ℝ)|^4469 ≤ (2115196458209/20000000000000 : ℝ)^3445
        have hw : |(-1769628263/10000000000 : ℝ)|=(1769628263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464940109/10000000000 : ℝ)|^4469 ≤ (45665126865487/100000000000000 : ℝ)^3445
        have hw : |(5464940109/10000000000 : ℝ)|=(5464940109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s2_6 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644114473/5000000000 : ℝ)*x 0 + (273247007/500000000 : ℝ)*x 1 + (-884813957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644114473/5000000000 : ℝ)^4469 ≤ (43758893205091/100000000000000 : ℝ)^3445 := by
    have hnat : (2644114473 : ℕ)^4469*100000000000000^3445 ≤ 43758893205091^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644114473 5000000000 43758893205091 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273247007/500000000 : ℝ)^4469 ≤ (570814090019/1250000000000 : ℝ)^3445 := by
    have hnat : (273247007 : ℕ)^4469*1250000000000^3445 ≤ 570814090019^3445*500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273247007 500000000 570814090019 1250000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884813957/5000000000 : ℝ)^4469 ≤ (1057597958531/10000000000000 : ℝ)^3445 := by
    have hnat : (884813957 : ℕ)^4469*10000000000000^3445 ≤ 1057597958531^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884813957 5000000000 1057597958531 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644114473/5000000000 : ℝ), (273247007/500000000 : ℝ), (-884813957/5000000000 : ℝ)] ![(43758893205091/100000000000000 : ℝ), (570814090019/1250000000000 : ℝ), (1057597958531/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644114473/5000000000 : ℝ)|^4469 ≤ (43758893205091/100000000000000 : ℝ)^3445
        have hw : |(2644114473/5000000000 : ℝ)|=(2644114473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273247007/500000000 : ℝ)|^4469 ≤ (570814090019/1250000000000 : ℝ)^3445
        have hw : |(273247007/500000000 : ℝ)|=(273247007/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-884813957/5000000000 : ℝ)|^4469 ≤ (1057597958531/10000000000000 : ℝ)^3445
        have hw : |(-884813957/5000000000 : ℝ)|=(884813957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s2_7 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278985789/10000000000 : ℝ)*x 0 + (574161089/1250000000 : ℝ)*x 1 + (39837617/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278985789/10000000000 : ℝ)^4469 ≤ (33247555461399/100000000000000 : ℝ)^3445 := by
    have hnat : (4278985789 : ℕ)^4469*100000000000000^3445 ≤ 33247555461399^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278985789 10000000000 33247555461399 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574161089/1250000000 : ℝ)^4469 ≤ (7289917224333/20000000000000 : ℝ)^3445 := by
    have hnat : (574161089 : ℕ)^4469*20000000000000^3445 ≤ 7289917224333^3445*1250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574161089 1250000000 7289917224333 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39837617/100000000 : ℝ)^4469 ≤ (473482162563/1562500000000 : ℝ)^3445 := by
    have hnat : (39837617 : ℕ)^4469*1562500000000^3445 ≤ 473482162563^3445*100000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39837617 100000000 473482162563 1562500000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278985789/10000000000 : ℝ), (574161089/1250000000 : ℝ), (39837617/100000000 : ℝ)] ![(33247555461399/100000000000000 : ℝ), (7289917224333/20000000000000 : ℝ), (473482162563/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278985789/10000000000 : ℝ)|^4469 ≤ (33247555461399/100000000000000 : ℝ)^3445
        have hw : |(4278985789/10000000000 : ℝ)|=(4278985789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574161089/1250000000 : ℝ)|^4469 ≤ (7289917224333/20000000000000 : ℝ)^3445
        have hw : |(574161089/1250000000 : ℝ)|=(574161089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39837617/100000000 : ℝ)|^4469 ≤ (473482162563/1562500000000 : ℝ)^3445
        have hw : |(39837617/100000000 : ℝ)|=(39837617/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1486_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9313/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2559/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2013/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9313/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9313/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9313/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9313/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9313/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9313/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7993/100000 : ℝ) ^ (4467/1024 : ℝ) ≤ (817063627653507/50000000000000000000 : ℝ) := by
    have hpowers : (7993/100000 : ℝ)^4467 ≤ (817063627653507/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7993 : ℕ)^4467*50000000000000000000^1024 ≤ 817063627653507^1024*100000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7993 100000 817063627653507 50000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7993/100000 : ℝ)) (X := (817063627653507/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9313/50000 : ℝ) ^ (4467/1024 : ℝ) ≤ (65469542145797037/100000000000000000000 : ℝ) := by
    have hpowers : (9313/50000 : ℝ)^4467 ≤ (65469542145797037/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9313 : ℕ)^4467*100000000000000000000^1024 ≤ 65469542145797037^1024*50000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9313 50000 65469542145797037 100000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9313/50000 : ℝ)) (X := (65469542145797037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000817063627653507/25000000000000000000 : ℝ) ≤ (500003745970973/500000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (25000817063627653507/25000000000000000000 : ℝ)^1024 ≤ (500003745970973/500000000000000 : ℝ)^4467 := by
      have hnat : (25000817063627653507 : ℕ)^1024*500000000000000^4467 ≤ 500003745970973^4467*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000817063627653507 25000000000000000000 500003745970973 500000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500003745970973/500000000000000 : ℝ)) (X := (25000817063627653507/25000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100067103669401104051/100000000000000000000 : ℝ) ≤ (2500384466054733/2500000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (100067103669401104051/100000000000000000000 : ℝ)^1024 ≤ (2500384466054733/2500000000000000 : ℝ)^4467 := by
      have hnat : (100067103669401104051 : ℕ)^1024*2500000000000000^4467 ≤ 2500384466054733^4467*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100067103669401104051 100000000000000000000 2500384466054733 2500000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500384466054733/2500000000000000 : ℝ)) (X := (100067103669401104051/100000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50065469542145797037/50000000000000000000 : ℝ) ≤ (2500750202254601/2500000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (50065469542145797037/50000000000000000000 : ℝ)^1024 ≤ (2500750202254601/2500000000000000 : ℝ)^4467 := by
      have hnat : (50065469542145797037 : ℕ)^1024*2500000000000000^4467 ≤ 2500750202254601^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065469542145797037 50000000000000000000 2500750202254601 2500000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500750202254601/2500000000000000 : ℝ)) (X := (50065469542145797037/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(817063627653507/50000000000000000000 : ℝ) ≤ ((26576852495655689697/26582500000000000000 : ℝ)+2*(91434049967/66456250000000 : ℝ)*(7993/100000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (26576852495655689697/26582500000000000000 : ℝ)+2*(91434049967/66456250000000 : ℝ)*(7993/100000 : ℝ)=(500003745970973/500000000000000 : ℝ) by norm_num, show 1+2*(817063627653507/50000000000000000000 : ℝ)=(25000817063627653507/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(65469542145797037/100000000000000000000 : ℝ)+(817063627653507/50000000000000000000 : ℝ) ≤ ((26576852495655689697/26582500000000000000 : ℝ)+(91434049967/66456250000000 : ℝ)*((9313/50000 : ℝ)+(7993/100000 : ℝ)))^(4467/1024 : ℝ) := by
    rw [show (26576852495655689697/26582500000000000000 : ℝ)+(91434049967/66456250000000 : ℝ)*((9313/50000 : ℝ)+(7993/100000 : ℝ))=(2500384466054733/2500000000000000 : ℝ) by norm_num, show 1+(65469542145797037/100000000000000000000 : ℝ)+(817063627653507/50000000000000000000 : ℝ)=(100067103669401104051/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(65469542145797037/100000000000000000000 : ℝ) ≤ ((26576852495655689697/26582500000000000000 : ℝ)+2*(91434049967/66456250000000 : ℝ)*(9313/50000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (26576852495655689697/26582500000000000000 : ℝ)+2*(91434049967/66456250000000 : ℝ)*(9313/50000 : ℝ)=(2500750202254601/2500000000000000 : ℝ) by norm_num, show 1+2*(65469542145797037/100000000000000000000 : ℝ)=(50065469542145797037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26576852495655689697/26582500000000000000 : ℝ)*(X 1 0+X 2 0)+(91434049967/66456250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (7993/100000 : ℝ)) (hi := (9313/50000 : ℝ)) (c := (26576852495655689697/26582500000000000000 : ℝ)) (alpha := (91434049967/66456250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26576852495655689697/26582500000000000000 : ℝ)*(X 0 1+X 2 1)+(91434049967/66456250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (7993/100000 : ℝ)) (hi := (9313/50000 : ℝ)) (c := (26576852495655689697/26582500000000000000 : ℝ)) (alpha := (91434049967/66456250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26576852495655689697/26582500000000000000 : ℝ)*(X 0 2+X 1 2)+(91434049967/66456250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (7993/100000 : ℝ)) (hi := (9313/50000 : ℝ)) (c := (26576852495655689697/26582500000000000000 : ℝ)) (alpha := (91434049967/66456250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1902187339/10000000000 : ℝ)*X 0 0+(1093348199/2000000000 : ℝ)*X 0 1+(5189346631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360775337/10000000000 : ℝ)*X 1 0+(-1022610739/5000000000 : ℝ)*X 1 1+(2594673369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360775453/10000000000 : ℝ)*X 2 0+(5189346687/10000000000 : ℝ)*X 2 1+(-2045221389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4278852659/10000000000 : ℝ)*X 0 0+(3979752307/10000000000 : ℝ)*X 0 1+(4597261243/10000000000 : ℝ)*X 0 2+(4278852659/10000000000 : ℝ)*X 1 0+(3979752307/10000000000 : ℝ)*X 1 1+(4597261243/10000000000 : ℝ)*X 1 2+(4278852659/10000000000 : ℝ)*X 2 0+(3979752307/10000000000 : ℝ)*X 2 1+(4597261243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1902247267/10000000000 : ℝ)*X 0 0+(5191130941/10000000000 : ℝ)*X 0 1+(2732470063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211529149/400000000 : ℝ)*X 1 0+(-1769628263/10000000000 : ℝ)*X 1 1+(5464940109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644114473/5000000000 : ℝ)*X 2 0+(273247007/500000000 : ℝ)*X 2 1+(-884813957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278985789/10000000000 : ℝ)*X 0 0+(574161089/1250000000 : ℝ)*X 0 1+(39837617/100000000 : ℝ)*X 0 2+(4278985789/10000000000 : ℝ)*X 1 0+(574161089/1250000000 : ℝ)*X 1 1+(39837617/100000000 : ℝ)*X 1 2+(4278985789/10000000000 : ℝ)*X 2 0+(574161089/1250000000 : ℝ)*X 2 1+(39837617/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45077680762321113715131/13291250000000000000000000000 : ℝ) := by norm_num
    linear_combination (195883141/50000000000000 : ℝ)*(base19) + (95201459/25000000000000 : ℝ)*(base23) + (2980843/6250000000000 : ℝ)*(lower2) + (62417929/100000000000000 : ℝ)*(upper3) + (4668929/6250000000000 : ℝ)*(upper5) + (653050259684237/25000000000000 : ℝ)*(major0) + (653050259684237/25000000000000 : ℝ)*(major1) + (653050259684237/25000000000000 : ℝ)*(major2) + (1802490255564841/50000000000000 : ℝ)*(sp0) + (450623261584457/12500000000000 : ℝ)*(sp1) + (1802493051818051/50000000000000 : ℝ)*(sp2) + (1619412460050801/100000000000000 : ℝ)*(sp3) + (23333251/390625000000 : ℝ)*(sp4) + (3019930129/100000000000000 : ℝ)*(sp7) + (1619415479980929/100000000000000 : ℝ)*(f.failure) + (1802493242220969/50000000000000 : ℝ)*(f.sum) + (52238275941697/26582500000000000000000000000 : ℝ)*base66 + (150578976862679473/94937500000000000000000000000000 : ℝ)*base68 + (108612521656070527/94937500000000000000000000000000 : ℝ)*base69 + (76152234921758027/94937500000000000000000000000000 : ℝ)*base71 + (90953826630399/53165000000000000000000000000 : ℝ)*base74 + (358748132160804473/94937500000000000000000000000000 : ℝ)*base76 + (396935781450133027/94937500000000000000000000000000 : ℝ)*base77 + (705058368498429473/94937500000000000000000000000000 : ℝ)*base80 + (1066010832269/53165000000000000000000000000 : ℝ)*base82 + (131068709/10000000000000000000000 : ℝ)*base90 + (131068709/10000000000000000000000 : ℝ)*base92 + (131068709/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6423892453023450180525419223/664562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1282658199/100000000000000 : ℝ)*(base19) + (395106893/25000000000000 : ℝ)*(base23) + (166870367/100000000000000 : ℝ)*(upper3) + (10637419/25000000000000 : ℝ)*(lower4) + (244584793/100000000000000 : ℝ)*(upper5) + (1323199230460349/50000000000000 : ℝ)*(major0) + (1323199230460349/50000000000000 : ℝ)*(major1) + (1323199230460349/50000000000000 : ℝ)*(major2) + (3706675707/25000000000000 : ℝ)*(sp1) + (19541551031/100000000000000 : ℝ)*(sp2) + (3652180670664041/100000000000000 : ℝ)*(sp4) + (1826082280651507/50000000000000 : ℝ)*(sp5) + (1826079774342719/50000000000000 : ℝ)*(sp6) + (820307964482869/50000000000000 : ℝ)*(sp7) + (820307964482869/50000000000000 : ℝ)*(f.failure) + (3652180670664041/100000000000000 : ℝ)*(f.sum) + (1328215746181/53165000000000000000000000000 : ℝ)*base65 + (947531868267414179/189875000000000000000000000000000 : ℝ)*base67 + (2827161127473539179/189875000000000000000000000000000 : ℝ)*base69 + (769583784556289179/189875000000000000000000000000000 : ℝ)*base71 + (15091662589053/26582500000000000000000000000 : ℝ)*base73 + (3290047056216539179/189875000000000000000000000000000 : ℝ)*base75 + (1039680933131914179/189875000000000000000000000000000 : ℝ)*base77 + (2529233713056914179/189875000000000000000000000000000 : ℝ)*base79 + (297571843019971/53165000000000000000000000000 : ℝ)*base81 + (73521449/5000000000000000000000 : ℝ)*base90 + (73521449/5000000000000000000000 : ℝ)*base92 + (73521449/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1486_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9313/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1486_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1486_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1486_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1486_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1486_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1486_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

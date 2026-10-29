-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1535_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:10.321881+00:00
-- url     : https://prove2.me/submissions/d195a37a-96d8-455a-81c3-7e3261f113f7

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
theorem support_rectangle_w1535_s3_0 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-229273433/1250000000 : ℝ)*x 0 + (1358193023/2500000000 : ℝ)*x 1 + (1043290411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (229273433/1250000000 : ℝ)^4567 ≤ (140434493811/1250000000000 : ℝ)^3543 := by
    have hnat : (229273433 : ℕ)^4567*1250000000000^3543 ≤ 140434493811^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229273433 1250000000 140434493811 1250000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358193023/2500000000 : ℝ)^4567 ≤ (9108927221231/20000000000000 : ℝ)^3543 := by
    have hnat : (1358193023 : ℕ)^4567*20000000000000^3543 ≤ 9108927221231^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358193023 2500000000 9108927221231 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043290411/2000000000 : ℝ)^4567 ≤ (43220604369561/100000000000000 : ℝ)^3543 := by
    have hnat : (1043290411 : ℕ)^4567*100000000000000^3543 ≤ 43220604369561^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043290411 2000000000 43220604369561 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-229273433/1250000000 : ℝ), (1358193023/2500000000 : ℝ), (1043290411/2000000000 : ℝ)] ![(140434493811/1250000000000 : ℝ), (9108927221231/20000000000000 : ℝ), (43220604369561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-229273433/1250000000 : ℝ)|^4567 ≤ (140434493811/1250000000000 : ℝ)^3543
        have hw : |(-229273433/1250000000 : ℝ)|=(229273433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358193023/2500000000 : ℝ)|^4567 ≤ (9108927221231/20000000000000 : ℝ)^3543
        have hw : |(1358193023/2500000000 : ℝ)|=(1358193023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043290411/2000000000 : ℝ)|^4567 ≤ (43220604369561/100000000000000 : ℝ)^3543
        have hw : |(1043290411/2000000000 : ℝ)|=(1043290411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s3_1 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350944099/10000000000 : ℝ)*x 0 + (-972491931/5000000000 : ℝ)*x 1 + (5216452063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350944099/10000000000 : ℝ)^4567 ≤ (5582789090603/12500000000000 : ℝ)^3543 := by
    have hnat : (5350944099 : ℕ)^4567*12500000000000^3543 ≤ 5582789090603^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350944099 10000000000 5582789090603 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972491931/5000000000 : ℝ)^4567 ≤ (1211708280331/10000000000000 : ℝ)^3543 := by
    have hnat : (972491931 : ℕ)^4567*10000000000000^3543 ≤ 1211708280331^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972491931 5000000000 1211708280331 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216452063/10000000000 : ℝ)^4567 ≤ (21610302227501/50000000000000 : ℝ)^3543 := by
    have hnat : (5216452063 : ℕ)^4567*50000000000000^3543 ≤ 21610302227501^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216452063 10000000000 21610302227501 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350944099/10000000000 : ℝ), (-972491931/5000000000 : ℝ), (5216452063/10000000000 : ℝ)] ![(5582789090603/12500000000000 : ℝ), (1211708280331/10000000000000 : ℝ), (21610302227501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350944099/10000000000 : ℝ)|^4567 ≤ (5582789090603/12500000000000 : ℝ)^3543
        have hw : |(5350944099/10000000000 : ℝ)|=(5350944099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-972491931/5000000000 : ℝ)|^4567 ≤ (1211708280331/10000000000000 : ℝ)^3543
        have hw : |(-972491931/5000000000 : ℝ)|=(972491931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216452063/10000000000 : ℝ)|^4567 ≤ (21610302227501/50000000000000 : ℝ)^3543
        have hw : |(5216452063/10000000000 : ℝ)|=(5216452063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s3_2 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350944087/10000000000 : ℝ)*x 0 + (5216452077/10000000000 : ℝ)*x 1 + (-97249193/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350944087/10000000000 : ℝ)^4567 ≤ (11165578148929/25000000000000 : ℝ)^3543 := by
    have hnat : (5350944087 : ℕ)^4567*25000000000000^3543 ≤ 11165578148929^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350944087 10000000000 11165578148929 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216452077/10000000000 : ℝ)^4567 ≤ (43220604604523/100000000000000 : ℝ)^3543 := by
    have hnat : (5216452077 : ℕ)^4567*100000000000000^3543 ≤ 43220604604523^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216452077 10000000000 43220604604523 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97249193/500000000 : ℝ)^4567 ≤ (12117082787249/100000000000000 : ℝ)^3543 := by
    have hnat : (97249193 : ℕ)^4567*100000000000000^3543 ≤ 12117082787249^3543*500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97249193 500000000 12117082787249 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350944087/10000000000 : ℝ), (5216452077/10000000000 : ℝ), (-97249193/500000000 : ℝ)] ![(11165578148929/25000000000000 : ℝ), (43220604604523/100000000000000 : ℝ), (12117082787249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350944087/10000000000 : ℝ)|^4567 ≤ (11165578148929/25000000000000 : ℝ)^3543
        have hw : |(5350944087/10000000000 : ℝ)|=(5350944087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216452077/10000000000 : ℝ)|^4567 ≤ (43220604604523/100000000000000 : ℝ)^3543
        have hw : |(5216452077/10000000000 : ℝ)|=(5216452077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97249193/500000000 : ℝ)|^4567 ≤ (12117082787249/100000000000000 : ℝ)^3543
        have hw : |(-97249193/500000000 : ℝ)|=(97249193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s3_3 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4258941853/10000000000 : ℝ)*x 0 + (4015774897/10000000000 : ℝ)*x 1 + (4514259311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258941853/10000000000 : ℝ)^4567 ≤ (16639193474521/50000000000000 : ℝ)^3543 := by
    have hnat : (4258941853 : ℕ)^4567*50000000000000^3543 ≤ 16639193474521^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258941853 10000000000 16639193474521 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4015774897/10000000000 : ℝ)^4567 ≤ (15424835678931/50000000000000 : ℝ)^3543 := by
    have hnat : (4015774897 : ℕ)^4567*50000000000000^3543 ≤ 15424835678931^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015774897 10000000000 15424835678931 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514259311/10000000000 : ℝ)^4567 ≤ (8967985418983/25000000000000 : ℝ)^3543 := by
    have hnat : (4514259311 : ℕ)^4567*25000000000000^3543 ≤ 8967985418983^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514259311 10000000000 8967985418983 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258941853/10000000000 : ℝ), (4015774897/10000000000 : ℝ), (4514259311/10000000000 : ℝ)] ![(16639193474521/50000000000000 : ℝ), (15424835678931/50000000000000 : ℝ), (8967985418983/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258941853/10000000000 : ℝ)|^4567 ≤ (16639193474521/50000000000000 : ℝ)^3543
        have hw : |(4258941853/10000000000 : ℝ)|=(4258941853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4015774897/10000000000 : ℝ)|^4567 ≤ (15424835678931/50000000000000 : ℝ)^3543
        have hw : |(4015774897/10000000000 : ℝ)|=(4015774897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514259311/10000000000 : ℝ)|^4567 ≤ (8967985418983/25000000000000 : ℝ)^3543
        have hw : |(4514259311/10000000000 : ℝ)|=(4514259311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s3_4 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-114638591/625000000 : ℝ)*x 0 + (5217595769/10000000000 : ℝ)*x 1 + (5431619747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114638591/625000000 : ℝ)^4567 ≤ (11234996307429/100000000000000 : ℝ)^3543 := by
    have hnat : (114638591 : ℕ)^4567*100000000000000^3543 ≤ 11234996307429^3543*625000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114638591 625000000 11234996307429 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217595769/10000000000 : ℝ)^4567 ≤ (10808204935207/25000000000000 : ℝ)^3543 := by
    have hnat : (5217595769 : ℕ)^4567*25000000000000^3543 ≤ 10808204935207^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217595769 10000000000 10808204935207 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431619747/10000000000 : ℝ)^4567 ≤ (910643678851/2000000000000 : ℝ)^3543 := by
    have hnat : (5431619747 : ℕ)^4567*2000000000000^3543 ≤ 910643678851^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431619747 10000000000 910643678851 2000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114638591/625000000 : ℝ), (5217595769/10000000000 : ℝ), (5431619747/10000000000 : ℝ)] ![(11234996307429/100000000000000 : ℝ), (10808204935207/25000000000000 : ℝ), (910643678851/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114638591/625000000 : ℝ)|^4567 ≤ (11234996307429/100000000000000 : ℝ)^3543
        have hw : |(-114638591/625000000 : ℝ)|=(114638591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217595769/10000000000 : ℝ)|^4567 ≤ (10808204935207/25000000000000 : ℝ)^3543
        have hw : |(5217595769/10000000000 : ℝ)|=(5217595769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431619747/10000000000 : ℝ)|^4567 ≤ (910643678851/2000000000000 : ℝ)^3543
        have hw : |(5431619747/10000000000 : ℝ)|=(5431619747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s3_5 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058793533/2000000000 : ℝ)*x 0 + (-1729816169/10000000000 : ℝ)*x 1 + (5431619737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058793533/2000000000 : ℝ)^4567 ≤ (8810050137737/20000000000000 : ℝ)^3543 := by
    have hnat : (1058793533 : ℕ)^4567*20000000000000^3543 ≤ 8810050137737^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058793533 2000000000 8810050137737 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1729816169/10000000000 : ℝ)^4567 ≤ (2604391365653/25000000000000 : ℝ)^3543 := by
    have hnat : (1729816169 : ℕ)^4567*25000000000000^3543 ≤ 2604391365653^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729816169 10000000000 2604391365653 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431619737/10000000000 : ℝ)^4567 ≤ (22766091917247/50000000000000 : ℝ)^3543 := by
    have hnat : (5431619737 : ℕ)^4567*50000000000000^3543 ≤ 22766091917247^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431619737 10000000000 22766091917247 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058793533/2000000000 : ℝ), (-1729816169/10000000000 : ℝ), (5431619737/10000000000 : ℝ)] ![(8810050137737/20000000000000 : ℝ), (2604391365653/25000000000000 : ℝ), (22766091917247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058793533/2000000000 : ℝ)|^4567 ≤ (8810050137737/20000000000000 : ℝ)^3543
        have hw : |(1058793533/2000000000 : ℝ)|=(1058793533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1729816169/10000000000 : ℝ)|^4567 ≤ (2604391365653/25000000000000 : ℝ)^3543
        have hw : |(-1729816169/10000000000 : ℝ)|=(1729816169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431619737/10000000000 : ℝ)|^4567 ≤ (22766091917247/50000000000000 : ℝ)^3543
        have hw : |(5431619737/10000000000 : ℝ)|=(5431619737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s3_6 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661745957/1250000000 : ℝ)*x 0 + (2715809873/5000000000 : ℝ)*x 1 + (-1729816169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661745957/1250000000 : ℝ)^4567 ≤ (22025125296077/50000000000000 : ℝ)^3543 := by
    have hnat : (661745957 : ℕ)^4567*50000000000000^3543 ≤ 22025125296077^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661745957 1250000000 22025125296077 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715809873/5000000000 : ℝ)^4567 ≤ (1422880747867/3125000000000 : ℝ)^3543 := by
    have hnat : (2715809873 : ℕ)^4567*3125000000000^3543 ≤ 1422880747867^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715809873 5000000000 1422880747867 3125000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1729816169/10000000000 : ℝ)^4567 ≤ (2604391365653/25000000000000 : ℝ)^3543 := by
    have hnat : (1729816169 : ℕ)^4567*25000000000000^3543 ≤ 2604391365653^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729816169 10000000000 2604391365653 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661745957/1250000000 : ℝ), (2715809873/5000000000 : ℝ), (-1729816169/10000000000 : ℝ)] ![(22025125296077/50000000000000 : ℝ), (1422880747867/3125000000000 : ℝ), (2604391365653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661745957/1250000000 : ℝ)|^4567 ≤ (22025125296077/50000000000000 : ℝ)^3543
        have hw : |(661745957/1250000000 : ℝ)|=(661745957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715809873/5000000000 : ℝ)|^4567 ≤ (1422880747867/3125000000000 : ℝ)^3543
        have hw : |(2715809873/5000000000 : ℝ)|=(2715809873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1729816169/10000000000 : ℝ)|^4567 ≤ (2604391365653/25000000000000 : ℝ)^3543
        have hw : |(-1729816169/10000000000 : ℝ)|=(1729816169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s3_7 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259010959/10000000000 : ℝ)*x 0 + (2255811893/5000000000 : ℝ)*x 1 + (4018430301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259010959/10000000000 : ℝ)^4567 ≤ (8319770748459/25000000000000 : ℝ)^3543 := by
    have hnat : (4259010959 : ℕ)^4567*25000000000000^3543 ≤ 8319770748459^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259010959 10000000000 8319770748459 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255811893/5000000000 : ℝ)^4567 ≤ (35844948204817/100000000000000 : ℝ)^3543 := by
    have hnat : (2255811893 : ℕ)^4567*100000000000000^3543 ≤ 35844948204817^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255811893 5000000000 35844948204817 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018430301/10000000000 : ℝ)^4567 ≤ (3859496097189/12500000000000 : ℝ)^3543 := by
    have hnat : (4018430301 : ℕ)^4567*12500000000000^3543 ≤ 3859496097189^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018430301 10000000000 3859496097189 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259010959/10000000000 : ℝ), (2255811893/5000000000 : ℝ), (4018430301/10000000000 : ℝ)] ![(8319770748459/25000000000000 : ℝ), (35844948204817/100000000000000 : ℝ), (3859496097189/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259010959/10000000000 : ℝ)|^4567 ≤ (8319770748459/25000000000000 : ℝ)^3543
        have hw : |(4259010959/10000000000 : ℝ)|=(4259010959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255811893/5000000000 : ℝ)|^4567 ≤ (35844948204817/100000000000000 : ℝ)^3543
        have hw : |(2255811893/5000000000 : ℝ)|=(2255811893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018430301/10000000000 : ℝ)|^4567 ≤ (3859496097189/12500000000000 : ℝ)^3543
        have hw : |(4018430301/10000000000 : ℝ)|=(4018430301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1535_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3183/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10953/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15537/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3183/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2121/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3183/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2121/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3183/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2121/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3183/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2121/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3183/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2121/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3183/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2121/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2121/20000 : ℝ) ^ (4565/1024 : ℝ) ≤ (4526046029501337/100000000000000000000 : ℝ) := by
    have hpowers : (2121/20000 : ℝ)^4565 ≤ (4526046029501337/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2121 : ℕ)^4565*100000000000000000000^1024 ≤ 4526046029501337^1024*20000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2121 20000 4526046029501337 100000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2121/20000 : ℝ)) (X := (4526046029501337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3183/20000 : ℝ) ^ (4565/1024 : ℝ) ≤ (172793656854597/625000000000000000 : ℝ) := by
    have hpowers : (3183/20000 : ℝ)^4565 ≤ (172793656854597/625000000000000000 : ℝ)^1024 := by
      have hnat : (3183 : ℕ)^4565*625000000000000000^1024 ≤ 172793656854597^1024*20000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3183 20000 172793656854597 625000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3183/20000 : ℝ)) (X := (172793656854597/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004526046029501337/50000000000000000000 : ℝ) ≤ (10000203045276217/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50004526046029501337/50000000000000000000 : ℝ)^1024 ≤ (10000203045276217/10000000000000000 : ℝ)^4565 := by
      have hnat : (50004526046029501337 : ℕ)^1024*10000000000000000^4565 ≤ 10000203045276217^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004526046029501337 50000000000000000000 10000203045276217 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000203045276217/10000000000000000 : ℝ)) (X := (50004526046029501337/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032173031126236857/100000000000000000000 : ℝ) ≤ (2000144320147801/2000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (100032173031126236857/100000000000000000000 : ℝ)^1024 ≤ (2000144320147801/2000000000000000 : ℝ)^4565 := by
      have hnat : (100032173031126236857 : ℕ)^1024*2000000000000000^4565 ≤ 2000144320147801^4565*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032173031126236857 100000000000000000000 2000144320147801 2000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144320147801/2000000000000000 : ℝ)) (X := (100032173031126236857/100000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312672793656854597/312500000000000000 : ℝ) ≤ (10001240156201793/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (312672793656854597/312500000000000000 : ℝ)^1024 ≤ (10001240156201793/10000000000000000 : ℝ)^4565 := by
      have hnat : (312672793656854597 : ℕ)^1024*10000000000000000^4565 ≤ 10001240156201793^4565*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312672793656854597 312500000000000000 10001240156201793 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001240156201793/10000000000000000 : ℝ)) (X := (312672793656854597/312500000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4526046029501337/100000000000000000000 : ℝ) ≤ ((1769669320301699293/1770000000000000000 : ℝ)+2*(129638865697/132750000000000 : ℝ)*(2121/20000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (1769669320301699293/1770000000000000000 : ℝ)+2*(129638865697/132750000000000 : ℝ)*(2121/20000 : ℝ)=(10000203045276217/10000000000000000 : ℝ) by norm_num, show 1+2*(4526046029501337/100000000000000000000 : ℝ)=(50004526046029501337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(172793656854597/625000000000000000 : ℝ)+(4526046029501337/100000000000000000000 : ℝ) ≤ ((1769669320301699293/1770000000000000000 : ℝ)+(129638865697/132750000000000 : ℝ)*((3183/20000 : ℝ)+(2121/20000 : ℝ)))^(4565/1024 : ℝ) := by
    rw [show (1769669320301699293/1770000000000000000 : ℝ)+(129638865697/132750000000000 : ℝ)*((3183/20000 : ℝ)+(2121/20000 : ℝ))=(2000144320147801/2000000000000000 : ℝ) by norm_num, show 1+(172793656854597/625000000000000000 : ℝ)+(4526046029501337/100000000000000000000 : ℝ)=(100032173031126236857/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(172793656854597/625000000000000000 : ℝ) ≤ ((1769669320301699293/1770000000000000000 : ℝ)+2*(129638865697/132750000000000 : ℝ)*(3183/20000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (1769669320301699293/1770000000000000000 : ℝ)+2*(129638865697/132750000000000 : ℝ)*(3183/20000 : ℝ)=(10001240156201793/10000000000000000 : ℝ) by norm_num, show 1+2*(172793656854597/625000000000000000 : ℝ)=(312672793656854597/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1769669320301699293/1770000000000000000 : ℝ)*(X 1 0+X 2 0)+(129638865697/132750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (3183/20000 : ℝ)) (c := (1769669320301699293/1770000000000000000 : ℝ)) (alpha := (129638865697/132750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1769669320301699293/1770000000000000000 : ℝ)*(X 0 1+X 2 1)+(129638865697/132750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (3183/20000 : ℝ)) (c := (1769669320301699293/1770000000000000000 : ℝ)) (alpha := (129638865697/132750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1769669320301699293/1770000000000000000 : ℝ)*(X 0 2+X 1 2)+(129638865697/132750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (3183/20000 : ℝ)) (c := (1769669320301699293/1770000000000000000 : ℝ)) (alpha := (129638865697/132750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-229273433/1250000000 : ℝ)*X 0 0+(1358193023/2500000000 : ℝ)*X 0 1+(1043290411/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350944099/10000000000 : ℝ)*X 1 0+(-972491931/5000000000 : ℝ)*X 1 1+(5216452063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350944087/10000000000 : ℝ)*X 2 0+(5216452077/10000000000 : ℝ)*X 2 1+(-97249193/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4258941853/10000000000 : ℝ)*X 0 0+(4015774897/10000000000 : ℝ)*X 0 1+(4514259311/10000000000 : ℝ)*X 0 2+(4258941853/10000000000 : ℝ)*X 1 0+(4015774897/10000000000 : ℝ)*X 1 1+(4514259311/10000000000 : ℝ)*X 1 2+(4258941853/10000000000 : ℝ)*X 2 0+(4015774897/10000000000 : ℝ)*X 2 1+(4514259311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-114638591/625000000 : ℝ)*X 0 0+(5217595769/10000000000 : ℝ)*X 0 1+(5431619747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058793533/2000000000 : ℝ)*X 1 0+(-1729816169/10000000000 : ℝ)*X 1 1+(5431619737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661745957/1250000000 : ℝ)*X 2 0+(2715809873/5000000000 : ℝ)*X 2 1+(-1729816169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4259010959/10000000000 : ℝ)*X 0 0+(2255811893/5000000000 : ℝ)*X 0 1+(4018430301/10000000000 : ℝ)*X 0 2+(4259010959/10000000000 : ℝ)*X 1 0+(2255811893/5000000000 : ℝ)*X 1 1+(4018430301/10000000000 : ℝ)*X 1 2+(4259010959/10000000000 : ℝ)*X 2 0+(2255811893/5000000000 : ℝ)*X 2 1+(4018430301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110147885109652829825284843/11062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1729964449/100000000000000 : ℝ)*(base19) + (1605700343/100000000000000 : ℝ)*(base23) + (60945627/100000000000000 : ℝ)*(lower2) + (248905447/100000000000000 : ℝ)*(upper3) + (165951673/100000000000000 : ℝ)*(upper5) + (828617569859617/25000000000000 : ℝ)*(major0) + (828617569859617/25000000000000 : ℝ)*(major1) + (828617569859617/25000000000000 : ℝ)*(major2) + (92456168743789/2000000000000 : ℝ)*(sp0) + (288927110700887/6250000000000 : ℝ)*(sp1) + (2311416947739149/50000000000000 : ℝ)*(sp2) + (80243683393889/4000000000000 : ℝ)*(sp3) + (27063989191/100000000000000 : ℝ)*(sp4) + (3160238841/25000000000000 : ℝ)*(sp7) + (200610472580259/10000000000000 : ℝ)*(f.failure) + (4622835501178641/100000000000000 : ℝ)*(f.sum) + (36713422495517/13275000000000000000000000000 : ℝ)*base65 + (606826432365587657/132750000000000000000000000000000 : ℝ)*base68 + (1221108440240087657/132750000000000000000000000000000 : ℝ)*base70 + (216771594448337657/132750000000000000000000000000000 : ℝ)*base72 + (74178654247517/13275000000000000000000000000 : ℝ)*base73 + (499785252299837657/132750000000000000000000000000000 : ℝ)*base76 + (1275117108812837657/132750000000000000000000000000000 : ℝ)*base78 + (135197923590162343/132750000000000000000000000000000 : ℝ)*base79 + (14067505026167/13275000000000000000000000000 : ℝ)*base81 + (2134819/200000000000000000000 : ℝ)*base89 + (2134819/200000000000000000000 : ℝ)*base91 + (2134819/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44896376400212298529121/4425000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1675142837/100000000000000 : ℝ)*(base19) + (225334851/12500000000000 : ℝ)*(base23) + (215915767/100000000000000 : ℝ)*(upper3) + (15165191/25000000000000 : ℝ)*(lower4) + (104717501/50000000000000 : ℝ)*(upper5) + (52343549034569/1562500000000 : ℝ)*(major0) + (52343549034569/1562500000000 : ℝ)*(major1) + (52343549034569/1562500000000 : ℝ)*(major2) + (25314248993/100000000000000 : ℝ)*(sp1) + (2725566717/10000000000000 : ℝ)*(sp2) + (4672372402303819/100000000000000 : ℝ)*(sp4) + (467234541291199/10000000000000 : ℝ)*(sp5) + (4672343343957841/100000000000000 : ℝ)*(sp6) + (2027601535918549/100000000000000 : ℝ)*(sp7) + (2027601535918549/100000000000000 : ℝ)*(f.failure) + (4672372402303819/100000000000000 : ℝ)*(f.sum) + (56660224920521/13275000000000000000000000000 : ℝ)*base66 + (2649525561023153/1037109375000000000000000000000 : ℝ)*base68 + (98535843344205401/8296875000000000000000000000000 : ℝ)*base69 + (45006375769638349/8296875000000000000000000000000 : ℝ)*base72 + (8712612076727/6637500000000000000000000000 : ℝ)*base73 + (9057735293017901/8296875000000000000000000000000 : ℝ)*base75 + (2067510927561931/2074218750000000000000000000000 : ℝ)*base78 + (94400847213142901/8296875000000000000000000000000 : ℝ)*base79 + (509713932811/207421875000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2106709/2000000000000000000000 : ℝ)*base89 + (2106709/2000000000000000000000 : ℝ)*base91 + (2106709/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1535_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3183/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10953/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15537/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1535_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1535_s4_0 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-229315509/1250000000 : ℝ)*x 0 + (2715270379/5000000000 : ℝ)*x 1 + (104369213/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (229315509/1250000000 : ℝ)^4567 ≤ (5618708632771/50000000000000 : ℝ)^3543 := by
    have hnat : (229315509 : ℕ)^4567*50000000000000^3543 ≤ 5618708632771^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229315509 1250000000 5618708632771 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715270379/5000000000 : ℝ)^4567 ≤ (1138013128779/2500000000000 : ℝ)^3543 := by
    have hnat : (2715270379 : ℕ)^4567*2500000000000^3543 ≤ 1138013128779^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715270379 5000000000 1138013128779 2500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104369213/200000000 : ℝ)^4567 ≤ (8648411513253/20000000000000 : ℝ)^3543 := by
    have hnat : (104369213 : ℕ)^4567*20000000000000^3543 ≤ 8648411513253^3543*200000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104369213 200000000 8648411513253 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-229315509/1250000000 : ℝ), (2715270379/5000000000 : ℝ), (104369213/200000000 : ℝ)] ![(5618708632771/50000000000000 : ℝ), (1138013128779/2500000000000 : ℝ), (8648411513253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-229315509/1250000000 : ℝ)|^4567 ≤ (5618708632771/50000000000000 : ℝ)^3543
        have hw : |(-229315509/1250000000 : ℝ)|=(229315509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715270379/5000000000 : ℝ)|^4567 ≤ (1138013128779/2500000000000 : ℝ)^3543
        have hw : |(2715270379/5000000000 : ℝ)|=(2715270379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104369213/200000000 : ℝ)|^4567 ≤ (8648411513253/20000000000000 : ℝ)^3543
        have hw : |(104369213/200000000 : ℝ)|=(104369213/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s4_1 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133758929/250000000 : ℝ)*x 0 + (-971549177/5000000000 : ℝ)*x 1 + (5218460751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133758929/250000000 : ℝ)^4567 ≤ (22327998983229/50000000000000 : ℝ)^3543 := by
    have hnat : (133758929 : ℕ)^4567*50000000000000^3543 ≤ 22327998983229^3543*250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133758929 250000000 22327998983229 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971549177/5000000000 : ℝ)^4567 ≤ (6050971687897/50000000000000 : ℝ)^3543 := by
    have hnat : (971549177 : ℕ)^4567*50000000000000^3543 ≤ 6050971687897^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971549177 5000000000 6050971687897 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218460751/10000000000 : ℝ)^4567 ≤ (1729682345803/4000000000000 : ℝ)^3543 := by
    have hnat : (5218460751 : ℕ)^4567*4000000000000^3543 ≤ 1729682345803^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218460751 10000000000 1729682345803 4000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133758929/250000000 : ℝ), (-971549177/5000000000 : ℝ), (5218460751/10000000000 : ℝ)] ![(22327998983229/50000000000000 : ℝ), (6050971687897/50000000000000 : ℝ), (1729682345803/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133758929/250000000 : ℝ)|^4567 ≤ (22327998983229/50000000000000 : ℝ)^3543
        have hw : |(133758929/250000000 : ℝ)|=(133758929/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971549177/5000000000 : ℝ)|^4567 ≤ (6050971687897/50000000000000 : ℝ)^3543
        have hw : |(-971549177/5000000000 : ℝ)|=(971549177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218460751/10000000000 : ℝ)|^4567 ≤ (1729682345803/4000000000000 : ℝ)^3543
        have hw : |(5218460751/10000000000 : ℝ)|=(5218460751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s4_2 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668794659/1250000000 : ℝ)*x 0 + (2609230317/5000000000 : ℝ)*x 1 + (-1943098359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668794659/1250000000 : ℝ)^4567 ≤ (1395499974107/3125000000000 : ℝ)^3543 := by
    have hnat : (668794659 : ℕ)^4567*3125000000000^3543 ≤ 1395499974107^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668794659 1250000000 1395499974107 3125000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609230317/5000000000 : ℝ)^4567 ≤ (10810514348841/25000000000000 : ℝ)^3543 := by
    have hnat : (2609230317 : ℕ)^4567*25000000000000^3543 ≤ 10810514348841^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609230317 5000000000 10810514348841 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943098359/10000000000 : ℝ)^4567 ≤ (2420388683187/20000000000000 : ℝ)^3543 := by
    have hnat : (1943098359 : ℕ)^4567*20000000000000^3543 ≤ 2420388683187^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943098359 10000000000 2420388683187 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668794659/1250000000 : ℝ), (2609230317/5000000000 : ℝ), (-1943098359/10000000000 : ℝ)] ![(1395499974107/3125000000000 : ℝ), (10810514348841/25000000000000 : ℝ), (2420388683187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668794659/1250000000 : ℝ)|^4567 ≤ (1395499974107/3125000000000 : ℝ)^3543
        have hw : |(668794659/1250000000 : ℝ)|=(668794659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609230317/5000000000 : ℝ)|^4567 ≤ (10810514348841/25000000000000 : ℝ)^3543
        have hw : |(2609230317/5000000000 : ℝ)|=(2609230317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1943098359/10000000000 : ℝ)|^4567 ≤ (2420388683187/20000000000000 : ℝ)^3543
        have hw : |(-1943098359/10000000000 : ℝ)|=(1943098359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s4_3 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259153603/10000000000 : ℝ)*x 0 + (4020635961/10000000000 : ℝ)*x 1 + (4509350081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259153603/10000000000 : ℝ)^4567 ≤ (104001624167/312500000000 : ℝ)^3543 := by
    have hnat : (4259153603 : ℕ)^4567*312500000000^3543 ≤ 104001624167^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259153603 10000000000 104001624167 312500000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4020635961/10000000000 : ℝ)^4567 ≤ (30897816039763/100000000000000 : ℝ)^3543 := by
    have hnat : (4020635961 : ℕ)^4567*100000000000000^3543 ≤ 30897816039763^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020635961 10000000000 30897816039763 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509350081/10000000000 : ℝ)^4567 ≤ (3582166421387/10000000000000 : ℝ)^3543 := by
    have hnat : (4509350081 : ℕ)^4567*10000000000000^3543 ≤ 3582166421387^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509350081 10000000000 3582166421387 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259153603/10000000000 : ℝ), (4020635961/10000000000 : ℝ), (4509350081/10000000000 : ℝ)] ![(104001624167/312500000000 : ℝ), (30897816039763/100000000000000 : ℝ), (3582166421387/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259153603/10000000000 : ℝ)|^4567 ≤ (104001624167/312500000000 : ℝ)^3543
        have hw : |(4259153603/10000000000 : ℝ)|=(4259153603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4020635961/10000000000 : ℝ)|^4567 ≤ (30897816039763/100000000000000 : ℝ)^3543
        have hw : |(4020635961/10000000000 : ℝ)|=(4020635961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509350081/10000000000 : ℝ)|^4567 ≤ (3582166421387/10000000000000 : ℝ)^3543
        have hw : |(4509350081/10000000000 : ℝ)|=(4509350081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s4_4 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-366910467/2000000000 : ℝ)*x 0 + (521956011/1000000000 : ℝ)*x 1 + (1357358291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366910467/2000000000 : ℝ)^4567 ≤ (2247528085707/20000000000000 : ℝ)^3543 := by
    have hnat : (366910467 : ℕ)^4567*20000000000000^3543 ≤ 2247528085707^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366910467 2000000000 2247528085707 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521956011/1000000000 : ℝ)^4567 ≤ (43253801577347/100000000000000 : ℝ)^3543 := by
    have hnat : (521956011 : ℕ)^4567*100000000000000^3543 ≤ 43253801577347^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521956011 1000000000 43253801577347 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357358291/2500000000 : ℝ)^4567 ≤ (45508557970737/100000000000000 : ℝ)^3543 := by
    have hnat : (1357358291 : ℕ)^4567*100000000000000^3543 ≤ 45508557970737^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357358291 2500000000 45508557970737 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366910467/2000000000 : ℝ), (521956011/1000000000 : ℝ), (1357358291/2500000000 : ℝ)] ![(2247528085707/20000000000000 : ℝ), (43253801577347/100000000000000 : ℝ), (45508557970737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366910467/2000000000 : ℝ)|^4567 ≤ (2247528085707/20000000000000 : ℝ)^3543
        have hw : |(-366910467/2000000000 : ℝ)|=(366910467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521956011/1000000000 : ℝ)|^4567 ≤ (43253801577347/100000000000000 : ℝ)^3543
        have hw : |(521956011/1000000000 : ℝ)|=(521956011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357358291/2500000000 : ℝ)|^4567 ≤ (45508557970737/100000000000000 : ℝ)^3543
        have hw : |(1357358291/2500000000 : ℝ)|=(1357358291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s4_5 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132362461/250000000 : ℝ)*x 0 + (-86606289/500000000 : ℝ)*x 1 + (1357358291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132362461/250000000 : ℝ)^4567 ≤ (8811188744361/20000000000000 : ℝ)^3543 := by
    have hnat : (132362461 : ℕ)^4567*20000000000000^3543 ≤ 8811188744361^3543*250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132362461 250000000 8811188744361 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86606289/500000000 : ℝ)^4567 ≤ (1043549828907/10000000000000 : ℝ)^3543 := by
    have hnat : (86606289 : ℕ)^4567*10000000000000^3543 ≤ 1043549828907^3543*500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86606289 500000000 1043549828907 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357358291/2500000000 : ℝ)^4567 ≤ (45508557970737/100000000000000 : ℝ)^3543 := by
    have hnat : (1357358291 : ℕ)^4567*100000000000000^3543 ≤ 45508557970737^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357358291 2500000000 45508557970737 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132362461/250000000 : ℝ), (-86606289/500000000 : ℝ), (1357358291/2500000000 : ℝ)] ![(8811188744361/20000000000000 : ℝ), (1043549828907/10000000000000 : ℝ), (45508557970737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132362461/250000000 : ℝ)|^4567 ≤ (8811188744361/20000000000000 : ℝ)^3543
        have hw : |(132362461/250000000 : ℝ)|=(132362461/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86606289/500000000 : ℝ)|^4567 ≤ (1043549828907/10000000000000 : ℝ)^3543
        have hw : |(-86606289/500000000 : ℝ)|=(86606289/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357358291/2500000000 : ℝ)|^4567 ≤ (45508557970737/100000000000000 : ℝ)^3543
        have hw : |(1357358291/2500000000 : ℝ)|=(1357358291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s4_6 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132362461/250000000 : ℝ)*x 0 + (1357358291/2500000000 : ℝ)*x 1 + (-86606289/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132362461/250000000 : ℝ)^4567 ≤ (8811188744361/20000000000000 : ℝ)^3543 := by
    have hnat : (132362461 : ℕ)^4567*20000000000000^3543 ≤ 8811188744361^3543*250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132362461 250000000 8811188744361 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357358291/2500000000 : ℝ)^4567 ≤ (45508557970737/100000000000000 : ℝ)^3543 := by
    have hnat : (1357358291 : ℕ)^4567*100000000000000^3543 ≤ 45508557970737^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357358291 2500000000 45508557970737 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86606289/500000000 : ℝ)^4567 ≤ (1043549828907/10000000000000 : ℝ)^3543 := by
    have hnat : (86606289 : ℕ)^4567*10000000000000^3543 ≤ 1043549828907^3543*500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86606289 500000000 1043549828907 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132362461/250000000 : ℝ), (1357358291/2500000000 : ℝ), (-86606289/500000000 : ℝ)] ![(8811188744361/20000000000000 : ℝ), (45508557970737/100000000000000 : ℝ), (1043549828907/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132362461/250000000 : ℝ)|^4567 ≤ (8811188744361/20000000000000 : ℝ)^3543
        have hw : |(132362461/250000000 : ℝ)|=(132362461/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357358291/2500000000 : ℝ)|^4567 ≤ (45508557970737/100000000000000 : ℝ)^3543
        have hw : |(1357358291/2500000000 : ℝ)|=(1357358291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86606289/500000000 : ℝ)|^4567 ≤ (1043549828907/10000000000000 : ℝ)^3543
        have hw : |(-86606289/500000000 : ℝ)|=(86606289/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s4_7 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851843709/2000000000 : ℝ)*x 0 + (4506816547/10000000000 : ℝ)*x 1 + (4023188421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851843709/2000000000 : ℝ)^4567 ≤ (33281173847181/100000000000000 : ℝ)^3543 := by
    have hnat : (851843709 : ℕ)^4567*100000000000000^3543 ≤ 33281173847181^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851843709 2000000000 33281173847181 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506816547/10000000000 : ℝ)^4567 ≤ (35795723427649/100000000000000 : ℝ)^3543 := by
    have hnat : (4506816547 : ℕ)^4567*100000000000000^3543 ≤ 35795723427649^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506816547 10000000000 35795723427649 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023188421/10000000000 : ℝ)^4567 ≤ (1546155135571/5000000000000 : ℝ)^3543 := by
    have hnat : (4023188421 : ℕ)^4567*5000000000000^3543 ≤ 1546155135571^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023188421 10000000000 1546155135571 5000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851843709/2000000000 : ℝ), (4506816547/10000000000 : ℝ), (4023188421/10000000000 : ℝ)] ![(33281173847181/100000000000000 : ℝ), (35795723427649/100000000000000 : ℝ), (1546155135571/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851843709/2000000000 : ℝ)|^4567 ≤ (33281173847181/100000000000000 : ℝ)^3543
        have hw : |(851843709/2000000000 : ℝ)|=(851843709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506816547/10000000000 : ℝ)|^4567 ≤ (35795723427649/100000000000000 : ℝ)^3543
        have hw : |(4506816547/10000000000 : ℝ)|=(4506816547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023188421/10000000000 : ℝ)|^4567 ≤ (1546155135571/5000000000000 : ℝ)^3543
        have hw : |(4023188421/10000000000 : ℝ)|=(4023188421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1535_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15537/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10953/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2749/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15537/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10953/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15537/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10953/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15537/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10953/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15537/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10953/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15537/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10953/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15537/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10953/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10953/100000 : ℝ) ^ (4565/1024 : ℝ) ≤ (2613370626897323/50000000000000000000 : ℝ) := by
    have hpowers : (10953/100000 : ℝ)^4565 ≤ (2613370626897323/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10953 : ℕ)^4565*50000000000000000000^1024 ≤ 2613370626897323^1024*100000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10953 100000 2613370626897323 50000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10953/100000 : ℝ)) (X := (2613370626897323/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15537/100000 : ℝ) ^ (4565/1024 : ℝ) ≤ (24837535875378843/100000000000000000000 : ℝ) := by
    have hpowers : (15537/100000 : ℝ)^4565 ≤ (24837535875378843/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15537 : ℕ)^4565*100000000000000000000^1024 ≤ 24837535875378843^1024*100000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15537 100000 24837535875378843 100000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15537/100000 : ℝ)) (X := (24837535875378843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002613370626897323/25000000000000000000 : ℝ) ≤ (10000234478250323/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (25002613370626897323/25000000000000000000 : ℝ)^1024 ≤ (10000234478250323/10000000000000000 : ℝ)^4565 := by
      have hnat : (25002613370626897323 : ℕ)^1024*10000000000000000^4565 ≤ 10000234478250323^4565*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002613370626897323 25000000000000000000 10000234478250323 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000234478250323/10000000000000000 : ℝ)) (X := (25002613370626897323/25000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030064277129173489/100000000000000000000 : ℝ) ≤ (10000674309545049/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (100030064277129173489/100000000000000000000 : ℝ)^1024 ≤ (10000674309545049/10000000000000000 : ℝ)^4565 := by
      have hnat : (100030064277129173489 : ℕ)^1024*10000000000000000^4565 ≤ 10000674309545049^4565*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030064277129173489 100000000000000000000 10000674309545049 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674309545049/10000000000000000 : ℝ)) (X := (100030064277129173489/100000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024837535875378843/50000000000000000000 : ℝ) ≤ (400044565633591/400000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50024837535875378843/50000000000000000000 : ℝ)^1024 ≤ (400044565633591/400000000000000 : ℝ)^4565 := by
      have hnat : (50024837535875378843 : ℕ)^1024*400000000000000^4565 ≤ 400044565633591^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024837535875378843 50000000000000000000 400044565633591 400000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400044565633591/400000000000000 : ℝ)) (X := (50024837535875378843/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2613370626897323/50000000000000000000 : ℝ) ≤ ((3819286658663101073/3820000000000000000 : ℝ)+2*(219915647363/229200000000000 : ℝ)*(10953/100000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (3819286658663101073/3820000000000000000 : ℝ)+2*(219915647363/229200000000000 : ℝ)*(10953/100000 : ℝ)=(10000234478250323/10000000000000000 : ℝ) by norm_num, show 1+2*(2613370626897323/50000000000000000000 : ℝ)=(25002613370626897323/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24837535875378843/100000000000000000000 : ℝ)+(2613370626897323/50000000000000000000 : ℝ) ≤ ((3819286658663101073/3820000000000000000 : ℝ)+(219915647363/229200000000000 : ℝ)*((15537/100000 : ℝ)+(10953/100000 : ℝ)))^(4565/1024 : ℝ) := by
    rw [show (3819286658663101073/3820000000000000000 : ℝ)+(219915647363/229200000000000 : ℝ)*((15537/100000 : ℝ)+(10953/100000 : ℝ))=(10000674309545049/10000000000000000 : ℝ) by norm_num, show 1+(24837535875378843/100000000000000000000 : ℝ)+(2613370626897323/50000000000000000000 : ℝ)=(100030064277129173489/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24837535875378843/100000000000000000000 : ℝ) ≤ ((3819286658663101073/3820000000000000000 : ℝ)+2*(219915647363/229200000000000 : ℝ)*(15537/100000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (3819286658663101073/3820000000000000000 : ℝ)+2*(219915647363/229200000000000 : ℝ)*(15537/100000 : ℝ)=(400044565633591/400000000000000 : ℝ) by norm_num, show 1+2*(24837535875378843/100000000000000000000 : ℝ)=(50024837535875378843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3819286658663101073/3820000000000000000 : ℝ)*(X 1 0+X 2 0)+(219915647363/229200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (10953/100000 : ℝ)) (hi := (15537/100000 : ℝ)) (c := (3819286658663101073/3820000000000000000 : ℝ)) (alpha := (219915647363/229200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3819286658663101073/3820000000000000000 : ℝ)*(X 0 1+X 2 1)+(219915647363/229200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (10953/100000 : ℝ)) (hi := (15537/100000 : ℝ)) (c := (3819286658663101073/3820000000000000000 : ℝ)) (alpha := (219915647363/229200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3819286658663101073/3820000000000000000 : ℝ)*(X 0 2+X 1 2)+(219915647363/229200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (10953/100000 : ℝ)) (hi := (15537/100000 : ℝ)) (c := (3819286658663101073/3820000000000000000 : ℝ)) (alpha := (219915647363/229200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-229315509/1250000000 : ℝ)*X 0 0+(2715270379/5000000000 : ℝ)*X 0 1+(104369213/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133758929/250000000 : ℝ)*X 1 0+(-971549177/5000000000 : ℝ)*X 1 1+(5218460751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668794659/1250000000 : ℝ)*X 2 0+(2609230317/5000000000 : ℝ)*X 2 1+(-1943098359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4259153603/10000000000 : ℝ)*X 0 0+(4020635961/10000000000 : ℝ)*X 0 1+(4509350081/10000000000 : ℝ)*X 0 2+(4259153603/10000000000 : ℝ)*X 1 0+(4020635961/10000000000 : ℝ)*X 1 1+(4509350081/10000000000 : ℝ)*X 1 2+(4259153603/10000000000 : ℝ)*X 2 0+(4020635961/10000000000 : ℝ)*X 2 1+(4509350081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-366910467/2000000000 : ℝ)*X 0 0+(521956011/1000000000 : ℝ)*X 0 1+(1357358291/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132362461/250000000 : ℝ)*X 1 0+(-86606289/500000000 : ℝ)*X 1 1+(1357358291/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132362461/250000000 : ℝ)*X 2 0+(1357358291/2500000000 : ℝ)*X 2 1+(-86606289/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((851843709/2000000000 : ℝ)*X 0 0+(4506816547/10000000000 : ℝ)*X 0 1+(4023188421/10000000000 : ℝ)*X 0 2+(851843709/2000000000 : ℝ)*X 1 0+(4506816547/10000000000 : ℝ)*X 1 1+(4023188421/10000000000 : ℝ)*X 1 2+(851843709/2000000000 : ℝ)*X 2 0+(4506816547/10000000000 : ℝ)*X 2 1+(4023188421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9953251392684854460391/955000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67440059/4000000000000 : ℝ)*(base19) + (199225051/12500000000000 : ℝ)*(base23) + (102141681/100000000000000 : ℝ)*(lower2) + (299005559/100000000000000 : ℝ)*(upper3) + (170735943/100000000000000 : ℝ)*(upper5) + (422591455938391/12500000000000 : ℝ)*(major0) + (422591455938391/12500000000000 : ℝ)*(major1) + (422591455938391/12500000000000 : ℝ)*(major2) + (4715226800543823/100000000000000 : ℝ)*(sp0) + (147351606599293/3125000000000 : ℝ)*(sp1) + (4715251503378443/100000000000000 : ℝ)*(sp2) + (1023098381040919/50000000000000 : ℝ)*(sp3) + (26296635029/100000000000000 : ℝ)*(sp4) + (13088345131/100000000000000 : ℝ)*(sp7) + (2046209850426969/100000000000000 : ℝ)*(f.failure) + (1178813274294713/25000000000000 : ℝ)*(f.sum) + (560643372313/358125000000000000000000000 : ℝ)*base66 + (114502264828119371/143250000000000000000000000000000 : ℝ)*base68 + (240323572510119371/143250000000000000000000000000000 : ℝ)*base70 + (208422532955619371/143250000000000000000000000000000 : ℝ)*base72 + (14186765295451/2865000000000000000000000000 : ℝ)*base73 + (852329745012380629/143250000000000000000000000000000 : ℝ)*base75 + (169546125162380629/143250000000000000000000000000000 : ℝ)*base77 + (2630743336878380629/143250000000000000000000000000000 : ℝ)*base79 + (3847711590607/1432500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14252071/2000000000000000000000 : ℝ)*base90 + (14252071/2000000000000000000000 : ℝ)*base92 + (14252071/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22439837927083157767953/3820000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29481551/3125000000000 : ℝ)*(base19) + (255771231/25000000000000 : ℝ)*(base23) + (24271943/20000000000000 : ℝ)*(upper3) + (18048751/50000000000000 : ℝ)*(lower4) + (15212529/12500000000000 : ℝ)*(upper5) + (3416244431963589/100000000000000 : ℝ)*(major0) + (3416244431963589/100000000000000 : ℝ)*(major1) + (3416244431963589/100000000000000 : ℝ)*(major2) + (917868707/6250000000000 : ℝ)*(sp1) + (7887752049/50000000000000 : ℝ)*(sp2) + (4764784473581333/100000000000000 : ℝ)*(sp4) + (4764768844272389/100000000000000 : ℝ)*(sp5) + (4764767674992311/100000000000000 : ℝ)*(sp6) + (2067704194535731/100000000000000 : ℝ)*(sp7) + (2067704194535731/100000000000000 : ℝ)*(f.failure) + (4764784473581333/100000000000000 : ℝ)*(f.sum) + (745917013531/3820000000000000000000000000 : ℝ)*base66 + (3516035311092280997/382000000000000000000000000000000 : ℝ)*base67 + (1862651116460280997/382000000000000000000000000000000 : ℝ)*base69 + (230892286323719003/382000000000000000000000000000000 : ℝ)*base72 + (14172133597289/3820000000000000000000000000 : ℝ)*base73 + (2665761961011719003/382000000000000000000000000000000 : ℝ)*base76 + (2640452181235719003/382000000000000000000000000000000 : ℝ)*base78 + (7664687671800280997/382000000000000000000000000000000 : ℝ)*base79 + (25418221237289/3820000000000000000000000000 : ℝ)*base81 + (16017229/2000000000000000000000 : ℝ)*base90 + (16017229/2000000000000000000000 : ℝ)*base92 + (16017229/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1535_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15537/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10953/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1535_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1535_s5_0 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1834563157/10000000000 : ℝ)*x 0 + (1357571343/2500000000 : ℝ)*x 1 + (2609345049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1834563157/10000000000 : ℝ)^4567 ≤ (2809431469669/25000000000000 : ℝ)^3543 := by
    have hnat : (1834563157 : ℕ)^4567*25000000000000^3543 ≤ 2809431469669^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834563157 10000000000 2809431469669 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357571343/2500000000 : ℝ)^4567 ≤ (9103553145759/20000000000000 : ℝ)^3543 := by
    have hnat : (1357571343 : ℕ)^4567*20000000000000^3543 ≤ 9103553145759^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357571343 2500000000 9103553145759 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609345049/5000000000 : ℝ)^4567 ≤ (1729780335319/4000000000000 : ℝ)^3543 := by
    have hnat : (2609345049 : ℕ)^4567*4000000000000^3543 ≤ 1729780335319^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609345049 5000000000 1729780335319 4000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1834563157/10000000000 : ℝ), (1357571343/2500000000 : ℝ), (2609345049/5000000000 : ℝ)] ![(2809431469669/25000000000000 : ℝ), (9103553145759/20000000000000 : ℝ), (1729780335319/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1834563157/10000000000 : ℝ)|^4567 ≤ (2809431469669/25000000000000 : ℝ)^3543
        have hw : |(-1834563157/10000000000 : ℝ)|=(1834563157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357571343/2500000000 : ℝ)|^4567 ≤ (9103553145759/20000000000000 : ℝ)^3543
        have hw : |(1357571343/2500000000 : ℝ)|=(1357571343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609345049/5000000000 : ℝ)|^4567 ≤ (1729780335319/4000000000000 : ℝ)^3543
        have hw : |(2609345049/5000000000 : ℝ)|=(2609345049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s5_1 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334393119/625000000 : ℝ)*x 0 + (-1942884023/10000000000 : ℝ)*x 1 + (326168099/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334393119/625000000 : ℝ)^4567 ≤ (22327637192749/50000000000000 : ℝ)^3543 := by
    have hnat : (334393119 : ℕ)^4567*50000000000000^3543 ≤ 22327637192749^3543*625000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334393119 625000000 22327637192749 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942884023/10000000000 : ℝ)^4567 ≤ (1210022270313/10000000000000 : ℝ)^3543 := by
    have hnat : (1942884023 : ℕ)^4567*10000000000000^3543 ≤ 1210022270313^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942884023 10000000000 1210022270313 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326168099/625000000 : ℝ)^4567 ≤ (43244502892721/100000000000000 : ℝ)^3543 := by
    have hnat : (326168099 : ℕ)^4567*100000000000000^3543 ≤ 43244502892721^3543*625000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326168099 625000000 43244502892721 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334393119/625000000 : ℝ), (-1942884023/10000000000 : ℝ), (326168099/625000000 : ℝ)] ![(22327637192749/50000000000000 : ℝ), (1210022270313/10000000000000 : ℝ), (43244502892721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334393119/625000000 : ℝ)|^4567 ≤ (22327637192749/50000000000000 : ℝ)^3543
        have hw : |(334393119/625000000 : ℝ)|=(334393119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942884023/10000000000 : ℝ)|^4567 ≤ (1210022270313/10000000000000 : ℝ)^3543
        have hw : |(-1942884023/10000000000 : ℝ)|=(1942884023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326168099/625000000 : ℝ)|^4567 ≤ (43244502892721/100000000000000 : ℝ)^3543
        have hw : |(326168099/625000000 : ℝ)|=(326168099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s5_2 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675144441/5000000000 : ℝ)*x 0 + (5218692173/10000000000 : ℝ)*x 1 + (-485720487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675144441/5000000000 : ℝ)^4567 ≤ (44655263390221/100000000000000 : ℝ)^3543 := by
    have hnat : (2675144441 : ℕ)^4567*100000000000000^3543 ≤ 44655263390221^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675144441 5000000000 44655263390221 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218692173/10000000000 : ℝ)^4567 ≤ (43244530546939/100000000000000 : ℝ)^3543 := by
    have hnat : (5218692173 : ℕ)^4567*100000000000000^3543 ≤ 43244530546939^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218692173 10000000000 43244530546939 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485720487/2500000000 : ℝ)^4567 ≤ (12100206045071/100000000000000 : ℝ)^3543 := by
    have hnat : (485720487 : ℕ)^4567*100000000000000^3543 ≤ 12100206045071^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485720487 2500000000 12100206045071 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675144441/5000000000 : ℝ), (5218692173/10000000000 : ℝ), (-485720487/2500000000 : ℝ)] ![(44655263390221/100000000000000 : ℝ), (43244530546939/100000000000000 : ℝ), (12100206045071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675144441/5000000000 : ℝ)|^4567 ≤ (44655263390221/100000000000000 : ℝ)^3543
        have hw : |(2675144441/5000000000 : ℝ)|=(2675144441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218692173/10000000000 : ℝ)|^4567 ≤ (43244530546939/100000000000000 : ℝ)^3543
        have hw : |(5218692173/10000000000 : ℝ)|=(5218692173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485720487/2500000000 : ℝ)|^4567 ≤ (12100206045071/100000000000000 : ℝ)^3543
        have hw : |(-485720487/2500000000 : ℝ)|=(485720487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s5_3 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259178571/10000000000 : ℝ)*x 0 + (804238309/2000000000 : ℝ)*x 1 + (901757607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259178571/10000000000 : ℝ)^4567 ≤ (8320192804421/25000000000000 : ℝ)^3543 := by
    have hnat : (4259178571 : ℕ)^4567*25000000000000^3543 ≤ 8320192804421^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259178571 10000000000 8320192804421 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804238309/2000000000 : ℝ)^4567 ≤ (15451659847951/50000000000000 : ℝ)^3543 := by
    have hnat : (804238309 : ℕ)^4567*50000000000000^3543 ≤ 15451659847951^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804238309 2000000000 15451659847951 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901757607/2000000000 : ℝ)^4567 ≤ (4476988634547/12500000000000 : ℝ)^3543 := by
    have hnat : (901757607 : ℕ)^4567*12500000000000^3543 ≤ 4476988634547^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901757607 2000000000 4476988634547 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259178571/10000000000 : ℝ), (804238309/2000000000 : ℝ), (901757607/2000000000 : ℝ)] ![(8320192804421/25000000000000 : ℝ), (15451659847951/50000000000000 : ℝ), (4476988634547/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259178571/10000000000 : ℝ)|^4567 ≤ (8320192804421/25000000000000 : ℝ)^3543
        have hw : |(4259178571/10000000000 : ℝ)|=(4259178571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804238309/2000000000 : ℝ)|^4567 ≤ (15451659847951/50000000000000 : ℝ)^3543
        have hw : |(804238309/2000000000 : ℝ)|=(804238309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901757607/2000000000 : ℝ)|^4567 ≤ (4476988634547/12500000000000 : ℝ)^3543
        have hw : |(901757607/2000000000 : ℝ)|=(901757607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s5_4 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-917295679/5000000000 : ℝ)*x 0 + (5219784809/10000000000 : ℝ)*x 1 + (542918249/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (917295679/5000000000 : ℝ)^4567 ≤ (11237948553491/100000000000000 : ℝ)^3543 := by
    have hnat : (917295679 : ℕ)^4567*100000000000000^3543 ≤ 11237948553491^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917295679 5000000000 11237948553491 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219784809/10000000000 : ℝ)^4567 ≤ (43256201814097/100000000000000 : ℝ)^3543 := by
    have hnat : (5219784809 : ℕ)^4567*100000000000000^3543 ≤ 43256201814097^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219784809 10000000000 43256201814097 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542918249/1000000000 : ℝ)^4567 ≤ (45505849620437/100000000000000 : ℝ)^3543 := by
    have hnat : (542918249 : ℕ)^4567*100000000000000^3543 ≤ 45505849620437^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542918249 1000000000 45505849620437 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-917295679/5000000000 : ℝ), (5219784809/10000000000 : ℝ), (542918249/1000000000 : ℝ)] ![(11237948553491/100000000000000 : ℝ), (43256201814097/100000000000000 : ℝ), (45505849620437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-917295679/5000000000 : ℝ)|^4567 ≤ (11237948553491/100000000000000 : ℝ)^3543
        have hw : |(-917295679/5000000000 : ℝ)|=(917295679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219784809/10000000000 : ℝ)|^4567 ≤ (43256201814097/100000000000000 : ℝ)^3543
        have hw : |(5219784809/10000000000 : ℝ)|=(5219784809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542918249/1000000000 : ℝ)|^4567 ≤ (45505849620437/100000000000000 : ℝ)^3543
        have hw : |(542918249/1000000000 : ℝ)|=(542918249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s5_5 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294558849/10000000000 : ℝ)*x 0 + (-173239107/1000000000 : ℝ)*x 1 + (2714591251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294558849/10000000000 : ℝ)^4567 ≤ (2202829583621/5000000000000 : ℝ)^3543 := by
    have hnat : (5294558849 : ℕ)^4567*5000000000000^3543 ≤ 2202829583621^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294558849 10000000000 2202829583621 5000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173239107/1000000000 : ℝ)^4567 ≤ (2609389639741/25000000000000 : ℝ)^3543 := by
    have hnat : (173239107 : ℕ)^4567*25000000000000^3543 ≤ 2609389639741^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173239107 1000000000 2609389639741 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714591251/5000000000 : ℝ)^4567 ≤ (5688231218761/12500000000000 : ℝ)^3543 := by
    have hnat : (2714591251 : ℕ)^4567*12500000000000^3543 ≤ 5688231218761^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714591251 5000000000 5688231218761 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294558849/10000000000 : ℝ), (-173239107/1000000000 : ℝ), (2714591251/5000000000 : ℝ)] ![(2202829583621/5000000000000 : ℝ), (2609389639741/25000000000000 : ℝ), (5688231218761/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294558849/10000000000 : ℝ)|^4567 ≤ (2202829583621/5000000000000 : ℝ)^3543
        have hw : |(5294558849/10000000000 : ℝ)|=(5294558849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-173239107/1000000000 : ℝ)|^4567 ≤ (2609389639741/25000000000000 : ℝ)^3543
        have hw : |(-173239107/1000000000 : ℝ)|=(173239107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714591251/5000000000 : ℝ)|^4567 ≤ (5688231218761/12500000000000 : ℝ)^3543
        have hw : |(2714591251/5000000000 : ℝ)|=(2714591251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s5_6 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647279427/5000000000 : ℝ)*x 0 + (2714591249/5000000000 : ℝ)*x 1 + (-1732391069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647279427/5000000000 : ℝ)^4567 ≤ (881131834521/2000000000000 : ℝ)^3543 := by
    have hnat : (2647279427 : ℕ)^4567*2000000000000^3543 ≤ 881131834521^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647279427 5000000000 881131834521 2000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714591249/5000000000 : ℝ)^4567 ≤ (45505849706871/100000000000000 : ℝ)^3543 := by
    have hnat : (2714591249 : ℕ)^4567*100000000000000^3543 ≤ 45505849706871^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714591249 5000000000 45505849706871 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732391069/10000000000 : ℝ)^4567 ≤ (5218779275599/50000000000000 : ℝ)^3543 := by
    have hnat : (1732391069 : ℕ)^4567*50000000000000^3543 ≤ 5218779275599^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732391069 10000000000 5218779275599 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647279427/5000000000 : ℝ), (2714591249/5000000000 : ℝ), (-1732391069/10000000000 : ℝ)] ![(881131834521/2000000000000 : ℝ), (45505849706871/100000000000000 : ℝ), (5218779275599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647279427/5000000000 : ℝ)|^4567 ≤ (881131834521/2000000000000 : ℝ)^3543
        have hw : |(2647279427/5000000000 : ℝ)|=(2647279427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714591249/5000000000 : ℝ)|^4567 ≤ (45505849706871/100000000000000 : ℝ)^3543
        have hw : |(2714591249/5000000000 : ℝ)|=(2714591249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1732391069/10000000000 : ℝ)|^4567 ≤ (5218779275599/50000000000000 : ℝ)^3543
        have hw : |(-1732391069/10000000000 : ℝ)|=(1732391069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s5_7 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532405257/1250000000 : ℝ)*x 0 + (4506266063/10000000000 : ℝ)*x 1 + (2011866671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532405257/1250000000 : ℝ)^4567 ≤ (33281410657171/100000000000000 : ℝ)^3543 := by
    have hnat : (532405257 : ℕ)^4567*100000000000000^3543 ≤ 33281410657171^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532405257 1250000000 33281410657171 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506266063/10000000000 : ℝ)^4567 ≤ (35790087594107/100000000000000 : ℝ)^3543 := by
    have hnat : (4506266063 : ℕ)^4567*100000000000000^3543 ≤ 35790087594107^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506266063 10000000000 35790087594107 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011866671/5000000000 : ℝ)^4567 ≤ (15464250863587/50000000000000 : ℝ)^3543 := by
    have hnat : (2011866671 : ℕ)^4567*50000000000000^3543 ≤ 15464250863587^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011866671 5000000000 15464250863587 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532405257/1250000000 : ℝ), (4506266063/10000000000 : ℝ), (2011866671/5000000000 : ℝ)] ![(33281410657171/100000000000000 : ℝ), (35790087594107/100000000000000 : ℝ), (15464250863587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532405257/1250000000 : ℝ)|^4567 ≤ (33281410657171/100000000000000 : ℝ)^3543
        have hw : |(532405257/1250000000 : ℝ)|=(532405257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506266063/10000000000 : ℝ)|^4567 ≤ (35790087594107/100000000000000 : ℝ)^3543
        have hw : |(4506266063/10000000000 : ℝ)|=(4506266063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2011866671/5000000000 : ℝ)|^4567 ≤ (15464250863587/50000000000000 : ℝ)^3543
        have hw : |(2011866671/5000000000 : ℝ)|=(2011866671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1535_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11001/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2749/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2749/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2749/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2749/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2749/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2749/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2749/25000 : ℝ) ^ (4565/1024 : ℝ) ≤ (5194179867239/97656250000000000 : ℝ) := by
    have hpowers : (2749/25000 : ℝ)^4565 ≤ (5194179867239/97656250000000000 : ℝ)^1024 := by
      have hnat : (2749 : ℕ)^4565*97656250000000000^1024 ≤ 5194179867239^1024*25000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2749 25000 5194179867239 97656250000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2749/25000 : ℝ)) (X := (5194179867239/97656250000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4565/1024 : ℝ) ≤ (24504333394551821/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4565 ≤ (24504333394551821/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4565*100000000000000000000^1024 ≤ 24504333394551821^1024*10000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 24504333394551821 100000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (24504333394551821/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (48833319179867239/48828125000000000 : ℝ) ≤ (312507456554839/312500000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (48833319179867239/48828125000000000 : ℝ)^1024 ≤ (312507456554839/312500000000000 : ℝ)^4565 := by
      have hnat : (48833319179867239 : ℕ)^1024*312500000000000^4565 ≤ 312507456554839^4565*48828125000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48833319179867239 48828125000000000 312507456554839 312500000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312507456554839/312500000000000 : ℝ)) (X := (48833319179867239/48828125000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029823173578604557/100000000000000000000 : ℝ) ≤ (10000668902475911/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (100029823173578604557/100000000000000000000 : ℝ)^1024 ≤ (10000668902475911/10000000000000000 : ℝ)^4565 := by
      have hnat : (100029823173578604557 : ℕ)^1024*10000000000000000^4565 ≤ 10000668902475911^4565*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029823173578604557 100000000000000000000 10000668902475911 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668902475911/10000000000000000 : ℝ)) (X := (100029823173578604557/100000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024504333394551821/50000000000000000000 : ℝ) ≤ (5000549597598487/5000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50024504333394551821/50000000000000000000 : ℝ)^1024 ≤ (5000549597598487/5000000000000000 : ℝ)^4565 := by
      have hnat : (50024504333394551821 : ℕ)^1024*5000000000000000^4565 ≤ 5000549597598487^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024504333394551821 50000000000000000000 5000549597598487 5000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000549597598487/5000000000000000 : ℝ)) (X := (50024504333394551821/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5194179867239/97656250000000000 : ℝ) ≤ ((1872150388113194559/1872500000000000000 : ℝ)+2*(143430907021/149800000000000 : ℝ)*(2749/25000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (1872150388113194559/1872500000000000000 : ℝ)+2*(143430907021/149800000000000 : ℝ)*(2749/25000 : ℝ)=(312507456554839/312500000000000 : ℝ) by norm_num, show 1+2*(5194179867239/97656250000000000 : ℝ)=(48833319179867239/48828125000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24504333394551821/100000000000000000000 : ℝ)+(5194179867239/97656250000000000 : ℝ) ≤ ((1872150388113194559/1872500000000000000 : ℝ)+(143430907021/149800000000000 : ℝ)*((1549/10000 : ℝ)+(2749/25000 : ℝ)))^(4565/1024 : ℝ) := by
    rw [show (1872150388113194559/1872500000000000000 : ℝ)+(143430907021/149800000000000 : ℝ)*((1549/10000 : ℝ)+(2749/25000 : ℝ))=(10000668902475911/10000000000000000 : ℝ) by norm_num, show 1+(24504333394551821/100000000000000000000 : ℝ)+(5194179867239/97656250000000000 : ℝ)=(100029823173578604557/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24504333394551821/100000000000000000000 : ℝ) ≤ ((1872150388113194559/1872500000000000000 : ℝ)+2*(143430907021/149800000000000 : ℝ)*(1549/10000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (1872150388113194559/1872500000000000000 : ℝ)+2*(143430907021/149800000000000 : ℝ)*(1549/10000 : ℝ)=(5000549597598487/5000000000000000 : ℝ) by norm_num, show 1+2*(24504333394551821/100000000000000000000 : ℝ)=(50024504333394551821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1872150388113194559/1872500000000000000 : ℝ)*(X 1 0+X 2 0)+(143430907021/149800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1872150388113194559/1872500000000000000 : ℝ)) (alpha := (143430907021/149800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1872150388113194559/1872500000000000000 : ℝ)*(X 0 1+X 2 1)+(143430907021/149800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1872150388113194559/1872500000000000000 : ℝ)) (alpha := (143430907021/149800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1872150388113194559/1872500000000000000 : ℝ)*(X 0 2+X 1 2)+(143430907021/149800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1872150388113194559/1872500000000000000 : ℝ)) (alpha := (143430907021/149800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1834563157/10000000000 : ℝ)*X 0 0+(1357571343/2500000000 : ℝ)*X 0 1+(2609345049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334393119/625000000 : ℝ)*X 1 0+(-1942884023/10000000000 : ℝ)*X 1 1+(326168099/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675144441/5000000000 : ℝ)*X 2 0+(5218692173/10000000000 : ℝ)*X 2 1+(-485720487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4259178571/10000000000 : ℝ)*X 0 0+(804238309/2000000000 : ℝ)*X 0 1+(901757607/2000000000 : ℝ)*X 0 2+(4259178571/10000000000 : ℝ)*X 1 0+(804238309/2000000000 : ℝ)*X 1 1+(901757607/2000000000 : ℝ)*X 1 2+(4259178571/10000000000 : ℝ)*X 2 0+(804238309/2000000000 : ℝ)*X 2 1+(901757607/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-917295679/5000000000 : ℝ)*X 0 0+(5219784809/10000000000 : ℝ)*X 0 1+(542918249/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294558849/10000000000 : ℝ)*X 1 0+(-173239107/1000000000 : ℝ)*X 1 1+(2714591251/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647279427/5000000000 : ℝ)*X 2 0+(2714591249/5000000000 : ℝ)*X 2 1+(-1732391069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((532405257/1250000000 : ℝ)*X 0 0+(4506266063/10000000000 : ℝ)*X 0 1+(2011866671/5000000000 : ℝ)*X 0 2+(532405257/1250000000 : ℝ)*X 1 0+(4506266063/10000000000 : ℝ)*X 1 1+(2011866671/5000000000 : ℝ)*X 1 2+(532405257/1250000000 : ℝ)*X 2 0+(4506266063/10000000000 : ℝ)*X 2 1+(2011866671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (221316422573067127006539141/23406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2129950783/100000000000000 : ℝ)*(base19) + (747128713/100000000000000 : ℝ)*(base23) + (364539469/100000000000000 : ℝ)*(lower2) + (592797007/100000000000000 : ℝ)*(upper5) + (847126178241433/25000000000000 : ℝ)*(major0) + (847126178241433/25000000000000 : ℝ)*(major1) + (847126178241433/25000000000000 : ℝ)*(major2) + (189041535860339/4000000000000 : ℝ)*(sp0) + (4726073107573013/100000000000000 : ℝ)*(sp1) + (73845215854607/1562500000000 : ℝ)*(sp2) + (512724550216959/25000000000000 : ℝ)*(sp3) + (11233063017/20000000000000 : ℝ)*(sp4) + (4831074941/25000000000000 : ℝ)*(sp5) + (16348058683/100000000000000 : ℝ)*(sp7) + (51272863723163/2500000000000 : ℝ)*(f.failure) + (118152364045589/2500000000000 : ℝ)*(f.sum) + (24876600223931/3745000000000000000000000000 : ℝ)*base65 + (65557369711642779/6687500000000000000000000000000 : ℝ)*base68 + (55384344256892779/6687500000000000000000000000000 : ℝ)*base70 + (22624046229232221/6687500000000000000000000000000 : ℝ)*base71 + (3243729513509/936250000000000000000000000 : ℝ)*base73 + (41559769528107221/6687500000000000000000000000000 : ℝ)*base75 + (43351535498017779/6687500000000000000000000000000 : ℝ)*base78 + (29397744497455279/6687500000000000000000000000000 : ℝ)*base80 + (5561506201099/936250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (189083/50000000000000000000 : ℝ)*base89 + (189083/50000000000000000000 : ℝ)*base91 + (189083/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (221821671774192155024919051/23406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151576201/10000000000000 : ℝ)*(base19) + (1648001921/100000000000000 : ℝ)*(base23) + (499297609/100000000000000 : ℝ)*(lower1) + (99630119/50000000000000 : ℝ)*(upper3) + (11377351/20000000000000 : ℝ)*(lower4) + (6024661/3125000000000 : ℝ)*(upper5) + (1711991282456237/50000000000000 : ℝ)*(major0) + (1711991282456237/50000000000000 : ℝ)*(major1) + (1711991282456237/50000000000000 : ℝ)*(major2) + (1927267657/100000000000000 : ℝ)*(sp2) + (2387788532008889/50000000000000 : ℝ)*(sp4) + (596946943531971/12500000000000 : ℝ)*(sp5) + (23877867443741/500000000000 : ℝ)*(sp6) + (1036193874953119/50000000000000 : ℝ)*(sp7) + (1036193874953119/50000000000000 : ℝ)*(f.failure) + (2387788532008889/50000000000000 : ℝ)*(f.sum) + (1971558938997/3745000000000000000000000000 : ℝ)*base65 + (489116759211889569/13375000000000000000000000000000 : ℝ)*base67 + (24322679644389569/13375000000000000000000000000000 : ℝ)*base69 + (1537680633818389569/13375000000000000000000000000000 : ℝ)*base71 + (14892275041353/3745000000000000000000000000 : ℝ)*base74 + (387054494417889569/13375000000000000000000000000000 : ℝ)*base75 + (21739522793360431/13375000000000000000000000000000 : ℝ)*base78 + (6003495347764569/13375000000000000000000000000000 : ℝ)*base79 + (9734648031223/3745000000000000000000000000 : ℝ)*base82 + (6690079/1000000000000000000000 : ℝ)*base89 + (6690079/1000000000000000000000 : ℝ)*base91 + (6690079/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1535_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1535_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1535_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3183/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1535_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1535_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1535_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3183/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1535_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
